{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
--{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Schedule.Uniform
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Schedule.Uniform (
  -- Exports the instance IsSchedule UniformScheduleFun

  compileKernel', CompiledKernel(..), rnfSArg, rnfSArgs
) where

import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Operation.Substitution   (strengthenArrayInstr)
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Schedule.Uniform.LiveVars
import Data.Array.Accelerate.Trafo.Schedule.Uniform.Simplify
import Data.Array.Accelerate.Trafo.Schedule.Uniform.Substitution
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.AST.IdxSet           as IdxSet
import qualified Data.Array.Accelerate.AST.Operation    as C
import qualified Data.Array.Accelerate.AST.Partitioned  as C
import Data.Kind
import Data.Maybe
import Data.String
import Formatting
import Data.List
    ( isSubsequenceOf, groupBy, nubBy, sort, group )
import Prelude hiding (id, (.), read)
import Control.Category
import Control.DeepSeq
import qualified Data.Array.Accelerate.AST.Environment as Env
import Control.Concurrent
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Accelerate.Pretty.Operation
import Data.Functor.Identity

import Debug.Trace
import Data.Array.Accelerate.Pretty
import qualified Data.Array.Accelerate.Pretty.Print as Pr
import Data.Array.Accelerate.Pretty.Schedule.Uniform
import Data.Array.Accelerate.AST.Exp

instance IsSchedule UniformScheduleFun where
  type ScheduleInput  UniformScheduleFun a = Input a
  type ScheduleOutput UniformScheduleFun a = Output a

  -- convertScheduleFun afun
  --   | (partial, _) <- partialScheduleFun afun
  --   = traceShow afun $ stronglyLiveVariablesFun $ simplifyFun emptySimplifyEnv $ simplifyFun emptySimplifyEnv
  --   $ stronglyLiveVariablesFun $ simplifyFun emptySimplifyEnv
  --   $ fromPartialFun PEnd (ReusedVars IdxSet.empty) partial

  --convertScheduleFun = convertScheduleFun'

  -- convertScheduleFun afun = stronglyLiveVariablesFun $ simplifyFun emptySimplifyEnv $ simplifyFun emptySimplifyEnv
  --   $ stronglyLiveVariablesFun $ simplifyFun emptySimplifyEnv $ fromUsageFun PEnd (usageAnalysisOpenAFun afun)

  convertScheduleFun afun = traceShow afun $ fromUsageFun PEnd (usageAnalysisOpenAFun afun)


  rnfSchedule (Slam lhs s) = rnfLeftHandSide rnfBaseR lhs `seq` rnfSchedule s
  rnfSchedule (Sbody s) = rnfSchedule' s

  callScheduledFun (GFunctionRbody repr) f
    | Refl <- reprIsBody @UniformScheduleFun repr = do
      (output, result) <- bindOutput repr
      f output
      return result
    where
      bindOutput :: GroundsR t -> IO (Output t, t)
      bindOutput TupRunit = return ((), ())
      bindOutput (TupRpair tp1 tp2) = do
        (out1, result1) <- bindOutput tp1
        (out2, result2) <- bindOutput tp2
        return ((out1, out2), (result1, result2))
      bindOutput (TupRsingle tp)
        | Refl <- outputSingle tp = do
          ref <- newIORef $ internalError "Illegal schedule: Read from ref without value. Some synchronization might be missing."
          mvar <- newEmptyMVar
          -- We return the result lazily, as the value is not yet available
          let value = unsafePerformIO $ do
                readMVar mvar
                readIORef ref
          return ((SignalResolver mvar, OutputRef ref), value)
  callScheduledFun (GFunctionRlam arg ret) f = do
    return $ \a -> do
      input <- bindInput arg a
      callScheduledFun @UniformScheduleFun ret $ f input
    where
      bindInput :: GroundsR t -> t -> IO (Input t)
      bindInput TupRunit _ = return ()
      bindInput (TupRpair tp1 tp2) (val1, val2) = do
        in1 <- bindInput tp1 val1
        in2 <- bindInput tp2 val2
        return (in1, in2)
      bindInput (TupRsingle tp) value
        | Refl <- inputSingle tp = do
          ref <- newIORef $ internalError "Illegal schedule: Read from ref without value. Some synchronization might be missing."
          mvar <- newEmptyMVar
          -- We consume the result lazily. The computation can already start
          -- asynchronously, and some parts/threads of the computation may at
          -- some point block on the input to be available.
          forkIO $ do
            -- In a separate thread, evaluate to WHNF
            value `seq` return ()
            -- and write value to reference and resolve signal
            writeIORef ref value
            putMVar mvar ()
          return (Signal mvar, Ref ref)

-- A recursice Show instance for PreOpenAcc
instance Show (C.PreOpenAcc op env a) where
  show (C.Exec op args) = "Exec "
  show (C.Return a) = "Return " 
  show (C.Compute e) = "Compute (" ++ show e ++ ")" 
  show (C.Alet lhs u a b) = "Alet (" ++ show a ++ ") (" ++ show b ++ ")"
  show (C.Alloc sh e n) = "Alloc (" ++ show e ++ ")"
  show (C.Use e n b) = "Use (" ++ show e ++ ") (" ++ show n ++ ")"
  show (C.Unit e) = "Unit "
  show (C.Acond e a b) = "Acond (" ++ show a ++ ") (" ++ show b ++ ")"
  show (C.Awhile u a b c) = "Awhile (" ++ show a ++ ") (" ++ show b ++ ")"

instance Show (C.PreOpenAfun op env a) where
  show (C.Abody a) = "Abody (" ++ show a ++ ")"
  show (C.Alam lhs a) = "Alam (" ++ show a ++ ")"

instance Show (PreOpenFun arr env t) where
  show (Body e) = "Body (" ++ show e ++ ")"
  show (Lam lhs f) = "Lam (" ++ show f ++ ")"

instance Show (PreOpenExp arr env t) where
  show (Let lhs e1 e2) = "Let (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (Evar v) = "Evar "
  show (Foreign _ _ f e) = "Foreign (" ++ show f ++ ") (" ++ show e ++ ")"
  show (Pair e1 e2) = "Pair (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show Nil = "Nil"
  show (VecPack _ e) = "VecPack (" ++ show e ++ ")"
  show (VecUnpack _ e) = "VecUnpack (" ++ show e ++ ")"
  show (IndexSlice slix e1 e2) = "IndexSlice (" ++ show slix ++ ") (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (IndexFull slix e1 e2) = "IndexFull (" ++ show slix ++ ") (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (ToIndex _ e1 e2) = "ToIndex (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (FromIndex _ e1 e2) = "FromIndex (" ++ show e1 ++ ") (" ++ show e2 ++ ")"
  show (Case e1 e2 e3) = "Case (" ++ show e1 ++ ") (" ++ show e2 ++ ") (" ++ show e3 ++ ")"
  show (Cond e1 e2 e3) = "Cond (" ++ show e1 ++ ") (" ++ show e2 ++ ") (" ++ show e3 ++ ")"
  show (While e1 e2 e3) = "While (" ++ show e1 ++ ") (" ++ show e2 ++ ") (" ++ show e3 ++ ")"
  show (Const _ e) = "Const "
  show (PrimConst e) = "PrimConst "
  show (PrimApp e1 e2) = "PrimApp (" ++ show e2 ++ ")"
  show (ArrayInstr _ e) = "ArrayInstr (" ++ show e ++ ")"
  show (ShapeSize _ e) = "ShapeSize (" ++ show e ++ ")"
  show (Undef _) = "Undef"
  show (Coerce _ _ e) = "Coerce (" ++ show e ++ ")"

convertScheduleFun' :: IsKernel kernel => C.PartitionedAfun (KernelOperation kernel) env t -> UniformScheduleFun kernel env (Scheduled UniformScheduleFun t)
convertScheduleFun' = \case
  C.Abody a
    | grounds <- groundsR a
    , Refl <- (reprIsBody @UniformScheduleFun grounds)
    , DeclareVars lhs sub value <- declareVars $ outputR grounds
    -> Slam lhs $ Sbody $ convertScheduleAcc (value weakenId) (weaken sub a)
  --C.Alam lhs f -> Slam (convertLHSInput lhs) (convertScheduleFun' f)
  C.Alam lhs f 
    | DeclareInput sub lhs' _ <- declareInput PEnd lhs
    -> undefined --Slam lhs' (convertScheduleFun' f)

convertScheduleAcc :: IsKernel kernel => BaseVars env (Output t) -> C.PreOpenAcc (Cluster (KernelOperation kernel)) env t -> UniformSchedule kernel env
convertScheduleAcc _ (C.Exec op args) = undefined
convertScheduleAcc value (C.Return vs) = writeReturn value vs Return
convertScheduleAcc _ (C.Compute e) = undefined
convertScheduleAcc value (C.Alet lhs u a1 a2) = convertLet value (C.Alet lhs u a1 a2)
convertScheduleAcc _ (C.Alloc sh e n) = undefined
convertScheduleAcc _ (C.Use e n b) =  undefined
convertScheduleAcc _ (C.Unit e) =  undefined
convertScheduleAcc value (C.Acond e a1 a2) = Acond e (convertScheduleAcc value a1) (convertScheduleAcc value a2) Return
convertScheduleAcc _ (C.Awhile u a1 a2 a3) = undefined


convertLet :: IsKernel kernel => BaseVars env (Output t) -> C.PreOpenAcc (Cluster (KernelOperation kernel)) env t -> UniformSchedule kernel env
convertLet value (C.Alet lhs u (C.Exec op args) a) | Exists env <- convertEnvFromList $ map (foldr1 combineMod') $ groupBy (\(Exists v1) (Exists v2) -> isJust $ matchIdx (varIdx v1) (varIdx v2)) $ argsVars args -- TODO: Remove duplicates more efficiently
                                                  , Reads reEnv k inputBindings <- readRefs $ convertEnvRefs env
                                                  , Just args' <- reindexArgs (reEnvIdx' reEnv) args
                                                  , Just Refl <- leftHandSideIsVoid lhs
                                                  , CompiledKernel kern sargs <- compileKernel' op args
                                                  , DefineOutput doOutput _ varsOut <- defineOutput (groundsR (C.Exec op args)) u
                                                    = Effect (Exec (kernelMetadata kern) kern sargs) (convertScheduleAcc value a) --(writeReturn value vs Return)--(writeReturn (weakenVars (weakenWithLHS lhs) value) vs Return) --(convertScheduleAcc value (C.Return vs)) --(Effect (RefWrite undefined undefined) Return) --(Alet LeftHandSideUnit undefined (convertScheduleAcc a2))
                                                  where
                                                    combineMod' :: Exists (Var AccessGroundR env) -> Exists (Var AccessGroundR env) -> Exists (Var AccessGroundR env)
                                                    combineMod' (Exists (Var (AccessGroundRbuffer m1 tp) ix)) var@(Exists (Var (AccessGroundRbuffer m2 _) _))
                                                      | Exists' m <- combineMod m1 m2 = Exists $ Var (AccessGroundRbuffer m tp) ix
                                                      | otherwise = var
                                                    combineMod' a _ = a -- Nothing has to be done when combining two scalars; they don't have access modifiers

-- convertLet value (C.Alet lhs u (C.Awhile u1 (C.Alam lhs1 (C.Abody a1)) (C.Alam lhs2 (C.Abody a2)) vs) a) = let (io, vs', creates) = getIO vs
--                                                                --creates = getCreates vs vs'
--                                                             in
--                                                             creates $ Awhile io (f vs) vs' $ Alet (mapLeftHandSide BaseRground lhs) undefined (convertScheduleAcc (mapTupR (weaken (weakenWithLHS lhs)) value) a)
--                                                           where
--                                                             getIO :: GroundVars env a -> (InputOutputR (Input a) (Output a), BaseVars env (Input a), UniformSchedule kernel env -> UniformSchedule kernel env)
--                                                             getIO TupRunit = (InputOutputRunit, TupRunit, id)
--                                                             getIO (TupRsingle (Var v _)) | Refl <- inputSingle v
--                                                                                          , io' <-  InputOutputRpair InputOutputRsignal InputOutputRref
--                                                                                          , (sig, sigres) <- (BaseRsignal, BaseRsignalResolver)
--                                                                                          , (ref, oRef) <- (BaseRref v, BaseRrefWrite v)
--                                                                                          --, DeclareVars lhs sub vars <- declareVars (TupRpair (TupRsingle sig) (TupRsingle ref))
--                                                                                          --, vars <- TupRsingle sig `TupRpair` TupRsingle ref
--                                                                                          --, vars <- TupRsingle (Var sig $ SuccIdx $ SuccIdx ZeroIdx) `TupRpair` TupRsingle (Var ref ZeroIdx)
--                                                                                          , binds <- Alet (LeftHandSideWildcard (TupRpair (TupRsingle ref) (TupRsingle oRef))) (NewRef v) . Alet (LeftHandSideWildcard (TupRpair (TupRsingle sig) (TupRsingle sigres))) NewSignal
--                                                                                            = (io', undefined, binds)
--                                                             getIO (TupRpair vs1 vs2) = let (io1, vs1', l1) = getIO vs1
--                                                                                            (io2, vs2', l2) = getIO vs2
--                                                                                        in
--                                                                                          (InputOutputRpair io1 io2, TupRpair vs1' vs2', l1 . l2)

--                                                             f :: GroundVars env a -> UniformScheduleFun kernel env (Input a -> Output PrimBool -> Output a -> ())
--                                                             f _ = Slam _
--                                                                 $ Slam (LeftHandSideSingle BaseRsignalResolver `LeftHandSidePair` LeftHandSideSingle (BaseRrefWrite $ GroundRscalar scalarType))
--                                                                 $ Slam _
--                                                                 $ Sbody
--                                                                 $ serial [
--                                                                   convertScheduleAcc (mapTupR (weaken (weakenWithLHS lhs1)) value) a1
--                                                                 , Alet (LeftHandSideSingle $ BaseRground $ GroundRscalar scalarType) (RefRead $ Var (BaseRref $ GroundRscalar scalarType) $ SuccIdx ZeroIdx)
--                                                                 $ Acond (Var scalarType ZeroIdx) (convertScheduleAcc (mapTupR (weaken (weakenWithLHS lhs2)) value) a2) Return Return
--                                                                 ]
                                                            
                                                            --getCreates :: GroundVars env a -> BasesR (Input a) -> UniformSchedule kernel env -> UniformSchedule kernel env
                                                            --getCreates _ TupRunit = _

convertLet value (C.Alet lhs u a1 a2) = Alet (mapLeftHandSide BaseRground lhs) (convertBinding u a1) (convertScheduleAcc (mapTupR (weaken (weakenWithLHS lhs)) value) a2)

writeReturn :: IsKernel kernel => BaseVars env (Output t) -> GroundVars env t -> (UniformSchedule kernel env -> UniformSchedule kernel env)
writeReturn TupRunit TupRunit = id
writeReturn (TupRpair (TupRsingle (Var _ sig)) (TupRsingle v1)) (TupRsingle v2@(Var repr _)) | Refl <- outputSingle repr = Effect (RefWrite v1 (mapVar BaseRground v2)) . Effect (SignalResolve [sig])
writeReturn (TupRpair a1 b1) (TupRpair a2 b2) = writeReturn a1 a2 . writeReturn b1 b2

convertLHSInput :: GLeftHandSide a env env' -> BLeftHandSide (Input a) env env'
convertLHSInput (LeftHandSideWildcard vs) = LeftHandSideWildcard $ inputR vs
convertLHSInput (LeftHandSidePair lhs1 lhs2) = LeftHandSidePair (convertLHSInput lhs1) (convertLHSInput lhs2)
--convertLHSInput (LeftHandSideSingle v) | Refl <- inputSingle v, Exists lhs' <- rebuildLHS $ LeftHandSidePair (LeftHandSideSingle BaseRsignal) (LeftHandSideSingle (BaseRref v)) = lhs'

type family InputEnv env a where
  InputEnv env () = env
  InputEnv env (a, b) = ((env, Signal), Ref a)
  InputEnv env a = ((env, Signal), Ref a)

convertBinding :: Uniquenesses a -> C.PreOpenAcc (Cluster op) env t -> Binding env t
convertBinding _ (C.Compute e) = Compute e
convertBinding _ (C.Alloc sh e n) = Alloc sh e n
convertBinding _ (C.Use e n b) = Use e n b
convertBinding _ (C.Unit e) = Unit e
convertBinding _ x = traceShow x undefined



data UsageOpenAcc (op :: Type -> Type) env a where
  -- | Executes an executable operation. Such execution does not return a
  -- value, the effects of the execution are only visible by the mutation of
  -- buffers which were annotated with either 'Mut' or 'Out'.
  -- Provides the operation arguments from the environment.
  --
  UsageExec    :: op args
               -> Args env args
               -> UsageOpenAcc op env ()

  -- | Returns the values of the given variables.
  --
  UsageReturn  :: GroundVars env a
               -> UsageOpenAcc op env a

  -- | Evaluates the expression and returns its value.
  --
  UsageCompute :: Exp env t
               -> UsageOpenAcc op env t

  -- | Local binding of ground values.
  -- As it is common in this intermediate representation to evaluate some program
  -- resulting in unit, for instance when execution some operation, and then
  -- and then do some other code, we write 'a; b' to denote 'let () = a in b'.
  UsageAlet    :: SyncEnv env
               -> GLeftHandSide bnd env env'
               -> Uniquenesses bnd
               -> UsageOpenAcc op env  bnd
               -> UsageOpenAcc op env' t
               -> UsageOpenAcc op env  t

  -- | Allocates a new buffer of the given size.
  --
  UsageAlloc   :: ShapeR sh
               -> ScalarType e
               -> ExpVars env sh
               -> UsageOpenAcc op env (Buffer e)

  -- | Buffer inlet. To pass an array constant in this data type, one may need
  -- multiple 'Use' constructs because of the explicit Structure-of-Arrays.
  -- Triggers (possibly) asynchronous host->device transfer if necessary.
  --
  UsageUse     :: ScalarType e
               -> Int -- Number of elements
               -> Buffer e
               -> UsageOpenAcc op env (Buffer e)

  -- | Capture a scalar in a singleton buffer
  --
  UsageUnit    :: ExpVar env e
               -> UsageOpenAcc op env (Buffer e)

  -- | If-then-else for array-level computations
  --
  UsageAcond   :: SyncEnv env
               -> ExpVar env PrimBool
               -> UsageOpenAcc op env a
               -> UsageOpenAcc op env a
               -> UsageOpenAcc op env a

  -- Value-recursion for array-level computations
  -- The uniqueness guarantees are an invariant of the loop
  -- and should hold before and after each iteration.
  --
  UsageAwhile  :: SyncEnv env
               -> Uniquenesses a
               -> UsageOpenAfun op env (a -> PrimBool)
               -> UsageOpenAfun op env (a -> a)
               -> GroundVars     env a
               -> UsageOpenAcc  op env a

-- | Function abstraction over parametrised array computations
--
data UsageOpenAfun op env t where
  UsageAbody ::                             UsageOpenAcc  op env  t -> UsageOpenAfun op env t
  UsageAlam  :: GLeftHandSide a env env' -> UsageOpenAfun op env' t -> UsageOpenAfun op env (a -> t)

instance HasGroundsR (UsageOpenAcc op env) where
  groundsR (UsageExec _ _)         = TupRunit
  groundsR (UsageReturn vars)      = groundsR vars
  groundsR (UsageCompute e)        = groundsR e
  groundsR (UsageAlet _ _ _ _ a)   = groundsR a
  groundsR (UsageAlloc _ tp _)     = TupRsingle $ GroundRbuffer tp
  groundsR (UsageUse tp _ _)       = TupRsingle $ GroundRbuffer tp
  groundsR (UsageUnit (Var tp _))  = TupRsingle $ GroundRbuffer tp
  groundsR (UsageAcond _ _ a _)    = groundsR a
  groundsR (UsageAwhile _ _ _ _ a) = groundsR a

usageAnalysisOpenAcc ::C.PreOpenAcc op env t -> UsageOpenAcc op env t
usageAnalysisOpenAcc (C.Exec op args) = UsageExec op args
usageAnalysisOpenAcc (C.Return vs) = UsageReturn vs
usageAnalysisOpenAcc (C.Compute e) = UsageCompute e
usageAnalysisOpenAcc (C.Alet lhs u a1 a2) = let a1' = usageAnalysisOpenAcc a1
                                                a2' = usageAnalysisOpenAcc a2
                                                used = unionPartialEnv max (syncEnvUsage a1') (weakenSyncEnv lhs (syncEnvUsage a2'))
                                            in UsageAlet used lhs u a1' a2'
usageAnalysisOpenAcc (C.Alloc sh e n) = UsageAlloc sh e n
usageAnalysisOpenAcc (C.Use e n b) =  UsageUse e n b
usageAnalysisOpenAcc (C.Unit e) =  UsageUnit e
usageAnalysisOpenAcc (C.Acond e a1 a2) = let a1' = usageAnalysisOpenAcc a1
                                             a2' = usageAnalysisOpenAcc a2
                                             used = unionPartialEnv max (syncEnvUsage a1') (syncEnvUsage a2')
                                         in UsageAcond used e a1' a2'
usageAnalysisOpenAcc (C.Awhile u a1 a2 vs) = let a1' = usageAnalysisOpenAFun a1
                                                 a2' = usageAnalysisOpenAFun a2
                                                 used = unionPartialEnv max (syncEnvFunUsage a1') $ unionPartialEnv max (syncEnvFunUsage a2') $ variablesToSyncEnv u vs
                                             in UsageAwhile used u a1' a2' vs


usageAnalysisOpenAFun :: C.PreOpenAfun op env t -> UsageOpenAfun op env t
usageAnalysisOpenAFun (C.Abody a) = UsageAbody (usageAnalysisOpenAcc a)
usageAnalysisOpenAFun (C.Alam lhs f) = UsageAlam lhs (usageAnalysisOpenAFun f)


syncEnvUsage :: UsageOpenAcc op env t -> SyncEnv env
syncEnvUsage (UsageExec op args) = syncEnvFromList (argsVars args)
syncEnvUsage (UsageReturn vs) = variablesToReadSyncEnv vs
syncEnvUsage (UsageCompute e) = syncEnvReadFromList (expGroundVars e)
syncEnvUsage (UsageAlet s _ _ _ _) = s
syncEnvUsage (UsageAlloc sh e n) = PEnd
syncEnvUsage (UsageUse e n b) = PEnd
syncEnvUsage (UsageUnit e) = PEnd
syncEnvUsage (UsageAcond s _ _ _) = s
syncEnvUsage (UsageAwhile s _ _ _ _) = s

syncEnvFunUsage :: UsageOpenAfun op env t -> SyncEnv env
syncEnvFunUsage (UsageAlam lhs f) = weakenSyncEnv lhs $ syncEnvFunUsage f
syncEnvFunUsage (UsageAbody s)    = syncEnvUsage s

variablesToReadSyncEnv :: GroundVars genv t -> SyncEnv genv
variablesToReadSyncEnv vars = partialEnvFromList combine $ go vars []
  where
    go :: GroundVars genv t -> [EnvBinding Sync genv] -> [EnvBinding Sync genv]
    go (TupRsingle (Var (GroundRbuffer _) ix))
                          accum = EnvBinding ix SyncRead : accum
    go (TupRpair v1 v2) accum = go v1 $ go v2 accum
    go _                accum = accum

    combine :: Sync s -> Sync s -> Sync s
    combine SyncRead SyncRead = SyncRead
    combine _        _        = internalError "A writable buffer cannot be aliassed"

syncEnvReadFromList :: [Exists (GroundVar env)] -> SyncEnv env
syncEnvReadFromList vs = partialEnvFromList combine $ mapMaybe syncReadEnvVar vs
  where
    syncReadEnvVar :: Exists (GroundVar env) -> Maybe (EnvBinding Sync env)
    syncReadEnvVar (Exists (Var (GroundRscalar tp) ix)) = Nothing
    syncReadEnvVar (Exists (Var (GroundRbuffer tp) ix)) = Just $ EnvBinding ix SyncRead

    combine :: Sync s -> Sync s -> Sync s
    combine SyncRead SyncRead = SyncRead
    combine _        _        = internalError "A writable buffer cannot be aliassed"

syncEnvFromList :: [Exists (Var AccessGroundR env)] -> SyncEnv env
syncEnvFromList vs = partialEnvFromList combine $ mapMaybe syncEnvVar vs
  where
    combine :: Sync s -> Sync s -> Sync s
    combine SyncRead SyncRead = SyncRead
    combine _        _        = internalError "A writable buffer cannot be aliassed"

syncEnvVar :: Exists (Var AccessGroundR genv) -> Maybe (EnvBinding Sync genv)
syncEnvVar (Exists (Var (AccessGroundRscalar    tp) ix)) = Nothing
syncEnvVar (Exists (Var (AccessGroundRbuffer In tp) ix)) = Just $ EnvBinding ix SyncRead
syncEnvVar (Exists (Var (AccessGroundRbuffer m  tp) ix)) = Just $ EnvBinding ix SyncWrite


data OutputVar fenv t where
  OutputScalar :: ScalarType t
               -> Idx fenv (OutputRef t)
               -> Idx fenv SignalResolver
               -> OutputVar fenv t

  OutputBuffer :: ScalarType t
               -> Idx fenv (OutputRef (Buffer t))
               -> Idx fenv SignalResolver
               -> Idx fenv SignalResolver
               -> OutputVar fenv (Buffer t)

  OutputSingleBuffer :: ScalarType t
               -> Idx fenv (OutputRef (Buffer t))
               -> Idx fenv SignalResolver
               -> OutputVar fenv (Buffer t)

  OutputEmpty :: OutputVar fenv t

type OutputVars fenv = TupR (OutputVar fenv)

instance Sink OutputVar where
  weaken k (OutputScalar tp ref s) = OutputScalar tp (weaken k ref) (weaken k s)
  weaken k (OutputBuffer tp ref s1 s2) = OutputBuffer tp (weaken k ref) (weaken k s1) (weaken k s2)
  weaken k (OutputSingleBuffer tp ref s) = OutputSingleBuffer tp (weaken k ref) (weaken k s)

getOutputRef :: OutputVar fenv t -> Idx fenv (OutputRef t)
getOutputRef (OutputScalar _ ref _) = ref
getOutputRef (OutputBuffer _ ref _ _) = ref
getOutputRef (OutputSingleBuffer _ ref _) = ref

getOutputSignals :: OutputVar fenv t -> [Idx fenv SignalResolver]
getOutputSignals (OutputScalar _ _ s) = [s]
getOutputSignals (OutputBuffer _ _ s1 s2) = [s1, s2]
getOutputSignals (OutputSingleBuffer _ _ s) = [s]

fromUsage :: forall kernel env' t env. IsKernel kernel => OutputVars env' t -> FutureEnv env' env -> UsageOpenAcc (Cluster (KernelOperation kernel)) env t -> UniformSchedule kernel env'
fromUsage outputVars env (UsageExec op args) | Reads' reEnv k waits resolves reads <- readVars (partialEnvFromVarsList (map accesToGround (argsVars args))) env
                                             , Just args' <- reindexArgs (reEnvIdx' reEnv) args
                                             , CompiledKernel kern sargs <- compileKernel' op args'
                                               = useSignals SignalAwait waits
                                               $ reads
                                               $ Effect (Exec (kernelMetadata kern) kern sargs)
                                               $ useSignals SignalResolve (map (weaken k) resolves)
                                               Return
fromUsage outputVars env (UsageReturn vs) = let (signals, write) = getOutput outputVars vs env
                                            in useSignals SignalAwait signals write
fromUsage outputVars env (UsageAlet s lhs u a1 a2) | s1 <- getLhsVars lhs ++ getWriteVars (partialEnvSkipLHS lhs (syncEnvUsage a1))
                                                   , waits <- directlyWaits' a2
                                                   , False <- sort s1 `isSubsequenceOf` sort waits
                                                   , False <- isTrivial a1
                                                   , ChainFutureEnv splitInstr k1 envBnd envBody <- chainFutureEnvironment weakenId env (syncEnvUsage a1) (environmentDropLHS (syncEnvUsage a2) lhs)
                                                   , DeclareLet k2 instr outputBnd envBody' _ <- declareLet envBody lhs u
                                                   , bnd <- fromUsage outputBnd (mapPartialEnv (weaken k2) envBnd) a1
                                                   , body <- fromUsage (mapTupR (weaken (k2 .> k1)) outputVars) envBody' a2
                                                   = splitInstr $ instr $ Fork bnd body
fromUsage outputVars env (UsageAlet s lhs u a1 a2) | Just Refl <- leftHandSideIsVoid lhs
                                                   , ChainFutureEnv splitInstr k1 envBnd envBody <- chainFutureEnvironment weakenId env (syncEnvUsage a1) (environmentDropLHS (syncEnvUsage a2) lhs)
                                                   , DeclareLet k2 instr outputBnd envBody' _ <- declareLet envBody lhs u
                                                   , bnd <- fromUsage outputBnd (mapPartialEnv (weaken k2) envBnd) a1
                                                   , body <- fromUsage (mapTupR (weaken (k2 .> k1)) outputVars) envBody' a2
                                                   = splitInstr $ instr $ serial [bnd, body]
fromUsage outputVars env (UsageAlet s lhs u a1 a2) | ChainFutureEnv splitInstr k1 envBnd envBody <- chainFutureEnvironment weakenId env (syncEnvUsage a1) (environmentDropLHS (syncEnvUsage a2) lhs)
                                                   , FromUsageBinding used grnds f <- fromUsageBinding a1
                                                   , Reads' reEnv k2 waits resolves reads <- readVars (partialEnvFromVarsList used) envBnd
                                                   , AddVars k3 envBody' lhs' <- addVars lhs (mapPartialEnv (weaken k2) envBody)
                                                   , Just bnd <- f (reEnvIdx' reEnv)
                                                   , body <- fromUsage (mapTupR (weaken (k3 .> k2 .> k1)) outputVars) envBody' a2
                                                   = splitInstr 
                                                   $ useSignals SignalAwait waits
                                                   $ reads 
                                                   $ Alet lhs' bnd
                                                   $ useSignals SignalResolve (map (weaken (k3 .> k2)) resolves)
                                                   body
fromUsage outputVars env (UsageAlet s lhs u a1 a2) | ChainFutureEnv splitInstr k1 envBnd envBody <- chainFutureEnvironment weakenId env (syncEnvUsage a1) (environmentDropLHS (syncEnvUsage a2) lhs)
                                                   , FromUsageBinding used grnds f <- fromUsageBinding a1
                                                   , Reads' reEnv k2 waits resolves reads <- readVars (partialEnvFromVarsList used) envBnd
                                                   , DeclareVars lhs' k3 value <- declareVars $ mapTupR BaseRground grnds
                                                   , Nothing <- f (reEnvIdx' reEnv)
                                                   = undefined
fromUsage outputVars env c@UsageCompute{} = let FromUsageBinding used grnds f = fromUsageBinding c
                                            in fromUsageBinding' outputVars used grnds f env
fromUsage outputVars env a@UsageAlloc{}   = let FromUsageBinding used grnds f = fromUsageBinding a
                                            in fromUsageBinding' outputVars used grnds f env
fromUsage outputVars env u@UsageUse{}     = let FromUsageBinding used grnds f = fromUsageBinding u
                                            in fromUsageBinding' outputVars used grnds f env
fromUsage outputVars env u@UsageUnit{}    = let FromUsageBinding used grnds f = fromUsageBinding u
                                            in fromUsageBinding' outputVars used grnds f env
fromUsage outputVars env (UsageAcond s (Var _ ix) a1 a2) = case prjPartial ix env of
                                                            (Just (FutureScalar tp s r)) -> Effect (SignalAwait [s])
                                                                                          $ Alet (LeftHandSideSingle $ BaseRground $ GroundRscalar tp) (RefRead (Var (BaseRref $ GroundRscalar tp) r))
                                                                                          $ Acond (Var tp ZeroIdx)
                                                                                            (sub env' (syncEnvUsage a1) (\fenv -> fromUsage outputVars' fenv a1))
                                                                                            (sub env' (syncEnvUsage a2) (\fenv -> fromUsage outputVars' fenv a2))
                                                                                            Return
                                                                                          where
                                                                                            env' = mapPartialEnv (weaken (weakenSucc weakenId)) env
                                                                                            outputVars' = mapTupR (weaken (weakenSucc weakenId)) outputVars
                                                            (Just (FutureNoRef (GroundRscalar tp) ix)) -> Acond (Var tp ix)
                                                                                            (sub env (syncEnvUsage a1) (\fenv -> fromUsage outputVars fenv a1))
                                                                                            (sub env (syncEnvUsage a2) (\fenv -> fromUsage outputVars fenv a2))
                                                                                            Return                                                                            
fromUsage outputVars env while@UsageAwhile{} = undefined--fromUsageWhile outputVars env while

fromUsageFun :: IsKernel kernel => FutureEnv env' env -> UsageOpenAfun (Cluster (KernelOperation kernel)) env t -> UniformScheduleFun kernel env' (Scheduled UniformScheduleFun t)
fromUsageFun env (UsageAbody body) | grounds <- groundsR body
                                   , Refl <- reprIsBody @UniformScheduleFun $ grounds
                                   , DeclareVars lhs k1 value <- declareVars $ outputR grounds
                                   = Slam lhs $ Sbody $ fromUsage (go grounds (value weakenId)) (mapPartialEnv (weaken k1) env) body
                                   where
                                    go :: GroundsR t -> BaseVars env (Output t) -> OutputVars env t
                                    go TupRunit TupRunit = TupRunit
                                    go (TupRsingle tp@(GroundRscalar t)) (TupRpair (TupRsingle (Var BaseRsignalResolver ix1)) (TupRsingle (Var (BaseRrefWrite _) ix2))) | Refl <- outputSingle tp = TupRsingle $ OutputScalar t ix2 ix1
                                    go (TupRsingle (GroundRbuffer t)) (TupRpair (TupRsingle (Var BaseRsignalResolver ix1)) (TupRsingle (Var (BaseRrefWrite _) ix2))) = TupRsingle $ OutputSingleBuffer t ix2 ix1
                                    go (TupRpair g1 g2) (TupRpair v1 v2) = TupRpair (go g1 v1) (go g2 v2)
fromUsageFun env (UsageAlam lhs f) | DeclareLam lhs' env' <- declareLam env lhs 
                                   = Slam lhs' (fromUsageFun env' f)

data DeclareLam fenv env' t where
  DeclareLam :: BLeftHandSide (Input t) fenv fenv'
               -> FutureEnv fenv' env'
               -> DeclareLam fenv env' t

declareLam :: FutureEnv fenv env -> GLeftHandSide t env env' -> DeclareLam fenv env' t
declareLam env (LeftHandSidePair lhs1 lhs2) | DeclareLam lhs1' env1 <- declareLam env lhs1
                                            , DeclareLam lhs2' env2 <- declareLam env1 lhs2
                                            = DeclareLam (LeftHandSidePair lhs1'  lhs2') env2
declareLam env (LeftHandSideWildcard w) = DeclareLam (LeftHandSideWildcard (inputR w)) env
declareLam env (LeftHandSideSingle (GroundRscalar tp)) | Refl <- inputSingle $ GroundRscalar tp = DeclareLam 
                                                         (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle (BaseRref $ GroundRscalar tp))
                                                         (PPush (mapPartialEnv (weaken (weakenSucc $ weakenSucc weakenId)) env) (FutureScalar tp (SuccIdx ZeroIdx) ZeroIdx))
declareLam env (LeftHandSideSingle (GroundRbuffer tp)) = DeclareLam 
                                                         (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle (BaseRref $ GroundRbuffer tp))
                                                         (PPush (mapPartialEnv (weaken (weakenSucc $ weakenSucc weakenId)) env) (FutureBuffer tp undefined ZeroIdx (Move (SuccIdx ZeroIdx)) Nothing))

directlyWaits :: UniformSchedule kernel env -> [Idx env Signal]
directlyWaits (Effect (SignalAwait s) a) = s ++ directlyWaits a
directlyWaits (Alet lhs bnd a) = mapMaybe (strengthenWithLHS lhs) $ directlyWaits a
directlyWaits _ = []

directlyWaits' :: UsageOpenAcc op env t -> [Exists (GroundVar env)]
directlyWaits' (UsageExec op args) = map accesToGround (argsVars args)
directlyWaits' (UsageAlet s lhs u bnd a) = directlyWaits' bnd -- ++ mapMaybe (\(Exists (Var tp x)) -> Exists . Var tp <$> strengthenWithLHS lhs x) (directlyWaits' a)
directlyWaits' (UsageAlloc _ _ vs) = flattenTupR $ toGrounds vs
directlyWaits' (UsageUnit v) = [Exists (toGround v)]
directlyWaits' (UsageCompute e) = expGroundVars e
directlyWaits' (UsageAcond _ e a1 a2) = Exists (toGround e) : intersect' (directlyWaits' a1) (directlyWaits' a2)
directlyWaits' _ = []

isTrivial :: UsageOpenAcc op env t -> Bool
isTrivial UsageAlloc{} = True
isTrivial UsageUnit{} = True
isTrivial UsageReturn{} = True
isTrivial (UsageCompute e) = expIsTrivial (const True) e
isTrivial _ = False

intersect' :: Ord a => [a] -> [a] -> [a]
intersect' xs ys = go (sort xs) (sort ys)
  where
    go :: Ord a => [a] -> [a] -> [a]
    go [] _ = []
    go _ [] = []
    go (x:xs) (y:ys) = case compare x y of
                         LT -> go xs (y:ys)
                         EQ -> x : go xs ys
                         GT -> go (x:xs) ys

getLhsVars :: GLeftHandSide bnd env env' -> [Exists (GroundVar env')]
getLhsVars = snd . go
  where
    go :: GLeftHandSide bnd env env' -> (env :> env', [Exists (GroundVar env')])
    go (LeftHandSideSingle v) = (weakenSucc weakenId, [Exists (Var v ZeroIdx)])
    go (LeftHandSideWildcard vs) = (weakenId, [])
    go (LeftHandSidePair lhs1 lhs2) = let (k1, vs1) = go lhs1
                                          (k2, vs2) = go lhs2
                                      in (k2 .> k1, weakenExistss k2 vs1 ++ vs2)

getWriteVars :: SyncEnv env -> [Exists (GroundVar env)]
getWriteVars env = mapMaybe go (partialEnvToList env)
  where
    go :: EnvBinding Sync env -> Maybe (Exists (GroundVar env))
    go (EnvBinding ix SyncWrite) = Just $ Exists (Var undefined ix)
    go _ = Nothing

instance Eq (Exists (GroundVar env')) where
  (Exists (Var x i1)) == (Exists (Var y i2)) = eqIdx i1 i2

eqIdx :: Idx env a -> Idx env a1 -> Bool
eqIdx ZeroIdx ZeroIdx = True
eqIdx (SuccIdx ix) (SuccIdx ix') = eqIdx ix ix'
eqIdx _ _ = False

instance Ord (Exists (GroundVar env')) where
  compare (Exists (Var _ i1)) (Exists (Var _ i2)) = compIdx i1 i2

compIdx :: Idx env a -> Idx env a1 -> Ordering
compIdx ZeroIdx ZeroIdx = EQ
compIdx (SuccIdx _) ZeroIdx = GT
compIdx ZeroIdx (SuccIdx _) = LT
compIdx (SuccIdx ix) (SuccIdx ix') = compIdx ix ix'

weakenExistss :: env :> env' -> [Exists (GroundVar env)] -> [Exists (GroundVar env')]
weakenExistss _ [] = []
weakenExistss k ((Exists v):vs) = Exists (weaken k v) : weakenExistss k vs

getOutput :: OutputVars env' t -> GroundVars env t -> FutureEnv env' env -> ([Idx env' Signal], UniformSchedule kernel env')
getOutput TupRunit TupRunit _ = ([], Return)
getOutput (TupRsingle outputVar) (TupRsingle (Var tp ix)) env = --(TupRpair (TupRpair (TupRsingle (Var BaseRsignalResolver s1)) (TupRsingle (Var BaseRsignalResolver s2))) (TupRsingle dest))
  case prjPartial ix env of
    Nothing -> ([], Return)
    Just (FutureScalar _ signal ref) -> ([signal], 
                                         Alet (LeftHandSideSingle $ BaseRground tp) (RefRead (Var (BaseRref tp) ref))
                                         $ Effect (RefWrite (weaken (weakenSucc weakenId) (Var (BaseRrefWrite tp) (getOutputRef outputVar))) (Var (BaseRground tp) ZeroIdx))
                                         $ Effect (SignalResolve (map (weakenSucc weakenId >:>) (getOutputSignals outputVar)))
                                         Return
                                        )
    Just (FutureNoRef _ ix) -> ([], 
                                         Effect (RefWrite (Var (BaseRrefWrite tp) (getOutputRef outputVar)) (Var (BaseRground tp) ix))
                                         $ Effect (SignalResolve (getOutputSignals outputVar))
                                         Return
                                        )
    Just (FutureBuffer _ _ ref read _) -> ([lockSignal read], 
                                         Alet (LeftHandSideSingle $ BaseRground tp) (RefRead (Var (BaseRref tp) ref))
                                         $ Effect (RefWrite (weaken (weakenSucc weakenId) (Var (BaseRrefWrite tp) (getOutputRef outputVar))) (Var (BaseRground tp) ZeroIdx))
                                         $ Effect (SignalResolve (map (weakenSucc weakenId >:>) (getOutputSignals outputVar)))
                                         Return
                                        )
getOutput (TupRpair t1 t2) (TupRpair v1 v2) env = let 
                               (s1, w1) = getOutput t1 v1 env
                               (s2, w2) = getOutput t2 v2 env
                             in (s1 ++ s2, serial [w1, w2])

data FromUsageBinding env t where
  FromUsageBinding :: [Exists (GroundVar env)]
                   -> GroundsR t
                   -> (forall fenv. env :?> fenv -> Maybe (Binding fenv t))
                   -> FromUsageBinding env t

fromUsageBinding :: forall t op env. UsageOpenAcc op env t -> FromUsageBinding env t
fromUsageBinding (UsageCompute e) = FromUsageBinding (expGroundVars e) (mapTupR GroundRscalar $ expType e) f
                                  where
                                    f :: env :?> fenv -> Maybe (Binding fenv t)
                                    f k = Compute <$> strengthenArrayInstr k e
fromUsageBinding (UsageAlloc sh tp n) = FromUsageBinding (expVarsList n) (TupRsingle $ GroundRbuffer tp) f
                                     where
                                       f :: env :?> fenv -> Maybe (Binding fenv t)
                                       f k = Alloc sh tp <$> strengthenVars k n
fromUsageBinding (UsageUse tp n b) = FromUsageBinding [] (TupRsingle $ GroundRbuffer tp) f
                                  where
                                    f :: env :?> fenv -> Maybe (Binding fenv t)
                                    f _ = Just (Use tp n b)
fromUsageBinding (UsageUnit e@(Var tp ix)) = FromUsageBinding [Exists (mapVar GroundRscalar e)] (TupRsingle $ GroundRbuffer tp) f
                               where
                                 f :: env :?> fenv -> Maybe (Binding fenv t)
                                 f k = Unit . Var tp <$> k ix
fromUsageBinding x = undefined

fromUsageBinding' :: IsKernel kernel => OutputVars env' t -> [Exists (GroundVar env)] -> GroundsR t -> (forall fenv. env :?> fenv -> Maybe (Binding fenv t)) -> FutureEnv env' env -> UniformSchedule kernel env'
fromUsageBinding' outputVars used grnds f env | Reads' reEnv k waits resolves reads <- readVars (partialEnvFromVarsList used) env,
                                           DeclareVars lhs k' value <- declareVars $ mapTupR BaseRground grnds,
                                           Just bnd <- f (reEnvIdx' reEnv),
                                           write <- bindOutput (mapTupR (weaken (k' .> k)) outputVars) (value weakenId)
                                          = useSignals SignalAwait waits
                                            $ reads
                                            $ Alet lhs bnd
                                            $ useSignals SignalResolve (map (weaken (k' .> k)) resolves)
                                            write

useSignals :: ([Idx env s] -> Effect kernel env) -> [Idx env s] -> (UniformSchedule kernel env -> UniformSchedule kernel env)
useSignals _ [] = id
useSignals f s = Effect (f s)

bindOutput :: OutputVars env' t -> BaseVars env' t -> UniformSchedule kernel env'
bindOutput outputVars vars = go outputVars vars Return
  where 
    go :: OutputVars env' t -> BaseVars env' t -> UniformSchedule kernel env' -> UniformSchedule kernel env'
    go TupRunit TupRunit = id
    go (TupRsingle outputVar) (TupRsingle v@(Var (BaseRground tp) ix)) = Effect (RefWrite (Var (BaseRrefWrite tp) (getOutputRef outputVar)) v) . Effect (SignalResolve (getOutputSignals outputVar))
    go (TupRpair o1 o2) (TupRpair v1 v2) = go o1 v1 . go o2 v2

data DeclareLet kernel fenv env' t where
  DeclareLet :: fenv :> fenv'
             -> (UniformSchedule kernel fenv' -> UniformSchedule kernel fenv)
             -> OutputVars fenv' t
             -> FutureEnv fenv' env'
             -> [Idx fenv' Signal]
             -> DeclareLet kernel fenv env' t

declareLet :: FutureEnv fenv env -> GLeftHandSide t env env' -> Uniquenesses t -> DeclareLet kernel fenv env' t --(fenv :> fenv', UniformSchedule kernel fenv' -> UniformSchedule kernel fenv, BaseVars fenv (Output t), FutureEnv fenv env')
declareLet env (LeftHandSidePair lhs1 lhs2) (TupRpair u1 u2) | DeclareLet k1 instr1 output1 env1 s1 <- declareLet env lhs1 u1
                                                             , DeclareLet k2 instr2 output2 env2 s2 <- declareLet env1 lhs2 u2
                                                             = DeclareLet (k2 .> k1) (instr1 . instr2) (TupRpair (mapTupR (weaken k2) output1) output2) env2 (map (weaken k2) s1 ++ s2)
declareLet env (LeftHandSideWildcard TupRunit) TupRunit = DeclareLet weakenId id TupRunit env []
declareLet env (LeftHandSideWildcard _) _ = DeclareLet weakenId id (TupRsingle OutputEmpty) env []
declareLet env (LeftHandSideSingle t@(GroundRscalar tp)) _ = DeclareLet
                                                            (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId)
                                                            (Alet lhsSignal NewSignal
                                                            . Alet (lhsRef $ GroundRscalar tp) (NewRef $ GroundRscalar tp))
                                                            (TupRsingle (OutputScalar tp idx0 idx2))  --(TupRpair (TupRpair undefined (TupRsingle (Var BaseRsignalResolver idx2))) (TupRsingle (Var (BaseRrefWrite $ GroundRscalar tp) idx0)))
                                                            (PPush (mapPartialEnv (weaken (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId)) env)
                                                            $ FutureScalar tp idx3 idx1)
                                                            [idx3]
                                                          where
                                                            idx0 = ZeroIdx
                                                            idx1 = SuccIdx ZeroIdx
                                                            idx2 = SuccIdx $ SuccIdx ZeroIdx
                                                            idx3 = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
declareLet env (LeftHandSideSingle t@(GroundRbuffer tp)) (TupRsingle Unique) = DeclareLet
                                                            (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId)
                                                            (Alet lhsSignal NewSignal
                                                            . Alet lhsSignal NewSignal
                                                            . Alet (lhsRef $ GroundRbuffer tp) (NewRef $ GroundRbuffer tp))
                                                            (TupRsingle (OutputBuffer tp idx0 idx2 idx4)) --(TupRpair (TupRpair (TupRsingle (Var BaseRsignalResolver idx2)) (TupRsingle (Var BaseRsignalResolver idx4))) (TupRsingle (Var (BaseRrefWrite $ GroundRbuffer tp) idx0)))
                                                            (PPush (mapPartialEnv (weaken (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId)) env)
                                                            $ FutureBuffer tp undefined idx1 (Move idx3) (Just (Move idx5)))
                                                            [idx3, idx5]
                                                          where
                                                            idx0 = ZeroIdx
                                                            idx1 = SuccIdx ZeroIdx
                                                            idx2 = SuccIdx $ SuccIdx ZeroIdx
                                                            idx3 = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
                                                            idx4 = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
                                                            idx5 = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
declareLet env (LeftHandSideSingle t@(GroundRbuffer tp)) (TupRsingle Shared) = DeclareLet
                                                            (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId)
                                                            (Alet lhsSignal NewSignal
                                                            . Alet (lhsRef $ GroundRbuffer tp) (NewRef $ GroundRbuffer tp))
                                                            (TupRsingle (OutputSingleBuffer tp idx0 idx2)) --(TupRpair (TupRpair (TupRsingle (Var BaseRsignalResolver idx2)) (TupRsingle (Var BaseRsignalResolver idx4))) (TupRsingle (Var (BaseRrefWrite $ GroundRbuffer tp) idx0)))
                                                            (PPush (mapPartialEnv (weaken (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId)) env)
                                                            $ FutureBuffer tp undefined idx1 (Move idx3) Nothing)
                                                            [idx3]
                                                          where
                                                            idx0 = ZeroIdx
                                                            idx1 = SuccIdx ZeroIdx
                                                            idx2 = SuccIdx $ SuccIdx ZeroIdx
                                                            idx3 = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx

data AddVars fenv env' t where
  AddVars :: fenv :> fenv'
          -> FutureEnv fenv' env'
          -> BLeftHandSide t fenv fenv'
          -> AddVars fenv env' t

addVars :: GLeftHandSide t env env' -> FutureEnv fenv env -> AddVars fenv env' t
addVars (LeftHandSideWildcard t) env = AddVars weakenId env (LeftHandSideWildcard (mapTupR BaseRground t))
addVars (LeftHandSideSingle tp) env = AddVars (weakenSucc weakenId) (PPush (mapPartialEnv (weaken (weakenSucc weakenId)) env) $ FutureNoRef tp ZeroIdx) (LeftHandSideSingle (BaseRground tp))
addVars (LeftHandSidePair lhs1 lhs2) env | AddVars k1 env1 lhs1' <- addVars lhs1 env
                                         , AddVars k2 env2 lhs2' <- addVars lhs2 env1
                                         = AddVars (k2 .> k1) env2 (LeftHandSidePair lhs1' lhs2')

accesToGround :: Exists (Var AccessGroundR env) -> Exists (Var GroundR env)
accesToGround (Exists (Var (AccessGroundRscalar tp) ix)) = Exists (Var (GroundRscalar tp) ix)
accesToGround (Exists (Var (AccessGroundRbuffer _ tp) ix)) = Exists (Var (GroundRbuffer tp) ix)

data Reads' kernel genv fenv where
  Reads' :: ReEnv' genv fenv'
        -> (fenv :> fenv')
        -> [Idx fenv Signal]
        -> [Idx fenv SignalResolver]
        -> (UniformSchedule kernel fenv' -> UniformSchedule kernel fenv)
        -> Reads' kernel genv fenv

readVars :: PartialEnv (Var GroundR env) env' -> FutureEnv fenv env -> Reads' kernel env' fenv --(ReEnv' env fenv', fenv :> fenv', UniformSchedule kernel fenv' -> UniformSchedule kernel fenv)
readVars PEnd env = Reads' ReEnvEnd' weakenId [] [] id
readVars (PPush vars (Var tp ix)) env | Reads' reEnv k waits resolves reads <- readVars vars env
                                           = case prjPartial ix env of
                                               Nothing -> undefined
                                               Just (FutureNoRef _ ix) -> Reads' (ReEnvId' (weaken k ix) reEnv) k waits resolves reads
                                               Just (FutureScalar _ s ref) -> Reads' (ReEnvKeep' reEnv) (weakenSucc' k) (s:waits) resolves (reads . Alet (LeftHandSideSingle (BaseRground tp)) (RefRead (Var (BaseRref tp) (weaken k ref))))
                                               Just (FutureBuffer _ _ ref read write) -> Reads' (ReEnvKeep' reEnv) (weakenSucc' k) (lockSignal read : getWriteWait write ++ waits) (getResolves (Just read) ++ getResolves write ++ resolves) (reads . Alet (LeftHandSideSingle (BaseRground tp)) (RefRead (Var (BaseRref tp) (weaken k ref))))
                                           where
                                            getResolves :: Maybe (Lock env) -> [Idx env SignalResolver]
                                            getResolves (Just (Borrow _ s)) = [s]
                                            getResolves _ = []

                                            getWriteWait :: Maybe (Lock env) -> [Idx env Signal]
                                            getWriteWait (Just l) = [lockSignal l]
                                            getWriteWait _ = []
readVars (PNone vars) env | Reads' reEnv k waits resolves reads <- readVars vars env
                          = Reads' (ReEnvSkip' reEnv) k waits resolves reads

partialEnvFromVarsList :: [Exists (Var GroundR env)] -> PartialEnv (Var GroundR env) env
partialEnvFromVarsList vars = partialEnvFromList const $ map go vars
  where
    go :: Exists (Var GroundR env) -> EnvBinding (Var GroundR env) env
    go (Exists v@(Var tp ix)) = EnvBinding ix v

fromUsageWhile :: forall kernel env' t env. IsKernel kernel => OutputVars env' t -> FutureEnv env' env -> UsageOpenAcc (Cluster (KernelOperation kernel)) env t -> UniformSchedule kernel env'
fromUsageWhile outputVars env (UsageAwhile s u g@(UsageAlam lhsg _) b@(UsageAlam lhsb _) vs) 
  -- Split environment for initial vars and body
  | ChainFutureEnv instrSplit k0 envInitial envLoop <- chainFutureEnvironment (weakenSucc $ weakenSucc weakenId) env (variablesToSyncEnv u vs) (unionPartialEnv max (syncEnvFunUsage g) (syncEnvFunUsage b))
  -- Create a LHS which brings variables in scope for both the condition and
  -- the step function. This is needed as they may have wildcards at different
  -- locations
  , Exists groundLhs <- unionLeftHandSides lhsg lhsb
  -- Create the input and output representations for the loop
  , AwhileInputOutput io k1 lhsInput envLoop' initial' outputEnv' outputRepr <- awhileInputOutput envInitial (\k -> mapPartialEnv (weaken k) envLoop) u vs groundLhs
  = Alet lhsSignal NewSignal
    $ Effect (SignalResolve [ZeroIdx])
    $ instrSplit 
    $ Awhile io f initial' Return
    where
      f = undefined




rnfSchedule' :: IsKernel kernel => UniformSchedule kernel env -> ()
rnfSchedule' Return                        = ()
rnfSchedule' (Alet lhs bnd body)           = rnfLeftHandSide rnfBaseR lhs `seq` rnfBinding bnd `seq` rnfSchedule' body
rnfSchedule' (Effect eff next)             = rnfEffect eff `seq` rnfSchedule' next
rnfSchedule' (Acond c true false next)     = rnfExpVar c `seq` rnfSchedule' true `seq` rnfSchedule' false `seq` rnfSchedule' next
rnfSchedule' (Awhile io body initial next) = rnfInputOutputR io `seq` rnfSchedule body `seq` rnfTupR rnfBaseVar initial `seq` rnfSchedule' next
rnfSchedule' (Fork a b)                    = rnfSchedule' a `seq` rnfSchedule' b

rnfBinding :: Binding env t -> ()
rnfBinding (Compute e)       = rnfOpenExp e
rnfBinding NewSignal         = ()
rnfBinding (NewRef r)        = rnfGroundR r
rnfBinding (Alloc shr tp sz) = rnfShapeR shr `seq` rnfScalarType tp `seq` rnfTupR rnfExpVar sz
rnfBinding (Use tp n buffer) = buffer `seq` n `seq` rnfScalarType tp
rnfBinding (Unit var)        = rnfExpVar var
rnfBinding (RefRead r)       = rnfBaseVar r

rnfEffect :: IsKernel kernel => Effect kernel env -> ()
rnfEffect (Exec md kernel args)   = rnf' md `seq` rnf' kernel `seq` rnfSArgs args
rnfEffect (SignalAwait signals)   = rnf signals
rnfEffect (SignalResolve signals) = rnf signals
rnfEffect (RefWrite ref value)    = rnfBaseVar ref `seq` rnfBaseVar value

rnfBaseVar :: BaseVar env t -> ()
rnfBaseVar = rnfVar rnfBaseR

rnfSArgs :: SArgs env args -> ()
rnfSArgs ArgsNil = ()
rnfSArgs (arg :>: args) = rnfSArg arg `seq` rnfSArgs args

rnfSArg :: SArg env t -> ()
rnfSArg (SArgScalar var)      = rnfExpVar var
rnfSArg (SArgBuffer mod' var) = mod' `seq` rnfGroundVar var

rnfInputOutputR :: InputOutputR input output -> ()
rnfInputOutputR (InputOutputRpair io1 io2) = rnfInputOutputR io1 `seq` rnfInputOutputR io2
rnfInputOutputR _ = ()

{-
-- * Compilation from PartitionedAcc to UniformSchedule
data FutureValue senv t
  = Future (BaseVar senv (Ref t)) (BaseVar senv Signal)
  | Ready (BaseVar senv t)

weakenFutureValue :: senv :> senv' -> FutureValue senv t -> FutureValue senv' t
weakenFutureValue k (Future ref sig) = Future (weaken k ref) (weaken k sig)
weakenFutureValue k (Ready var)      = Ready (weaken k var)

data SignalInfo senv t where
  -- Bool denotes whether the signal was already waited on.
  SignalImplies :: Bool -> [Idx senv Signal] -> SignalInfo senv Signal
  -- The SignalResolver resolves the given Signal
  SignalResolvesTo :: Idx senv Signal -> SignalInfo senv SignalResolver
  -- Used for bindings in the environment which are not a signal, or signal which don't have any implications linked to it
  SignalNone    :: SignalInfo senv t

type SignalEnv senv = Env (SignalInfo senv) senv
-}
{-
data Strengthen env env' where
  StrengthenId :: Strengthen env env
  StrengthenSucc :: Strengthen env env' -> Strengthen (env, t) env'

strengthenIdx :: Strengthen env env' -> env :?> env'
strengthenIdx StrengthenId       idx           = Just idx
strengthenIdx (StrengthenSucc k) (SuccIdx idx) = strengthenIdx k idx
strengthenIdx (StrengthenSucc _) ZeroIdx       = Nothing
-}
{-
strengthenSignalInfo :: Strengthen senv senv' -> SignalInfo senv t -> SignalInfo senv' t
strengthenSignalInfo _ SignalNone          = SignalNone
strengthenSignalInfo k (SignalImplies r i) = SignalImplies r $ mapMaybe (strengthenIdx k) i

strengthenSignalEnv :: forall senv senv'. Strengthen senv senv' -> SignalEnv senv -> SignalEnv senv'
strengthenSignalEnv StrengthenId = id
strengthenSignalEnv k = go k
  where
    go :: forall senv1. Strengthen senv1 senv' -> Env (SignalInfo senv) senv1 -> SignalEnv senv'
    go StrengthenId env = mapEnv (strengthenSignalInfo k) env
    go (StrengthenSucc k') (Push env _) = go k' env

weakenSignalInfo :: senv :> senv' -> SignalInfo senv t -> SignalInfo senv' t
weakenSignalInfo _ SignalNone          = SignalNone
weakenSignalInfo k (SignalImplies r i) = SignalImplies r $ map (k >:>) i

weakenSignalEnv :: senv :> senv' -> SignalEnv senv -> Env (SignalInfo senv') senv
weakenSignalEnv k = mapEnv (weakenSignalInfo k)
-}
{-
-- A list of resolved signals (which we already awaited on),
-- and an environment mapping the ground variables to future values.
data FEnv senv genv = FEnv
  -- A list of signals we waited on and the last signal we resolved. This is used to build `SignalImplies` we waiting on a next signal.
  -- Note that we only store one last resolved signal, as we create a chain of resolved signals in the SignalEnv.
  { fenvAwaitedSignals :: [Idx senv Signal]
  -- Set of implications between signal, denoting that some signal will already be resolved when waiting on some other signal.
  , fenvSignalInfo :: SignalEnv senv
  -- Mapping from the ground environment (as used in PartitionedAcc) to the new environment
  , fenvGround     :: Env (FutureValue senv) genv
  }
  -}

{-
-- Returns a new environment, which contains the information that this signal (and possibly others)
-- are resolved (have been waited on). Also returns a Bool denoting whether we should explicitly wait
-- on this signal. I.e., when it returns False, the signal was already previously waited on (possibly
-- indirectly through some other signal), so we don't have to wait on it again.
awaitSignal :: forall senv genv. Idx senv Signal -> FEnv senv genv -> (FEnv senv genv, Bool)
awaitSignal idx fenv = (fenv', shouldWait)
  where
    (signalEnv, shouldWait) = go True idx (fenvSignalInfo fenv)
    fenv' = fenv{ fenvAwaitedSignals = if shouldWait then idx : fenvAwaitedSignals fenv else fenvAwaitedSignals fenv, fenvSignalInfo = signalEnv }

    go :: Bool -> Idx senv Signal -> Env (SignalInfo senv) senv -> (Env (SignalInfo senv) senv, Bool)
    go direct idx' env = (foldr (\ix env' -> fst $ go False ix env') env' implied, shouldWait')
      where
        (env', (implied, shouldWait')) = prjUpdate' f idx' env
        f :: SignalInfo senv Signal -> (SignalInfo senv Signal, ([Idx senv Signal], Bool))
        f SignalNone              = (SignalImplies True [], ([], True))
        f (SignalImplies False i) = (SignalImplies True i , (i , True))
        f (SignalImplies True  i) = (SignalImplies True i , ([], False))

awaitSignals :: [Idx senv Signal] -> FEnv senv genv -> (FEnv senv genv, [Idx senv Signal])
awaitSignals signals fenv = (foldr (\idx fenv' -> fst $ awaitSignal idx fenv') fenv signals, minimal)
  where
    minimal = minimalAwaitSignals fenv signals

-- Computes the transitive closure of the 'implies' relation on signals.
-- Stops the descend at signals in 'stopAt'.
signalTransitiveClosure :: forall senv genv. S.Set (Idx senv Signal) -> Idx senv Signal -> FEnv senv genv -> S.Set (Idx senv Signal)
signalTransitiveClosure stopAt idx fenv = go idx S.empty
  where
    go :: Idx senv Signal -> S.Set (Idx senv Signal) -> S.Set (Idx senv Signal)
    go idx' visited
      | idx' `S.member` visited = visited
      | idx' `S.member` stopAt = S.insert idx' visited
      | otherwise = case prj' idx' $ fenvSignalInfo fenv of
          SignalImplies False i -> foldr go (S.insert idx' visited) i
          _                     -> S.insert idx' visited

-- Shortens a list of signals, such that awaiting this shorter list implies that all the signals are resolved.
minimalAwaitSignals :: forall senv genv. FEnv senv genv -> [Idx senv Signal] -> [Idx senv Signal]
minimalAwaitSignals fenv signals = map fst $ filter f reachables
  where
    f :: (Idx senv Signal, S.Set (Idx senv Signal)) -> Bool
    f self = any (isImpliedBy self) reachables

    -- 'self' is implied by 'other' if 'self' is in 'otherImplies' and if they do not form a cycle.
    -- In case of a cycle, we say that the lowest index implies the other.
    isImpliedBy :: (Idx senv Signal, S.Set (Idx senv Signal)) -> (Idx senv Signal, S.Set (Idx senv Signal)) -> Bool
    isImpliedBy (self, selfImplies) (other, otherImplies)
      | self == other = False
      | self `S.member` otherImplies
        = if other `S.member` selfImplies then
            -- Cycle. We say that the lowest index implies the other. Thus, 'self' is implied by 'other' if other < self.
            other < self
          else
            -- No cycle. 'self' is implied by 'other'.
            True
      | otherwise = False
    
    reachables :: [(Idx senv Signal, S.Set (Idx senv Signal))]
    reachables = map (\idx -> (idx, signalTransitiveClosure set idx fenv)) signals

    set = S.fromList signals

resolveSignal :: FEnv senv genv -> Idx senv SignalResolver -> FEnv senv genv
resolveSignal fenv resolver
  | SignalResolvesTo signal <- prj' resolver $ fenvSignalInfo fenv =
    let
      (signalEnv, _) = prjReplace' signal (SignalImplies True (fenvAwaitedSignals fenv)) $ fenvSignalInfo fenv
    in
      fenv{ fenvSignalInfo = signalEnv, fenvAwaitedSignals = [signal] }
resolveSignal fenv _ = fenv

resolveSignals :: forall senv genv. FEnv senv genv -> [Idx senv SignalResolver] -> FEnv senv genv
resolveSignals fenv resolvers = case signals of
  []                -> fenv
  (firstSignal : _) -> fenv{ fenvSignalInfo = signalEnv, fenvAwaitedSignals = [firstSignal] }
  where
    signals = mapMaybe findSignal $ nub resolvers

    findSignal :: Idx senv SignalResolver -> Maybe (Idx senv Signal)
    findSignal idx = case prj' idx $ fenvSignalInfo fenv of
      SignalResolvesTo signal -> Just signal
      _ -> Nothing

    signalsWithOthers :: [(Idx senv Signal, [Idx senv Signal])]
    signalsWithOthers = mapWithRemainder (\ix ixs -> (ix, ixs)) signals

    signalEnv = updates' f signalsWithOthers $ fenvSignalInfo fenv

    f others _ = SignalImplies True (others ++ fenvAwaitedSignals fenv)

mapWithRemainder :: forall a b. (a -> [a] -> b) -> [a] -> [b]
mapWithRemainder f = go []
  where
    go :: [a] -> [a] -> [b]
    -- prefix is in reverse order
    go prefix (x : xs) = f x (reverseAppend prefix xs) : go (x : prefix) xs
    go _      []       = []

    -- Reverses the first list and appends it to the second
    reverseAppend :: [a] -> [a] -> [a]
    reverseAppend []     accum = accum
    reverseAppend (x:xs) accum = reverseAppend xs (x : accum)
-}
{-

awaitFuture :: FEnv senv genv -> GroundVars genv t -> (forall senv'. senv :> senv' -> BaseVars senv' t -> UniformSchedule kernel senv') -> UniformSchedule kernel senv
awaitFuture env1 vars1
  = let (symbols, res) = go env1 vars1
  where
    go :: FEnv senv genv -> GroundVars genv t -> (forall senv'. senv :> senv' -> BaseVars senv' t -> UniformSchedule kernel senv') -> ([Var senv Signal], UniformSchedule kernel senv)
    go env TupRunit f = ([], f weakenId TupRunit)
    go env (TupRsingle )

prjAwaitFuture :: FEnv senv genv -> GroundVar genv t -> Either (BaseVar env t) (BaseVar env Signal, BaseVar env (Ref t), FEnv (senv, t) genv)
prjAwaitFuture (Push _    (Ready var))         (Var _ ZeroIdx) = Left var
prjAwaitFuture (Push senv (Future signal ref)) (Var _ ZeroIdx) = Right (signal, ref, )
  where
    senv' = mapEnv (weakenFutureValue (weakenSucc weakenId)) senv
    -}
{-
prj' :: Idx env t -> Env f env -> f t
prj' ZeroIdx       (Push _   v) = v
prj' (SuccIdx idx) (Push val _) = prj' idx val
-}

type SyncEnv = PartialEnv Sync

data Sync t where
  SyncRead  :: Sync (Buffer e)
  SyncWrite :: Sync (Buffer e)

instance Eq (Sync t) where
  SyncRead  == SyncRead  = True
  SyncWrite == SyncWrite = True
  _         == _         = False

instance Ord (Sync t) where
  SyncRead < SyncWrite = True
  _        < _         = False

  a <= b = a == b || a < b

data Acquire genv where
  Acquire :: Modifier m
          -> GroundVar genv (Buffer e)
          -- Returns a signal to wait on before the operation can start.
          -- In case of an input buffer (In), this signal refers to
          -- the last write to the buffer.
          -- In case of a Mut or Out buffer, it refers to all previous
          -- usages of the buffer, both reads and writes. The signal
          -- variable may thus later on be substituted for multiple
          -- variables.
          -- Also provides a SignalResolver which should be resolved
          -- when the operation is finished. Later reads or writes to
          -- this buffer will wait on this signal.
          -> Acquire genv

data ConvertEnv genv fenv fenv' where
  ConvertEnvNil     :: ConvertEnv genv fenv fenv

  ConvertEnvSeq     :: ConvertEnv genv fenv1 fenv2
                    -> ConvertEnv genv fenv2 fenv3
                    -> ConvertEnv genv fenv1 fenv3

  ConvertEnvAcquire :: Acquire genv
                    -> ConvertEnv genv fenv ((fenv, Signal), SignalResolver)

  ConvertEnvFuture  :: GroundVar genv e
                    -> ConvertEnv genv fenv ((fenv, Signal), Ref e)

data PartialDoOutput fenv fenv' t r where
  PartialDoOutputPair     :: PartialDoOutput fenv1 fenv2 t  r
                          -> PartialDoOutput fenv2 fenv3 t' r'
                          -> PartialDoOutput fenv1 fenv3 (t, t') (r, r')

  -- First SignalResolver grants access to the ref, the second grants read access and the
  -- third guarantees that all reads have been finished.
  -- Together they thus grant write access.
  --
  PartialDoOutputUnique   :: fenv' ~ ((((fenv, OutputRef (Buffer t)), SignalResolver), SignalResolver), SignalResolver)
                          => ScalarType t
                          -> PartialDoOutput fenv  fenv' (Buffer t) (((SignalResolver, SignalResolver), SignalResolver), OutputRef (Buffer t))

  -- First SignalResolver grants access to the ref, the second grants read access.
  --
  PartialDoOutputShared   :: fenv' ~ (((fenv, OutputRef (Buffer t)), SignalResolver), SignalResolver)
                          => ScalarType t
                          -> PartialDoOutput fenv  fenv' (Buffer t) ((SignalResolver, SignalResolver), OutputRef (Buffer t))

  -- Scalar values or shared buffers
  PartialDoOutputScalar   :: fenv' ~ ((fenv, OutputRef t), SignalResolver)
                          => ScalarType t
                          -> PartialDoOutput fenv  fenv' t (SignalResolver, OutputRef t)

  PartialDoOutputUnit     :: PartialDoOutput fenv  fenv () ()

partialDoOutputGroundsR :: PartialDoOutput fenv fenv' t r -> GroundsR t
partialDoOutputGroundsR (PartialDoOutputPair out1 out2) = partialDoOutputGroundsR out1 `TupRpair` partialDoOutputGroundsR out2
partialDoOutputGroundsR (PartialDoOutputUnique tp) = TupRsingle $ GroundRbuffer tp
partialDoOutputGroundsR (PartialDoOutputShared tp) = TupRsingle $ GroundRbuffer tp
partialDoOutputGroundsR (PartialDoOutputScalar tp) = TupRsingle $ GroundRscalar tp
partialDoOutputGroundsR PartialDoOutputUnit        = TupRunit

data OutputEnv t r where
  OutputEnvPair :: OutputEnv t  r
                 -> OutputEnv t' r'
                 -> OutputEnv (t, t') (r, r')

  -- The SignalResolvers grant access to the reference, to reading the buffer and writing to the buffer.
  -- The consumer of this buffer is the unique consumer of it, and thus takes ownership (and responsibility to deallocate it).
  OutputEnvUnique :: OutputEnv (Buffer t) (((SignalResolver, SignalResolver), SignalResolver), OutputRef (Buffer t))

  -- The SignalResolvers grant access to the reference and to reading the buffer.
  -- The consumer of this buffer does not get ownership, there may be multiple references to this buffer.
  OutputEnvShared :: OutputEnv (Buffer t) ((SignalResolver, SignalResolver), OutputRef (Buffer t))

  OutputEnvScalar :: ScalarType t -> OutputEnv t (SignalResolver, OutputRef t)

  -- There is no output (unit) or the output variables are reused
  -- with destination-passing-style.
  -- We thus do not need to copy the results manually.
  --
  OutputEnvIgnore :: OutputEnv t ()

data DefineOutput fenv t where
  DefineOutput :: PartialDoOutput fenv fenv' t r
                -> fenv :> fenv'
                -> (forall fenv'' . fenv' :> fenv'' -> BaseVars fenv'' r)
                -> DefineOutput fenv t

defineOutput :: forall fenv t.
                 GroundsR t
              -> Uniquenesses t
              -> DefineOutput fenv t
defineOutput (TupRsingle (GroundRbuffer tp)) (TupRsingle Unique) = DefineOutput env subst value
  where
    env = PartialDoOutputUnique tp

    subst = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId

    value :: forall fenv''. ((((fenv, OutputRef t), SignalResolver), SignalResolver), SignalResolver) :> fenv'' -> BaseVars fenv'' (((SignalResolver, SignalResolver), SignalResolver), OutputRef t)
    value k = ((TupRsingle (Var BaseRsignalResolver $ k >:> ZeroIdx) `TupRpair` TupRsingle (Var BaseRsignalResolver $ k >:> SuccIdx ZeroIdx)) `TupRpair` TupRsingle (Var BaseRsignalResolver (k >:> SuccIdx (SuccIdx ZeroIdx)))) `TupRpair` TupRsingle (Var (BaseRrefWrite $ GroundRbuffer tp) (k >:> SuccIdx (SuccIdx $ SuccIdx ZeroIdx)))
defineOutput (TupRsingle (GroundRscalar tp)) (TupRsingle Unique) = bufferImpossible tp
defineOutput (TupRsingle (GroundRbuffer tp)) _ = DefineOutput env subst value
  where
    env = PartialDoOutputShared tp

    subst = weakenSucc $ weakenSucc $ weakenSucc weakenId

    value :: forall fenv''. (((fenv, OutputRef t), SignalResolver), SignalResolver) :> fenv'' -> BaseVars fenv'' ((SignalResolver, SignalResolver), OutputRef t)
    value k = (TupRsingle (Var BaseRsignalResolver $ k >:> ZeroIdx) `TupRpair` TupRsingle (Var BaseRsignalResolver $ k >:> SuccIdx ZeroIdx)) `TupRpair` TupRsingle (Var (BaseRrefWrite $ GroundRbuffer tp) (k >:> SuccIdx (SuccIdx ZeroIdx)))
defineOutput (TupRsingle (GroundRscalar tp)) _ = DefineOutput env subst value
  where
    env = PartialDoOutputScalar tp

    subst = weakenSucc $ weakenSucc weakenId

    value :: forall fenv''. ((fenv, OutputRef t), SignalResolver) :> fenv'' -> BaseVars fenv'' (SignalResolver, OutputRef t)
    value k = TupRsingle (Var BaseRsignalResolver $ k >:> ZeroIdx) `TupRpair` TupRsingle (Var (BaseRrefWrite $ GroundRscalar tp) (k >:> SuccIdx ZeroIdx))
defineOutput (TupRpair t1 t2) us
  | DefineOutput out1 subst1 value1 <- defineOutput t1 u1
  , DefineOutput out2 subst2 value2 <- defineOutput t2 u2 = DefineOutput (PartialDoOutputPair out1 out2) (subst2 .> subst1) (\k -> value1 (k .> subst2) `TupRpair` value2 k)
  where
    (u1, u2) = pairUniqueness us
defineOutput TupRunit         _                     = DefineOutput PartialDoOutputUnit weakenId (const TupRunit)

writeOutput :: PartialDoOutput fenv fenv' t r -> BaseVars fenv'' r -> BaseVars fenv'' t -> UniformSchedule kernel fenv''
writeOutput doOutput outputVars valueVars = go doOutput outputVars valueVars Return
  where
    go :: PartialDoOutput fenv fenv' t r -> BaseVars fenv'' r -> BaseVars fenv'' t -> UniformSchedule kernel fenv'' -> UniformSchedule kernel fenv''
    go PartialDoOutputUnit _ _ = id
    go (PartialDoOutputPair o1 o2) (TupRpair r1 r2) (TupRpair v1 v2) = go o1 r1 v1 . go o2 r2 v2
    go (PartialDoOutputScalar _) (TupRpair (TupRsingle signal) (TupRsingle ref)) (TupRsingle v)
      = Effect (RefWrite ref v)
      . Effect (SignalResolve [varIdx signal])
    go (PartialDoOutputShared _) (TupRpair (TupRsingle s1 `TupRpair` TupRsingle s2) (TupRsingle ref)) (TupRsingle v)
      = Effect (RefWrite ref v)
      . Effect (SignalResolve [varIdx s1, varIdx s2])
    go (PartialDoOutputUnique _) (TupRpair (TupRpair (TupRsingle s1 `TupRpair` TupRsingle s2) (TupRsingle s3)) (TupRsingle ref)) (TupRsingle v)
      = Effect (RefWrite ref v)
      . Effect (SignalResolve [varIdx s1, varIdx s2, varIdx s3])
    go _ _ _ = internalError "Tuple mismatch in PartialDoOutput, output variables and value variables"

{-
data ConvertEnvRead kernel genv fenv1 where
  ConvertEnvRead :: (UniformSchedule kernel fenv2 -> UniformSchedule kernel fenv1)
                 -> (forall fenv3. ReEnv' genv fenv2 fenv3 -> ReEnv' genv fenv1 fenv3) -- TODO: This doesn't work. We need to assure that genv and fenv are in the same order
                 -> fenv1 :> fenv2
                 -> ConvertEnvRead kernel genv fenv1
-}
-- Void data type with orphan type argument.
-- Used to mark that a variable of the ground environment is used.
--
newtype FutureRef fenv t = FutureRef (BaseVar fenv (Ref t))

convertEnvRefs :: forall genv fenv fenv'. ConvertEnv genv fenv fenv' -> PartialEnv (FutureRef fenv') genv
convertEnvRefs env = partialEnvFromList const $ snd $ go weakenId env []
  where
    go :: fenv2 :> fenv' -> ConvertEnv genv fenv1 fenv2 -> [EnvBinding (FutureRef fenv') genv] -> (fenv1 :> fenv', [EnvBinding (FutureRef fenv') genv])
    go k ConvertEnvNil                  accum = (k, accum)
    go k (ConvertEnvSeq e1 e2)          accum = (k1, bs')
      where
        (k2, bs) = go k e2 accum
        (k1, bs') = go k2 e1 bs
    go k (ConvertEnvAcquire _)          accum = (weakenSucc $ weakenSucc k, accum)
    go k (ConvertEnvFuture (Var tp ix)) accum = (weakenSucc $ weakenSucc k, EnvBinding ix (FutureRef $ Var (BaseRref tp) $ k >:> ZeroIdx) : accum)

data Reads kernel genv fenv where
  Reads :: ReEnv' genv fenv'
        -> (fenv :> fenv')
        -> (UniformSchedule kernel fenv' -> UniformSchedule kernel fenv)
        -> Reads kernel genv fenv

readRefs :: PartialEnv (FutureRef fenv) genv -> Reads kernel genv fenv
readRefs PEnd = Reads ReEnvEnd' weakenId id
readRefs (PPush env (FutureRef (Var tp idx)))
  | Reads r k f <- readRefs env =
    let
      tp' = case tp of
        BaseRref t -> BaseRground t
        _ -> error "Impossible Ref base type"
      r' = ReEnvKeep' r
      k' = weakenSucc' k
      f' = f . Alet (LeftHandSideSingle tp') (RefRead $ Var tp $ k >:> idx)
    in
      Reads r' k' f'
readRefs (PNone env)
  | Reads r k f <- readRefs env = Reads (ReEnvSkip' r) k f

data ReEnv' genv fenv where
  ReEnvEnd'  :: ReEnv' genv fenv
  ReEnvSkip' :: ReEnv' genv fenv -> ReEnv' (genv, t) fenv
  ReEnvKeep' :: ReEnv' genv fenv -> ReEnv' (genv, t) (fenv, t)
  ReEnvId'   :: Idx fenv t -> ReEnv' genv fenv -> ReEnv' (genv, t) (fenv)

reEnvIdx' :: ReEnv' genv fenv -> genv :?> fenv
reEnvIdx' (ReEnvKeep' _) ZeroIdx      = Just ZeroIdx
reEnvIdx' (ReEnvId' ix _) ZeroIdx     = Just ix
reEnvIdx' (ReEnvKeep' r) (SuccIdx ix) = SuccIdx <$> reEnvIdx' r ix
reEnvIdx' (ReEnvSkip' r) (SuccIdx ix) = reEnvIdx' r ix
reEnvIdx' (ReEnvId' _ r) (SuccIdx ix) = reEnvIdx' r ix
reEnvIdx' _              _            = Nothing

convertEnvWeaken :: ConvertEnv genv fenv fenv' -> fenv :> fenv'
convertEnvWeaken ConvertEnvNil = weakenId
convertEnvWeaken (ConvertEnvAcquire _) = weakenSucc (weakenSucc weakenId)
convertEnvWeaken (ConvertEnvFuture _)  = weakenSucc (weakenSucc weakenId)
convertEnvWeaken (ConvertEnvSeq e1 e2) = convertEnvWeaken e2 .> convertEnvWeaken e1

convertEnvSignals :: forall genv fenv fenv'. ConvertEnv genv fenv fenv' -> [Idx fenv' Signal]
convertEnvSignals = snd . flip (go weakenId) []
  where
    go :: fenv2 :> fenv' -> ConvertEnv genv fenv1 fenv2 -> [Idx fenv' Signal] -> (fenv1 :> fenv', [Idx fenv' Signal])
    go k ConvertEnvNil         accum = (k, accum)
    go k (ConvertEnvAcquire _) accum = (weakenSucc $ weakenSucc k, k >:> SuccIdx ZeroIdx : accum)
    go k (ConvertEnvFuture _)  accum = (weakenSucc $ weakenSucc k, k >:> SuccIdx ZeroIdx : accum)
    go k (ConvertEnvSeq e1 e2) accum = go k' e1 accum'
      where
        (k', accum') = go k e2 accum

convertEnvSignalResolvers :: forall genv fenv fenv' fenv''. fenv' :> fenv'' -> ConvertEnv genv fenv fenv' -> [Idx fenv'' SignalResolver]
convertEnvSignalResolvers k1 = snd . flip (go k1) []
  where
    go :: fenv2 :> fenv'' -> ConvertEnv genv fenv1 fenv2 -> [Idx fenv'' SignalResolver] -> (fenv1 :> fenv'', [Idx fenv'' SignalResolver])
    go k ConvertEnvNil         accum = (k, accum)
    go k (ConvertEnvAcquire _) accum = (weakenSucc $ weakenSucc k, k >:> ZeroIdx : accum)
    go k (ConvertEnvFuture _)  accum = (weakenSucc $ weakenSucc k, accum)
    go k (ConvertEnvSeq e1 e2) accum = go k' e1 accum'
      where
        (k', accum') = go k e2 accum

convertEnvReadonlyFromList :: [Exists (GroundVar genv)] -> Exists (ConvertEnv genv fenv)
convertEnvReadonlyFromList []
    = Exists ConvertEnvNil
convertEnvReadonlyFromList [Exists var]
  | Exists e1 <- convertEnvReadonlyVar var
    = Exists e1
convertEnvReadonlyFromList (Exists var:vars)
  | Exists e1 <- convertEnvReadonlyVar var
  , Exists e2 <- convertEnvReadonlyFromList vars
    = Exists $ e1 `ConvertEnvSeq` e2

convertEnvReadonlyVar :: GroundVar genv t -> Exists (ConvertEnv genv fenv)
convertEnvReadonlyVar var@(Var tp _)
  | GroundRbuffer _ <- tp = Exists $ future `ConvertEnvSeq` ConvertEnvAcquire (Acquire In var)
  | otherwise             = Exists future
    where
      future = ConvertEnvFuture var

convertEnvFromList :: [Exists (Var AccessGroundR genv)] -> Exists (ConvertEnv genv fenv)
convertEnvFromList [] = Exists ConvertEnvNil
convertEnvFromList [Exists var]
  | Exists e1 <- convertEnvVar var
    = Exists e1
convertEnvFromList (Exists var:vars)
  | Exists e1 <- convertEnvVar var
  , Exists e2 <- convertEnvFromList vars
    = Exists $ e1 `ConvertEnvSeq` e2

convertEnvToList :: ConvertEnv genv fenv fenv' -> [Exists (Idx genv)]
convertEnvToList = (`go` [])
  where
    go :: ConvertEnv genv fenv fenv' -> [Exists (Idx genv)] -> [Exists (Idx genv)]
    go ConvertEnvNil = id
    go (ConvertEnvSeq e1 e2) = go e1 . go e2
    go (ConvertEnvAcquire (Acquire _ (Var _ idx))) = (Exists idx :)
    go (ConvertEnvFuture (Var _ idx)) = (Exists idx :)

convertEnvVar :: Var AccessGroundR genv t -> Exists (ConvertEnv genv fenv)
convertEnvVar (Var (AccessGroundRscalar    tp) ix) = Exists $ ConvertEnvFuture $ Var (GroundRscalar tp) ix
convertEnvVar (Var (AccessGroundRbuffer In tp) ix) = Exists $ ConvertEnvFuture var `ConvertEnvSeq` ConvertEnvAcquire (Acquire In var)
  where
    var = Var (GroundRbuffer tp) ix
convertEnvVar (Var (AccessGroundRbuffer m  tp) ix) = Exists $ ConvertEnvFuture var `ConvertEnvSeq` ConvertEnvAcquire (Acquire In var) `ConvertEnvSeq` ConvertEnvAcquire (Acquire m var)
  where
    var = Var (GroundRbuffer tp) ix

-- In PartialDeclare, we try to reuse the return address of the computation,
-- if this variable will be returned.
--
data Destination r t where
  DestinationNew   :: Destination r t
  DestinationReuse :: TupleIdx r t -> Destination r t

data PartialSchedule kernel genv t where
  PartialDo     :: PartialDoOutput () fenv t r
                -> ConvertEnv genv fenv fenv'
                -> UniformSchedule kernel fenv'
                -> PartialSchedule kernel genv t

  -- Returns a tuple of variables. Note that (some of) these
  -- variables may already have been resolved, as they may be
  -- annotated in PartialDeclare. We allow variables to unify,
  -- to prevent additional signals and references to be created.
  --
  PartialReturn :: Uniquenesses t
                -> GroundVars genv t
                -> PartialSchedule kernel genv t

  -- When both branches use the same buffer variables, the first
  -- branch first gets access to it and can release it (using OutputRelease)
  -- to the second branch.
  -- The ordering in this constructor is thus not symmetric (as opposed to Fork
  -- in UniformSchedule, as the dependency is made explicit there by the use of
  -- signals).
  -- When the left branch has a OutputRelease matching with a InputAcquire from
  -- the second branch (or other matching signals), a new signal will be bound
  -- here.
  -- Note that whereas 'BufferSignals genv' could be derived from the two branches,
  -- it is stored here to avoid recomputing it multiple times, which should mean
  -- that we only compute buffer signals O(n) times instead of O(n^2), in terms of
  -- the number of nodes of the AST.
  -- We also try to reuse signal and ref variables for variables which are later
  -- on returned. We can reuse their signal and ref variables instead of introducing
  -- new ones. Note that, in case of a buffer, we still need to introduce an additional
  -- signal, which should be resolved when all operations on the buffer in the bound
  -- computation are resolved.
  --
  PartialDeclare
                :: SyncEnv genv
                -> GLeftHandSide bnd genv genv'
                -> TupR (Destination t) bnd
                -> Uniquenesses bnd
                -> PartialSchedule kernel genv  bnd
                -> PartialSchedule kernel genv' t
                -> PartialSchedule kernel genv  t

  PartialAcond  :: SyncEnv genv -- Stored for efficiency reasons to avoid recomputing it.
                -> ExpVar genv PrimBool
                -> PartialSchedule kernel genv t
                -> PartialSchedule kernel genv t
                -> PartialSchedule kernel genv t

  PartialAwhile :: SyncEnv genv
                -> Uniquenesses t
                -> PartialScheduleFun kernel genv (t -> PrimBool)
                -> PartialScheduleFun kernel genv (t -> t)
                -> GroundVars genv t
                -> PartialSchedule kernel genv t

partialDeclare  :: GLeftHandSide bnd genv genv'
                -> TupR (Destination t) bnd
                -> Uniquenesses bnd
                -> PartialSchedule kernel genv  bnd
                -> PartialSchedule kernel genv' t
                -> PartialSchedule kernel genv  t
partialDeclare lhs dest us bnd sched = PartialDeclare sync lhs dest us bnd sched
  where
    sync = unionPartialEnv max (syncEnv bnd) (weakenSyncEnv lhs $ syncEnv sched)

partialAcond    :: ExpVar genv PrimBool
                -> PartialSchedule kernel genv t
                -> PartialSchedule kernel genv t
                -> PartialSchedule kernel genv t
partialAcond cond t f = PartialAcond sync cond t f
  where
    sync = unionPartialEnv max (syncEnv t) (syncEnv f)

partialAwhile   :: Uniquenesses t
                -> PartialScheduleFun kernel genv (t -> PrimBool)
                -> PartialScheduleFun kernel genv (t -> t)
                -> GroundVars genv t
                -> PartialSchedule kernel genv t
partialAwhile us cond f vars = PartialAwhile sync us cond f vars
  where
    sync = unionPartialEnv max (syncEnvFun cond) $ unionPartialEnv max (syncEnvFun f) $ variablesToSyncEnv us vars

data PartialScheduleFun kernel genv t where
  Plam  :: GLeftHandSide s genv genv'
        -> PartialScheduleFun kernel genv' t
        -> PartialScheduleFun kernel genv (s -> t)

  Pbody :: PartialSchedule    kernel genv  t
        -> PartialScheduleFun kernel genv  t

instance HasGroundsR (PartialSchedule kernel genv) where
  groundsR (PartialDo doOutput _ _) = partialDoOutputGroundsR doOutput
  groundsR (PartialReturn _ vars) = mapTupR varType vars
  groundsR (PartialDeclare _ _ _ _ _ p) = groundsR p
  groundsR (PartialAcond _ _ p _) = groundsR p
  groundsR (PartialAwhile _ _ _ _ vars) = groundsR vars

-- We can only reuse the resulting address of a variable if the local binding is not used elsewhere.
-- For instance, we may reuse the return address for x in `let x = .. in x`,
-- but that is not allowed in `let x = .. in let y = .. x .. in (x, y)`
-- or `let x = .. in (x, x)`.
-- This function removes a set of variables and can be used to remove for instance the set of variables
-- used in another binding or effect.
removeMaybeVars :: forall genv u. MaybeVars GroundR genv u -> IdxSet genv -> MaybeVars GroundR genv u
removeMaybeVars vars remove = mapTupR f vars
  where
    f :: MaybeVar GroundR genv t -> MaybeVar GroundR genv t
    f var@(JustVar (Var _ idx))
      | idx `IdxSet.member` remove = NoVar
      | otherwise         = var
    f NoVar = NoVar

lhsDestination :: GLeftHandSide t genv genv' -> MaybeVars GroundR genv' u -> TupR (Destination u) t
lhsDestination (LeftHandSidePair l1 l2) vars = lhsDestination l1 (strengthenMaybeVars l2 vars) `TupRpair` lhsDestination l2 vars
lhsDestination (LeftHandSideWildcard t) _    = mapTupR (const DestinationNew) t
lhsDestination (LeftHandSideSingle _)   vars = case findVar vars of
    Just ix -> TupRsingle $ DestinationReuse ix
    Nothing -> TupRsingle DestinationNew
  where
    findVar :: MaybeVars GroundR (env, t) s -> Maybe (TupleIdx s t)
    findVar (TupRpair a b) = case (findVar a, findVar b) of
      (Just i , _     ) -> Just $ TupleIdxLeft i
      (Nothing, Just i) -> Just $ TupleIdxRight i
      _                 -> Nothing
    findVar (TupRsingle (JustVar (Var _ ZeroIdx))) = Just TupleIdxSelf
    findVar _ = Nothing

joinVars :: MaybeVars GroundR genv t -> MaybeVars GroundR genv t -> MaybeVars GroundR genv t
joinVars m@(TupRsingle (JustVar (Var _ x))) (TupRsingle (JustVar (Var _ y)))
  | x == y = m
joinVars (TupRpair x1 x2) (TupRpair y1 y2) = joinVars x1 y1 `TupRpair` joinVars x2 y2
joinVars TupRunit         _                = TupRunit
joinVars _                TupRunit         = TupRunit
joinVars _                _                = TupRsingle NoVar

data Exists' (a :: (Type -> Type -> Type) -> Type) where
  Exists' :: a m -> Exists' a

partialSchedule :: forall kernel genv1 t1. IsKernel kernel => C.PartitionedAcc (KernelOperation kernel) genv1 t1 -> (PartialSchedule kernel genv1 t1, IdxSet genv1)
partialSchedule = (\(s, used, _) -> (s, used)) . travA (TupRsingle Shared)
  where
    travA :: forall genv t. Uniquenesses t -> C.PartitionedAcc (KernelOperation kernel) genv t -> (PartialSchedule kernel genv t, IdxSet genv, MaybeVars GroundR genv t)
    travA _  (C.Exec op args)
      | Exists env <- convertEnvFromList $ map (foldr1 combineMod') $ groupBy (\(Exists v1) (Exists v2) -> isJust $ matchIdx (varIdx v1) (varIdx v2)) $ argsVars args -- TODO: Remove duplicates more efficiently
      , Reads reEnv k inputBindings <- readRefs $ convertEnvRefs env
      , Just args' <- reindexArgs (reEnvIdx' reEnv) args
      , CompiledKernel kernel sargs <- compileKernel' op args'
        = let
            signals = convertEnvSignals env
            resolvers = convertEnvSignalResolvers k env

          in
            ( PartialDo PartialDoOutputUnit env
                $ await signals
                $ inputBindings
                $ Effect (Exec (kernelMetadata kernel) kernel sargs)
                $ resolve resolvers
                  Return
            , IdxSet.fromList $ convertEnvToList env
            , TupRunit
            )
      | otherwise = error "partialSchedule: reindexArgs returned Nothing. Probably some variable is missing in 'execVars'"
      where
        combineMod' :: Exists (Var AccessGroundR env) -> Exists (Var AccessGroundR env) -> Exists (Var AccessGroundR env)
        combineMod' (Exists (Var (AccessGroundRbuffer m1 tp) ix)) var@(Exists (Var (AccessGroundRbuffer m2 _) _))
          | Exists' m <- combineMod m1 m2 = Exists $ Var (AccessGroundRbuffer m tp) ix
          | otherwise = var
        combineMod' a _ = a -- Nothing has to be done when combining two scalars; they don't have access modifiers

    travA us (C.Return vars)  = (PartialReturn us vars, IdxSet.fromVarList $ flattenTupR vars, mapTupR f vars)
      where
        duplicates = map head $ filter (\g -> length g >= 2) $ group $ sort $ map (\(Exists (Var _ ix)) -> idxToInt ix) $ flattenTupR vars

        f :: GroundVar genv t' -> MaybeVar GroundR genv t'
        f v@(Var _ idx)
          | idxToInt idx `elem` duplicates = NoVar
          | otherwise = JustVar v
    travA _  (C.Compute e)    = partialLift (mapTupR GroundRscalar $ expType e) f (expGroundVars e)
      where
        f :: genv :?> fenv -> Maybe (Binding fenv t)
        f k = Compute <$> strengthenArrayInstr k e
    travA us (C.Alet lhs us' bnd a) = (partialDeclare lhs dest us' bnd' a', used, vars')
      where
        dest = lhsDestination lhs vars
        used = used1 `IdxSet.union` IdxSet.drop' lhs used2
        (bnd', used1, _) = travA us' bnd
        (a', used2, vars) = travA us a
        vars' = strengthenMaybeVars lhs vars `removeMaybeVars` used
    travA _  (C.Alloc shr tp sh) = partialLift1 (TupRsingle $ GroundRbuffer tp) (Alloc shr tp) sh
    travA _  (C.Use tp n buffer) = partialLift1 (TupRsingle $ GroundRbuffer tp) (const $ Use tp n buffer) TupRunit
    travA _  (C.Unit var@(Var tp _)) = partialLift1 (TupRsingle $ GroundRbuffer tp) f (TupRsingle var)
      where
        f (TupRsingle var') = Unit var'
        f TupRunit          = internalError "Unit scalar type impossible"
        f TupRpair{}        = internalError "Pair scalar type impossible"
    travA us (C.Acond c t f) = (partialAcond c t' f', IdxSet.union used1 used2, vars)
      where
        (t', used1, vars1) = travA us t
        (f', used2, vars2) = travA us f
        vars = joinVars vars1 vars2
    travA _  (C.Awhile us c f vars) = (partialAwhile us c' f' vars, used1 `IdxSet.union` used2 `IdxSet.union` IdxSet.fromVarList (flattenTupR vars), TupRsingle NoVar)
      where
        (c', used1) = partialScheduleFun c
        (f', used2) = partialScheduleFun f

partialScheduleFun :: IsKernel kernel => C.PartitionedAfun (KernelOperation kernel) genv t -> (PartialScheduleFun kernel genv t, IdxSet genv)
partialScheduleFun (C.Alam lhs f) = (Plam lhs f', IdxSet.drop' lhs used)
  where
    (f', used) = partialScheduleFun f
partialScheduleFun (C.Abody b)    = (Pbody b', used)
  where
    (b', used) = partialSchedule b

partialLift1 :: GroundsR s -> (forall fenv. ExpVars fenv t -> Binding fenv s) -> ExpVars genv t -> (PartialSchedule kernel genv s, IdxSet genv, MaybeVars GroundR genv s)
partialLift1 tp f vars = partialLift tp (\k -> f <$> strengthenVars k vars) (expVarsList vars)

expVarsList :: ExpVars genv t -> [Exists (GroundVar genv)]
expVarsList = (`go` [])
  where
    go :: ExpVars genv t -> [Exists (GroundVar genv)] -> [Exists (GroundVar genv)]
    go TupRunit                 accum = accum
    go (TupRsingle (Var tp ix)) accum = Exists (Var (GroundRscalar tp) ix) : accum
    go (TupRpair v1 v2)         accum = go v1 $ go v2 accum

strengthenVars :: genv :?> fenv -> Vars s genv t -> Maybe (Vars s fenv t)
strengthenVars _ TupRunit                = pure TupRunit
strengthenVars k (TupRsingle (Var t ix)) = TupRsingle . Var t <$> k ix
strengthenVars k (TupRpair v1 v2)        = TupRpair <$> strengthenVars k v1 <*> strengthenVars k v2

partialLift :: forall kernel genv s. GroundsR s -> (forall fenv. genv :?> fenv -> Maybe (Binding fenv s)) -> [Exists (GroundVar genv)] -> (PartialSchedule kernel genv s, IdxSet genv, MaybeVars GroundR genv s)
partialLift tp f vars
  | DefineOutput doOutput _ varsOut <- defineOutput @() @s tp $ unique tp
  , Exists env <- convertEnvReadonlyFromList $ nubBy (\(Exists v1) (Exists v2) -> isJust $ matchVar v1 v2) vars -- TODO: Remove duplicates more efficiently
  , Reads reEnv k inputBindings <- readRefs $ convertEnvRefs env
  , DeclareVars lhs k' value <- declareVars $ mapTupR BaseRground tp
  , Just binding <- f (reEnvIdx' reEnv)
  =
    let
      signals = convertEnvSignals env
      resolvers = convertEnvSignalResolvers (k' .> k) env
    in
      ( PartialDo doOutput env
          $ await signals
          $ inputBindings
          $ Alet lhs binding
          $ resolve resolvers
          $ writeOutput doOutput (varsOut (k' .> k .> convertEnvWeaken env)) (value weakenId)
      , IdxSet.fromList $ convertEnvToList env
      , mapTupR (const NoVar) tp
      )
partialLift _ _ _ = internalError "PartialLift failed. Was the list of used variables missing some variable?"

combineMod :: Modifier m -> Modifier m' -> Exists' Modifier
combineMod In  In  = Exists' In
combineMod Out Out = Exists' Out
combineMod _   _   = Exists' Mut

combineAccessGroundR :: AccessGroundR t -> AccessGroundR t -> AccessGroundR t
combineAccessGroundR (AccessGroundRbuffer m1 tp) (AccessGroundRbuffer m2 _)
  | Exists' m <- combineMod m1 m2 = AccessGroundRbuffer m tp
combineAccessGroundR a _ = a -- Nothing has to be done when combining two scalars; they don't have access modifiers

data CompiledKernel kenv fenv kernel where
  CompiledKernel :: OpenKernelFun kernel kenv f
                 -> SArgs fenv f
                 -> CompiledKernel kenv fenv kernel

compileKernel'
  :: forall fenv kernel args.
     IsKernel kernel
  => Cluster (KernelOperation kernel) args
  -> Args fenv args
  -> CompiledKernel () fenv kernel
compileKernel' cluster args =
  go
    (partialEnvFromList combineAccessGroundR (map (\(Exists (Var tp ix)) -> EnvBinding ix tp) vars))
    weakenId
    Empty
    (\ _ x -> x)
  where
    vars = argsVars args

    go
      :: forall fenv1 kenv.
         PartialEnv AccessGroundR fenv1
      -> (fenv1 :> fenv)
      -> Env AccessGroundR kenv
      -> (forall kenv'. kenv :> kenv' -> PartialEnv (Idx kenv') fenv1 -> PartialEnv (Idx kenv') fenv)
      -> CompiledKernel kenv fenv kernel
    go PEnd _  kenv kSubst =
      CompiledKernel
        (KernelFunBody $ compileKernel kenv cluster args')
        ArgsNil
      where
        kSubst' = kSubst weakenId PEnd
        Identity args' = reindexArgs prjIdx args
        prjIdx :: forall a. Idx fenv a -> Identity (Idx kenv a)
        prjIdx idx = case prjPartial idx kSubst' of
          Nothing -> internalError "Variable not found in environment. The environment was probably built incorrectly, argsVars may have missed this variable?"
          Just idx' -> Identity idx'
    go (PPush env a@(AccessGroundRscalar tp)) k1 kenv kSubstF
      | CompiledKernel kernel sargs <- go env (weakenSucc k1) (kenv `Push` a) (\k2 kSubst -> kSubstF (weakenSucc k2) $ PPush kSubst (k2 >:> ZeroIdx))
      = CompiledKernel (KernelFunLam (KernelArgRscalar tp) kernel) (SArgScalar (Var tp $ k1 >:> ZeroIdx) :>: sargs)
    go (PPush env a@(AccessGroundRbuffer mod' tp)) k1 kenv kSubstF
      | CompiledKernel kernel sargs <- go env (weakenSucc k1) (kenv `Push` a) (\k2 kSubst -> kSubstF (weakenSucc k2) $ PPush kSubst (k2 >:> ZeroIdx))
      = CompiledKernel (KernelFunLam (KernelArgRbuffer mod' tp) kernel) (SArgBuffer mod' (Var (GroundRbuffer tp) $ k1 >:> ZeroIdx) :>: sargs)
    go (PNone env) k1 kenv kSubstF
      = go env (weakenSucc k1) kenv (\k2 kSubst -> kSubstF k2 $ PNone kSubst)

syncEnv :: PartialSchedule kernel genv t -> SyncEnv genv
syncEnv (PartialDo _ env _)          = convertEnvToSyncEnv env
syncEnv (PartialReturn u vars)       = variablesToSyncEnv u vars
syncEnv (PartialDeclare s _ _ _ _ _) = s
syncEnv (PartialAcond s _ _ _)       = s
syncEnv (PartialAwhile s _ _ _ _)    = s

syncEnvFun :: PartialScheduleFun kernel genv t -> SyncEnv genv
syncEnvFun (Plam lhs f) = weakenSyncEnv lhs $ syncEnvFun f
syncEnvFun (Pbody s)    = syncEnv s

convertEnvToSyncEnv :: ConvertEnv genv fenv fenv' -> SyncEnv genv
convertEnvToSyncEnv = partialEnvFromList max . (`go` [])
  where
    go :: ConvertEnv genv fenv fenv' -> [EnvBinding Sync genv] -> [EnvBinding Sync genv]
    go (ConvertEnvSeq env1 env2)                  accum = go env1 $ go env2 accum
    go (ConvertEnvAcquire (Acquire m (Var _ ix))) accum = EnvBinding ix s : accum
      where
        s = case m of
          In -> SyncRead
          _  -> SyncWrite
    go _ accum = accum

variablesToSyncEnv :: Uniquenesses t -> GroundVars genv t -> SyncEnv genv
variablesToSyncEnv uniquenesses vars = partialEnvFromList combine $ go uniquenesses vars []
  where
    go :: Uniquenesses t -> GroundVars genv t -> [EnvBinding Sync genv] -> [EnvBinding Sync genv]
    go (TupRsingle Unique) (TupRsingle (Var (GroundRbuffer _) ix))
                          accum = EnvBinding ix SyncWrite : accum
    go (TupRsingle Shared) (TupRsingle (Var (GroundRbuffer _) ix))
                          accum = EnvBinding ix SyncRead : accum
    go u (TupRpair v1 v2) accum = go u1 v1 $ go u2 v2 accum
      where (u1, u2) = pairUniqueness u
    go _ _                accum = accum

    combine :: Sync s -> Sync s -> Sync s
    combine SyncRead SyncRead = SyncRead
    combine _        _        = internalError "A writable buffer cannot be aliassed"

pairUniqueness :: Uniquenesses (s, t) -> (Uniquenesses s, Uniquenesses t)
pairUniqueness (TupRpair u1 u2)    = (u1, u2)
pairUniqueness (TupRsingle Shared) = (TupRsingle Shared, TupRsingle Shared)

weakenSyncEnv :: GLeftHandSide t env env' -> SyncEnv env' -> SyncEnv env
weakenSyncEnv _                        PEnd          = PEnd
weakenSyncEnv (LeftHandSideWildcard _) env           = env
weakenSyncEnv (LeftHandSideSingle _)   (PPush env _) = env
weakenSyncEnv (LeftHandSideSingle _)   (PNone env)   = env
weakenSyncEnv (LeftHandSidePair l1 l2) env           = weakenSyncEnv l1 $ weakenSyncEnv l2 env

data Lock fenv
  = Borrow (Idx fenv Signal) (Idx fenv SignalResolver)
  | Move (Idx fenv Signal)

lockSignal :: Lock fenv -> Idx fenv Signal
lockSignal (Borrow s _) = s
lockSignal (Move s) = s

setLockSignal :: Idx fenv Signal -> Lock fenv -> Lock fenv
setLockSignal s (Borrow _ r) = Borrow s r
setLockSignal s (Move _)     = Move s

data Future fenv t where
  FutureScalar :: ScalarType t
               -> Idx fenv Signal
               -> Idx fenv (Ref t)
               -> Future fenv t

  -- A buffer has a signal to denote that the Ref may be read,
  -- and signals and resolvers grouped in Locks to synchronize
  -- read and write access to the buffer.
  -- Informal properties / invariants:
  --  - If the read signal is resolved, then we may read from
  --    the array.
  --  - If the signals of the read and write access are both
  --    resolved, then we may destructively update the array.
  --  - The read resolver may only be resolved after the read
  --    signal is resolved.
  --  - The write resolver may only be resolved after both
  --    the read and write signals are resolved.
  FutureBuffer :: ScalarType t
               -> Idx fenv Signal -- This signal is resolved when the Ref is filled.
               -> Idx fenv (Ref (Buffer t))
               -> Lock fenv -- Read access
               -> Maybe (Lock fenv) -- Write access, if needed
               -> Future fenv (Buffer t)

  FutureNoRef :: GroundR t
              -> Idx fenv t
              -> Future fenv t

type FutureEnv fenv = PartialEnv (Future fenv)

instance Sink' Lock where
  weaken' k (Borrow s r) = Borrow (weaken k s) (weaken k r)
  weaken' k (Move s)     = Move (weaken k s)

instance Sink Future where
  weaken k (FutureScalar tp signal ref) = FutureScalar tp (weaken k signal) (weaken k ref)
  weaken k (FutureBuffer tp signal ref read write)
    = FutureBuffer
        tp
        (weaken k signal)
        (weaken k ref)
        (weaken' k read)
        (weaken' k <$> write)
  weaken k (FutureNoRef tp ix) = FutureNoRef tp (weaken k ix)

-- Implementation of the sub-environment rule, by restricting the futures
-- in the FutureEnv to the abilities required by the SyncEnv.
-- Creates a sub-environment, providing only the futures needed in some subterm.
-- Also returns a list of locks which are not used in this sub-environment
-- (because the buffer is not used in that sub-term, or the sub-term doesn't require
-- write access for that buffer). Those locks should be resolved, ie, we should fork
-- a thread, wait on the signal and resolve the resolver, such that later operations
-- can get access to the resource.
--
subFutureEnvironment :: forall fenv genv kernel. FutureEnv fenv genv -> SyncEnv genv -> (FutureEnv fenv genv, [UniformSchedule kernel fenv])
subFutureEnvironment (PNone fenv) (PNone senv) = (PNone fenv', actions)
  where
    (fenv', actions) = subFutureEnvironment fenv senv
subFutureEnvironment (PNone fenv) PEnd = (PNone fenv', actions)
  where
    (fenv', actions) = subFutureEnvironment fenv PEnd
subFutureEnvironment PEnd (PNone senv) = (PNone fenv', actions)
  where
    (fenv', actions) = subFutureEnvironment PEnd senv
subFutureEnvironment PEnd _ = (PEnd, [])
subFutureEnvironment (PPush fenv f@FutureScalar{}) senv = (PPush fenv' f, actions)
  where
    (fenv', actions) = subFutureEnvironment fenv $ partialEnvTail senv
subFutureEnvironment (PPush fenv f@FutureNoRef{}) senv = (PPush fenv' f, actions)
  where
    (fenv', actions) = subFutureEnvironment fenv $ partialEnvTail senv
subFutureEnvironment (PPush fenv f@(FutureBuffer tp signal ref read write)) (PPush senv sync) = (PPush fenv' f', action ++ actions)
  where
    (fenv', actions) = subFutureEnvironment fenv senv

    (f', action)
      | Nothing <- write,             SyncRead  <- sync -- No need to change
        = (f, [])
      | Just _ <- write,              SyncWrite <- sync -- No need to change
        = (f, [])
      | Nothing <- write,             SyncWrite <- sync -- Illegal input
        = internalError "Got a FutureBuffer without write capabilities, but the SyncEnv asks for write permissions"
      | Just (Borrow ws wr) <- write, SyncRead  <- sync -- Write capability not used
        = ( FutureBuffer tp signal ref read write
          -- Resolve the write resolver after taking both the read and write signal
          , [Effect (SignalAwait [lockSignal read, ws]) $ Effect (SignalResolve [wr]) Return]
          )
      | Just (Move _) <- write,       SyncRead  <- sync
        = ( FutureBuffer tp signal ref read Nothing
          , []
          )
subFutureEnvironment (PPush fenv (FutureBuffer _ _ _ read write)) (PNone senv) = (PNone fenv', action ++ actions)
  where
    (fenv', actions) = subFutureEnvironment fenv senv

    action
      | Borrow rs rr <- read
      , Just (Borrow ws wr) <- write
        = return
        $ Effect (SignalResolve [rr])
        $ Effect (SignalAwait [rs, ws])
        $ Effect (SignalResolve [wr]) Return
      | Move rs <- read
      , Just (Borrow ws wr) <- write
        = return
        $ Effect (SignalAwait [rs, ws])
        $ Effect (SignalResolve [wr]) Return
      | Borrow _ rr <- read
        = return
        $ Effect (SignalResolve [rr]) Return
      | otherwise = []
subFutureEnvironment _ (PPush _ _) = internalError "Keys of SyncEnv are not a subset of the keys of the FutureEnv"
subFutureEnvironment fenv@(PPush _ _) PEnd = subFutureEnvironment fenv (PNone PEnd)

sub :: forall fenv genv kernel. FutureEnv fenv genv -> SyncEnv genv -> (FutureEnv fenv genv -> UniformSchedule kernel fenv) -> UniformSchedule kernel fenv
sub fenv senv body = forks (body fenv' : actions)
  where
    (fenv', actions) = subFutureEnvironment fenv senv

-- Data type for the existentially qualified type variable fenv' used in chainFuture
data ChainFutureEnv kernel fenv genv where
  ChainFutureEnv :: (UniformSchedule kernel fenv' -> UniformSchedule kernel fenv) -> fenv :> fenv' -> FutureEnv fenv' genv -> FutureEnv fenv' genv -> ChainFutureEnv kernel fenv genv

chainFutureEnvironment :: fenv :> fenv' -> FutureEnv fenv genv -> SyncEnv genv -> SyncEnv genv -> ChainFutureEnv kernel fenv' genv
chainFutureEnvironment _ PEnd PEnd PEnd = ChainFutureEnv id weakenId PEnd PEnd
chainFutureEnvironment k (PPush fenv f@FutureScalar{}) senvLeft senvRight
  | ChainFutureEnv instr k1 fenvLeft fenvRight <- chainFutureEnvironment k fenv (partialEnvTail senvLeft) (partialEnvTail senvRight)
  = ChainFutureEnv instr k1 (PPush fenvLeft $ weaken (k1 .> k) f) (PPush fenvRight $ weaken (k1 .> k) f)
chainFutureEnvironment k (PPush fenv f@FutureNoRef{}) senvLeft senvRight
  | ChainFutureEnv instr k1 fenvLeft fenvRight <- chainFutureEnvironment k fenv (partialEnvTail senvLeft) (partialEnvTail senvRight)
  = ChainFutureEnv instr k1 (PPush fenvLeft $ weaken (k1 .> k) f) (PPush fenvRight $ weaken (k1 .> k) f)
-- Used in both subterms
chainFutureEnvironment k (PPush fenv f) (PPush senvLeft sLeft) (PPush senvRight sRight)
  | ChainFuture    instr1 k1 fLeft    fRight    <- chainFuture (weaken k f) sLeft sRight
  , ChainFutureEnv instr2 k2 fenvLeft fenvRight <- chainFutureEnvironment (k1 .> k) fenv senvLeft senvRight
  = ChainFutureEnv
      (instr1 . instr2)
      (k2 .> k1)
      (PPush fenvLeft  $ weaken k2 fLeft)
      (PPush fenvRight $ weaken k2 fRight)
-- Only used in left subterm
chainFutureEnvironment k (PPush fenv f) (PPush senvLeft _) senvRight
  | ChainFutureEnv instr k1 fenvLeft fenvRight <- chainFutureEnvironment k fenv senvLeft (partialEnvTail senvRight)
  = ChainFutureEnv instr k1 (PPush fenvLeft $ weaken (k1 .> k) f) (partialEnvSkip fenvRight)
-- Only used in right subterm
chainFutureEnvironment k (PPush fenv f) senvLeft (PPush senvRight _)
  | ChainFutureEnv instr k1 fenvLeft fenvRight <- chainFutureEnvironment k fenv (partialEnvTail senvLeft) senvRight
  = ChainFutureEnv instr k1 (partialEnvSkip fenvLeft) (PPush fenvRight $ weaken (k1 .> k) f)
-- Index not present
chainFutureEnvironment k (PNone fenv) senvLeft senvRight
  | ChainFutureEnv instr k1 fenvLeft fenvRight <- chainFutureEnvironment k fenv (partialEnvTail senvLeft) (partialEnvTail senvRight)
  = ChainFutureEnv instr k1 (partialEnvSkip fenvLeft) (partialEnvSkip fenvRight)
chainFutureEnvironment _ _ _ _ = internalError "Illegal case. The keys of the FutureEnv should be the union of the keys of the two SyncEnvs."

-- Data type for the existentially qualified type variable fenv' used in chainFuture
data ChainFuture kernel fenv t where
  ChainFuture :: (UniformSchedule kernel fenv' -> UniformSchedule kernel fenv) -> fenv :> fenv' -> Future fenv' t -> Future fenv' t -> ChainFuture kernel fenv t

chainFuture :: Future fenv t -> Sync t -> Sync t -> ChainFuture kernel fenv t
chainFuture (FutureScalar tp _ _) SyncRead  _ = bufferImpossible tp
chainFuture (FutureScalar tp _ _) SyncWrite _ = bufferImpossible tp

-- Read before read, without a release
--          Left     Right
-- Read  --> X      -> X
--        \       /
--          -----
chainFuture f@(FutureBuffer _ _ _ (Move _) mwrite) SyncRead SyncRead
  | Just _ <- mwrite = internalError "Expected a FutureBuffer without write lock"
  | Nothing <- mwrite
  = ChainFuture
      -- This doesn't require any additional signals
      id
      weakenId
      f
      f

-- Read before read
--          Left     Right
--               -------
--             /         \
-- Read  --> X      -> X -->
--        \       /
--          -----
chainFuture (FutureBuffer tp signal ref (Borrow s r) mwrite) SyncRead SyncRead
  | Just _ <- mwrite = internalError "Expected a FutureBuffer without write lock"
  | Nothing <- mwrite
  = ChainFuture
      -- Create a pair of signal and resolver for both subterms.
      -- Fork a thread which will resolve the final read signal when the two
      -- new signals have been resolved.
      ( Alet lhsSignal NewSignal
        . Alet lhsSignal NewSignal
        . Fork (Effect (SignalAwait [signal1, signal2]) $ Effect (SignalResolve [weaken k r]) Return)
      )
      -- Weaken all other identifiers with four, as we introduced two new signals
      -- and two new signal resolvers.
      k
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (Borrow (weaken k s) resolver1)
          Nothing
      )
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (Borrow (weaken k s) resolver2)
          Nothing
      )
  where
    k = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId

    signal1   = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    resolver1 =           SuccIdx $ SuccIdx ZeroIdx
    signal2   =                     SuccIdx ZeroIdx
    resolver2 =                             ZeroIdx

-- Write before read, without release
--          Left     Right
-- Read  --> X       > X
--                 /
--               /
--             /
-- Write --> X
--
-- Note that the left subterm must synchronise its read and write operations itself.
chainFuture (FutureBuffer tp signal ref (Move readSignal) (Just (Move writeSignal))) SyncWrite SyncRead
  = ChainFuture
      -- Create a signal to let the read operation in the second subterm only
      -- start after the write operation of the first subterm has finished.
      ( Alet lhsSignal NewSignal )
      k
      -- The first subterm must resolve the new signal after finishing its write operation.
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (Move $ weaken k readSignal)
          (Just $ Borrow (weaken k writeSignal) writeResolver)
      )
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (Move writeSignal2)
          Nothing
      )
  where
    k = weakenSucc $ weakenSucc weakenId
    writeSignal2  = SuccIdx ZeroIdx
    writeResolver = ZeroIdx

-- Write before read
--          Left     Right
--               -------
--             /         \
-- Read  --> X       > X -->
--                 /
--               /
--             /
-- Write --> X ------------->
-- Note that the left subterm must synchronise its read and write operations itself.
chainFuture (FutureBuffer tp signal ref (Borrow readSignal readRelease) (Just (Borrow writeSignal writeRelease))) SyncWrite SyncRead
  = ChainFuture
      -- Create a signal (signal1) to let the read operation in the second subterm only
      -- start after the write operation of the first subterm has finished.
      -- Also create signals (signal2 and signal3) to denote that the read operations
      -- of respectively the left and right subterm have finished.
      -- 'readRelease' will be resolved when signal2 and signal3 are both resolved.
      -- 'writeRelease' will be resolved when signal1 is resolved.
      ( Alet lhsSignal NewSignal
        . Alet lhsSignal NewSignal
        . Alet lhsSignal NewSignal
        . Fork (Effect (SignalAwait [signal2, signal3]) $ Effect (SignalResolve [weaken k readRelease]) Return)
        . Fork (Effect (SignalAwait [signal1]) $ Effect (SignalResolve [weaken k writeRelease]) Return)
      )
      k
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (Borrow (weaken k readSignal) resolver2)
          (Just $ Borrow (weaken k writeSignal) resolver1)
      )
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (Borrow signal1 resolver3)
          Nothing
      )
  where
    k = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId

    signal1   = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    resolver1 =           SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    signal2   =                     SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    resolver2 =                               SuccIdx $ SuccIdx ZeroIdx
    signal3   =                                         SuccIdx ZeroIdx
    resolver3 =                                                 ZeroIdx

-- Write before read, with a write release
--          Left     Right
-- Read  --> X       > X
--                 /
--               /
--             /
-- Write --> X ------------->
-- Note that the left subterm must synchronise its read and write operations itself.
chainFuture (FutureBuffer tp signal ref (Move readSignal) (Just (Borrow writeSignal writeRelease))) SyncWrite SyncRead
  = ChainFuture
      -- Create a signal to let the read operation in the second subterm only
      -- start after the write operation of the first subterm has finished.
      -- 'writeSignal' can be resolved when this newly introduced signal
      -- is resolved.
      ( Alet lhsSignal NewSignal
        . Fork (Effect (SignalAwait [signal1]) $ Effect (SignalResolve [weaken k writeRelease]) Return)
      )
      -- Weaken all other identifiers with two, as we introduced a new signal
      -- and a new signal resolver
      k
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (Move (weaken k readSignal))
          (Just $ Borrow (weaken k writeSignal) resolver1)
      )
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (Move signal1)
          Nothing
      )
  where
    k = weakenSucc $ weakenSucc weakenId
    signal1   = SuccIdx ZeroIdx
    resolver1 = ZeroIdx

-- Invalid cases of write-before-read
chainFuture (FutureBuffer _ _ _ _ Nothing) SyncWrite SyncRead = internalError "Expected a FutureBuffer with write lock"
chainFuture (FutureBuffer _ _ _ (Borrow _ _) (Just (Move _))) SyncWrite SyncRead = internalError "Illegal FutureBuffer with Borrow-Move locks"

-- Read before write
--          Left     Right
--          -----
--        /       \
-- Read  --> X      -> X -->
--             \
--               \
--                 \
-- Write ------------> X -->
chainFuture (FutureBuffer tp signal ref read mwrite) SyncRead SyncWrite
  | Nothing <- mwrite = internalError "Expected a FutureBuffer with write lock"
  | Just write <- mwrite
  = ChainFuture
      -- Create a signal to let the write operation in the second subterm only
      -- start after the read operation of the first subterm has finished.
      -- Also create a signal which will be resolved when the newly introduced signal
      -- and the incoming write signal are both resolved.
      ( Alet lhsSignal NewSignal
        . Alet lhsSignal NewSignal
        . Fork (Effect (SignalAwait [weaken k $ lockSignal write, signal1]) $ Effect (SignalResolve [resolver2]) Return)
      )
      -- Weaken all other identifiers with four, as we introduced two new signals
      -- and two new signal resolvers.
      k
      -- The first subterm must resolve the new signal after finishing its read operation.
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (Borrow (weaken k $ lockSignal read) resolver1)
          Nothing
      )
      -- The second subterm must wait on the signal before it can start the write operation.
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (weaken' k read)
          (Just $ setLockSignal signal2 $ weaken' k write)
      )
  where
    k = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId

    signal1   = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    resolver1 =           SuccIdx $ SuccIdx ZeroIdx
    signal2   =                     SuccIdx ZeroIdx
    resolver2 =                             ZeroIdx

-- Write before write
--          Left     Right
-- Read  --> X       > X -->
--             \   /
--               X
--             /   \
-- Write --> X       > X -->
chainFuture (FutureBuffer tp signal ref read mwrite) SyncWrite SyncWrite
  | Nothing <- mwrite = internalError "Expected a FutureBuffer with write lock"
  | Just write <- mwrite
  = ChainFuture
      -- Create two signals (signal1 and signal2) to let the first subterm
      -- inform that respectively its read or write operations have finished.
      ( Alet lhsSignal NewSignal
        . Alet lhsSignal NewSignal
      )
      k
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (Borrow (weaken k $ lockSignal read) resolver1)
          (Just $ Borrow (weaken k $ lockSignal write) resolver2)
      )
      ( FutureBuffer
          tp
          (weaken k signal)
          (weaken k ref)
          (setLockSignal signal2 $ weaken' k read)
          (Just $ setLockSignal signal1 $ weaken' k write)
      )
  where
    k = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId

    signal1   = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    resolver1 =           SuccIdx $ SuccIdx ZeroIdx
    signal2   =                     SuccIdx ZeroIdx
    resolver2 =                             ZeroIdx

-- Data type for the existentially qualified type variable fenv' used in loopFutureEnvironment
-- This is split in 3 data types, as we must introduce variables in the input arguments,
-- output arguments and in the body in local declarations.
-- LoopFutureEnv, LoopFutureEnvOutput and LoopFutureEnvBody are similar to
-- LoopFuture, LoopFutureOutput and LoopFutureBody but contain 
data LoopFutureEnv kernel fenv0 fenv1 genv where
  LoopFutureEnv
    :: InputOutputR input output
    -- Input
    -> fenv1 :> fenv2
    -> BLeftHandSide input fenv1 fenv2
    -> BaseVars fenv0 input -- Initial state
    -- Output
    -> (forall fenv3. fenv2 :> fenv3 -> LoopFutureEnvOutput kernel fenv3 genv output)
    -> LoopFutureEnv kernel fenv0 fenv1 genv

data LoopFutureEnvOutput kernel fenv3 genv output where
  LoopFutureEnvOutput
    :: fenv3 :> fenv4
    -> BLeftHandSide output fenv3 fenv4
    -> (forall fenv5. fenv4 :> fenv5 -> LoopFutureEnvBody kernel fenv5 genv)
    -> LoopFutureEnvOutput kernel fenv3 genv output

data LoopFutureEnvBody kernel fenv5 genv where
  LoopFutureEnvBody
    -- Instruction to declare new signals
    :: (UniformSchedule kernel fenv6 -> UniformSchedule kernel fenv5)
    -> fenv5 :> fenv6
    -> FutureEnv fenv6 genv
    -> FutureEnv fenv6 genv
    -> (forall fenv7. fenv6 :> fenv7 -> [UniformSchedule kernel fenv7]) -- Instructions to be called when the loop terminates
    -> LoopFutureEnvBody kernel fenv5 genv

futureEnvOuter :: GLeftHandSide s genv1 genv2 -> FutureEnv fenv genv2 -> FutureEnvOuter fenv genv1 genv2
futureEnvOuter (LeftHandSideWildcard _) env           = FutureEnvOuter env  $ flip const
futureEnvOuter (LeftHandSideSingle _)   (PPush env a) = FutureEnvOuter env  $ \k env' -> PPush env' $ weaken k a
futureEnvOuter (LeftHandSideSingle _)   (PNone env)   = FutureEnvOuter env  $ \_ env' -> partialEnvSkip env'
futureEnvOuter (LeftHandSideSingle _)   PEnd          = FutureEnvOuter PEnd $ \_ env' -> partialEnvSkip env'
futureEnvOuter (LeftHandSidePair l1 l2) env
  | FutureEnvOuter env2 f2 <- futureEnvOuter l2 env
  , FutureEnvOuter env1 f1 <- futureEnvOuter l1 env2
  = FutureEnvOuter env1 $ \k env' -> f2 k $ f1 k env'

data FutureEnvOuter fenv genv1 genv2 where
  FutureEnvOuter
    :: FutureEnv fenv genv1
    -> (forall fenv'. fenv :> fenv' -> FutureEnv fenv' genv1 -> FutureEnv fenv' genv2)
    -> FutureEnvOuter fenv genv1 genv2

loopFutureEnvironment :: Idx fenv Signal -> fenv :> fenv1 -> FutureEnv fenv genv -> SyncEnv genv -> SyncEnv genv -> LoopFutureEnv kernel fenv fenv1 genv
loopFutureEnvironment _ _ PEnd _ _
  = LoopFutureEnv
      InputOutputRunit
      weakenId
      (LeftHandSideWildcard TupRunit)
      TupRunit
      $ \_ ->
        LoopFutureEnvOutput
          weakenId
          (LeftHandSideWildcard TupRunit)
          $ \_ ->
            LoopFutureEnvBody
              id
              weakenId
              PEnd
              PEnd
              $ const []
loopFutureEnvironment resolved k (PPush fenv f) senvLeft senvRight
  | LoopFuture    ioA k12A lhsInputA initialA outputA <- loopFuture resolved k f (partialEnvLast senvLeft) (partialEnvLast senvRight)
  , LoopFutureEnv ioB k12B lhsInputB initialB outputB <- loopFutureEnvironment resolved (k12A .> k) fenv (partialEnvTail senvLeft) (partialEnvTail senvRight)
  = LoopFutureEnv
      (InputOutputRpair ioA ioB)
      (k12B .> k12A)
      (LeftHandSidePair lhsInputA lhsInputB)
      (TupRpair initialA initialB)
      $ \k23 ->
        if -- This is a 'multi-way' (or actually a single-way) if, to pattern match on LoopFuture{Env}Output
          | LoopFutureOutput    k34A lhsOutputA bodyA <- outputA (k23 .> k12B)
          , LoopFutureEnvOutput k34B lhsOutputB bodyB <- outputB (k34A .> k23)
          -> LoopFutureEnvOutput
              (k34B .> k34A)
              (LeftHandSidePair lhsOutputA lhsOutputB)
              $ \k45 ->
                if
                  | LoopFutureBody instrA k56A futureLeft futureRight releaseA <- bodyA (k45 .> k34B)
                  , LoopFutureEnvBody instrB k56B fenvLeft fenvRight releaseB <- bodyB (k56A .> k45)
                  -> LoopFutureEnvBody
                      (instrA . instrB)
                      (k56B .> k56A)
                      (partialEnvPush fenvLeft  (weaken k56B <$> futureLeft))
                      (partialEnvPush fenvRight (weaken k56B <$> futureRight))
                      $ \k67 ->
                          map (weaken' (k67 .> k56B)) releaseA
                          ++ releaseB k67
loopFutureEnvironment resolved k (PNone fenv) senvLeft senvRight
  | LoopFutureEnv io k12 lhsInput initial output <- loopFutureEnvironment resolved k fenv (partialEnvTail senvLeft) (partialEnvTail senvRight)
  = LoopFutureEnv
      io
      k12
      lhsInput
      initial
      $ \k23 ->
        if -- Again a multi-way if with only one alternative to pattern match on LoopFutureOutput
          | LoopFutureEnvOutput k34 lhsOutput body <- output k23
          -> LoopFutureEnvOutput
              k34
              lhsOutput
              $ \k45 ->
                if
                  | LoopFutureEnvBody instr k56 fenvLeft fenvRight release <- body k45
                  -> LoopFutureEnvBody instr k56 (partialEnvSkip fenvLeft) (partialEnvSkip fenvRight) release

-- Data type for the existentially qualified type variable fenv' used in loopFuture
-- This is split in 3 data types, as we must introduce variables in the input arguments,
-- output arguments and in the body in local declarations.
data LoopFuture kernel fenv0 fenv1 t where
  LoopFuture
    :: InputOutputR input output
    -- Input
    -> fenv1 :> fenv2
    -> BLeftHandSide input fenv1 fenv2
    -> BaseVars fenv0 input
    -- Output
    -> (forall fenv3. fenv2 :> fenv3 -> LoopFutureOutput kernel fenv3 t output)
    -> LoopFuture kernel fenv0 fenv1 t

data LoopFutureOutput kernel fenv3 t output where
  LoopFutureOutput
    :: fenv3 :> fenv4
    -> BLeftHandSide output fenv3 fenv4
    -> (forall fenv5. fenv4 :> fenv5 -> LoopFutureBody kernel fenv5 t)
    -> LoopFutureOutput kernel fenv3 t output

data LoopFutureBody kernel fenv5 t where
  LoopFutureBody
    -- Instruction to declare new signals
    :: (UniformSchedule kernel fenv6 -> UniformSchedule kernel fenv5)
    -> fenv5 :> fenv6
    -> Maybe (Future fenv6 t)
    -> Maybe (Future fenv6 t)
    -> [UniformSchedule kernel fenv6] -- Instruction to be called when the loop terminates
    -> LoopFutureBody kernel fenv5 t

loopFuture :: Idx fenv0 Signal -> fenv0 :> fenv1 -> Future fenv0 t -> Maybe (Sync t) -> Maybe (Sync t) -> LoopFuture kernel fenv0 fenv1 t
-- Illegal and impossible cases
loopFuture _ _ (FutureScalar tp _ _) (Just SyncRead)  _ = bufferImpossible tp
loopFuture _ _ (FutureScalar tp _ _) (Just SyncWrite) _ = bufferImpossible tp
loopFuture _ _ (FutureScalar tp _ _) _  (Just SyncRead) = bufferImpossible tp
loopFuture _ _ (FutureScalar tp _ _) _ (Just SyncWrite) = bufferImpossible tp

-- Cases with write permissions
loopFuture _ k01 (FutureBuffer tp signal ref readLock (Just writeLock)) (Just SyncWrite) (Just SyncWrite)
  -- "Write-before-write"
  -- We must add two signals (and accompanying signal resolvers) to the state
  -- to synchronize read and write access. Furthermore we need to declare two
  -- local signals in the body of the loop.
  -- Note that the next iteration gets read access when the current one
  -- finished writing, and the next iteration gets write access when this
  -- iteration has finished reading. This is similar to the write-before-write
  -- case in chainFuture.
  --
  = LoopFuture
      (InputOutputRpair InputOutputRsignal InputOutputRsignal)
      (weakenSucc $ weakenSucc weakenId)
      (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle BaseRsignal)
      (TupRsingle (Var BaseRsignal $ lockSignal readLock) `TupRpair` TupRsingle (Var BaseRsignal $ lockSignal writeLock))
      $ \k23 ->
        LoopFutureOutput
          (weakenSucc $ weakenSucc weakenId)
          (LeftHandSideSingle BaseRsignalResolver `LeftHandSidePair` LeftHandSideSingle BaseRsignalResolver)
          $ \k45 ->
            let
              instr =
                  Alet lhsSignal NewSignal -- Signal denotes whether the condition has finished reading the array
                . Alet lhsSignal NewSignal -- Signal denotes whether the condition has finished writing the array


              k56 = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId
              k46 = k56 .> k45
              k26 = k46 .> weakenSucc (weakenSucc weakenId) .> k23
              k = k26 .> weakenSucc (weakenSucc weakenId) .> k01

              -- Release at end of loop
              releaseRead = case readLock of
                Borrow _ resolver ->
                  [Effect (SignalAwait [SuccIdx ZeroIdx]) $ Effect (SignalResolve [k >:> resolver]) Return]
                _ -> []
              releaseWrite = case writeLock of
                Borrow _ resolver ->
                  [Effect (SignalAwait [SuccIdx $ SuccIdx $ SuccIdx ZeroIdx]) $ Effect (SignalResolve [k >:> resolver]) Return]
                _ -> []
            in
              LoopFutureBody
                instr
                k56
                (Just $ FutureBuffer tp (weaken k signal) (weaken k ref)
                  (Borrow (k26 >:> SuccIdx ZeroIdx) (SuccIdx $ SuccIdx ZeroIdx))
                  (Just $ Borrow (k26 >:> ZeroIdx) ZeroIdx))
                (Just $ FutureBuffer tp (weaken k signal) (weaken k ref)
                  (Borrow (SuccIdx ZeroIdx) (k46 >:> ZeroIdx))
                  (Just $ Borrow (SuccIdx $ SuccIdx $ SuccIdx ZeroIdx) (k46 >:> SuccIdx ZeroIdx)))
                (releaseRead ++ releaseWrite)

loopFuture _ k01 (FutureBuffer tp signal ref readLock (Just writeLock)) (Just SyncWrite) (Just SyncRead)
  -- "Write-before-read"
  -- We must add two signals (and accompanying signal resolvers) to the state
  -- to synchronize read and write access. Furthermore we need to declare three
  -- local signals in the body of the loop.
  -- Note that the next iteration gets read access when the current one
  -- finished writing, and the next iteration gets write access when this
  -- iteratioon has finished reading. This is similar to the write-before-write
  -- case in chainFuture.
  --
  = LoopFuture
      (InputOutputRpair InputOutputRsignal InputOutputRsignal)
      (weakenSucc $ weakenSucc weakenId)
      (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle BaseRsignal)
      (TupRsingle (Var BaseRsignal $ lockSignal readLock) `TupRpair` TupRsingle (Var BaseRsignal $ lockSignal writeLock))
      $ \k23 ->
        LoopFutureOutput
          (weakenSucc $ weakenSucc weakenId)
          (LeftHandSideSingle BaseRsignalResolver `LeftHandSidePair` LeftHandSideSingle BaseRsignalResolver)
          $ \k45 ->
            let
              -- Wait on condition and step to be finished reading
              awaitRead = [SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx, SuccIdx ZeroIdx]
              -- Wait on condition to be finished writing
              awaitWrite = [SuccIdx $ SuccIdx $ SuccIdx ZeroIdx]
              instr = \i ->
                Alet lhsSignal NewSignal -- Signal denotes whether the condition has finished reading the array
                  $ Alet lhsSignal NewSignal -- Signal denotes whether the condition has finished writing the array
                  $ Alet lhsSignal NewSignal -- Signal denotes whether the step has finished reading the array
                  $ Fork i
                  $ Fork
                      -- When condition and step are done reading, then the
                      -- next iteration may get write access.
                      (Effect (SignalAwait awaitRead) $ Effect (SignalResolve [k46 >:> ZeroIdx]) Return)
                      -- When condition is finished with writing, then the
                      -- next iteration may get read access.
                      (Effect (SignalAwait awaitWrite) $ Effect (SignalResolve [k46 >:> SuccIdx ZeroIdx]) Return)

              k56 = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId
              k46 = k56 .> k45
              k26 = k46 .> weakenSucc (weakenSucc weakenId) .> k23
              k = k26 .> weakenSucc (weakenSucc weakenId) .> k01

              -- Release at end of loop
              releaseRead = case readLock of
                Borrow _ resolver ->
                  [Effect (SignalAwait awaitWrite) $ Effect (SignalResolve [k >:> resolver]) Return]
                _ -> []
              releaseWrite = case writeLock of
                Borrow _ resolver ->
                  [Effect (SignalAwait $ take 1 awaitRead) $ Effect (SignalResolve [k >:> resolver]) Return]
                _ -> []
            in
              LoopFutureBody
                instr
                k56
                (Just $ FutureBuffer tp (weaken k signal) (weaken k ref)
                  (Borrow (k26 >:> SuccIdx ZeroIdx) (SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx))
                  (Just $ Borrow (k26 >:> ZeroIdx) (SuccIdx $ SuccIdx ZeroIdx)))
                (Just $ FutureBuffer tp (weaken k signal) (weaken k ref)
                  -- The step may start reading when the condition is finished writing
                  (Borrow (SuccIdx $ SuccIdx $ SuccIdx ZeroIdx) ZeroIdx)
                  Nothing)
                (releaseRead ++ releaseWrite)
loopFuture _ k01 (FutureBuffer tp signal ref readLock (Just writeLock)) (Just SyncRead) (Just SyncWrite)
  -- "Read-before-write"
  -- We must add two signals (and accompanying signal resolvers) to the state
  -- to synchronize read and write access. Futhermore we need to declare two
  -- local signals in the body of the loop.
  -- Note that the next iteration gets read access when the current one
  -- finished writing, and the next iteration gets write access when this
  -- iteratioon has finished reading. This is similar to the write-before-write
  -- case in chainFuture.
  --
  = LoopFuture
      (InputOutputRpair InputOutputRsignal InputOutputRsignal)
      (weakenSucc $ weakenSucc weakenId)
      (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle BaseRsignal)
      (TupRsingle (Var BaseRsignal $ lockSignal readLock) `TupRpair` TupRsingle (Var BaseRsignal $ lockSignal writeLock))
      $ \k23 ->
        LoopFutureOutput
          (weakenSucc $ weakenSucc weakenId)
          (LeftHandSideSingle BaseRsignalResolver `LeftHandSidePair` LeftHandSideSingle BaseRsignalResolver)
          $ \k45 ->
            let
              instr = \i ->
                Alet lhsSignal NewSignal -- Signal denotes whether the condition has finished reading the array
                  $ Alet lhsSignal NewSignal -- Signal denotes whether the step may start writing to the array
                  $ Fork i
                  $ -- The step may start writing to the array when the previous iteration has granted
                    -- write access and the condition has finished reading from the array. 
                    Effect (SignalAwait [k26 >:> ZeroIdx, SuccIdx $ SuccIdx $ SuccIdx ZeroIdx])
                           (Effect (SignalResolve [ZeroIdx]) Return)

              k56 = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId
              k46 = k56 .> k45
              k26 = k46 .> weakenSucc (weakenSucc weakenId) .> k23
              k = k26 .> weakenSucc (weakenSucc weakenId) .> k01

              -- Release at end of loop
              releaseRead = case readLock of
                Borrow _ resolver ->
                  [Effect (SignalAwait [k26 >:> SuccIdx ZeroIdx]) $ Effect (SignalResolve [k >:> resolver]) Return]
                _ -> []
              releaseWrite = case writeLock of
                Borrow _ resolver ->
                  [Effect (SignalAwait [k26 >:> ZeroIdx]) $ Effect (SignalResolve [k >:> resolver]) Return]
                _ -> []
            in
              LoopFutureBody
                instr
                k56
                (Just $ FutureBuffer tp (weaken k signal) (weaken k ref)
                  (Borrow (k26 >:> SuccIdx ZeroIdx) (SuccIdx $ SuccIdx ZeroIdx))
                  Nothing)
                (Just $ FutureBuffer tp (weaken k signal) (weaken k ref)
                  -- The next iteration gets write access when this iteration
                  -- finished reading.
                  (Borrow (k26 >:> SuccIdx ZeroIdx) (k46 >:> ZeroIdx))
                  -- The next iteration gets read access when this iteration
                  -- finished writing.
                  (Just $ Borrow (SuccIdx ZeroIdx) (k46 >:> SuccIdx ZeroIdx)))
                (releaseRead ++ releaseWrite)
loopFuture _ k01 (FutureBuffer tp signal ref readLock (Just writeLock)) (Just SyncWrite) Nothing
  -- "Write-in-condition"
  -- A writeable buffer used only in the condition.
  -- We need to add two signals (and accompanying signal resolvers) to the
  -- state of the loop to synchronize read and write access.
  -- Furthermore, we need to declare two declare two local signals
  -- in the body of the loop. The compiled code for the condition
  -- will resolve those local signals. When that signal is resolved, we
  -- also resolve the signal from the state. We release the buffer from the
  -- the loop (if condition was false and readLock and/or writeLock are Borrow)
  = LoopFuture
      (InputOutputRpair InputOutputRsignal InputOutputRsignal)
      (weakenSucc $ weakenSucc weakenId)
      (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle BaseRsignal)
      (TupRsingle (Var BaseRsignal $ lockSignal readLock) `TupRpair` TupRsingle (Var BaseRsignal $ lockSignal writeLock))
      $ \k23 ->
        LoopFutureOutput
          (weakenSucc $ weakenSucc weakenId)
          (LeftHandSideSingle BaseRsignalResolver `LeftHandSidePair` LeftHandSideSingle BaseRsignalResolver)
          $ \k45 ->
            let
              awaitRead = [SuccIdx $ SuccIdx $ SuccIdx ZeroIdx]
              awaitWrite = [SuccIdx ZeroIdx]
              instr = \i ->
                Alet lhsSignal NewSignal
                $ Alet lhsSignal NewSignal
                $ Fork i
                -- When this iteration is done reading, the next may get write access.
                -- Note that an operation needs both read and write access to perform
                -- updates to a buffer, so the next iteration will indirectly also wait
                -- for this iteration to be done with writing.
                $ Fork (Effect (SignalAwait awaitRead) $ Effect (SignalResolve [k46 >:> ZeroIdx]) Return)
                -- When this iteration is done writing, the next may get read access.
                $ Effect (SignalAwait awaitWrite) $ Effect (SignalResolve [k46 >:> SuccIdx ZeroIdx]) Return
              k56 = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId
              k46 = k56 .> k45
              k26 = k46 .> weakenSucc (weakenSucc weakenId) .> k23
              k = k26 .> weakenSucc (weakenSucc weakenId) .> k01

              -- Release at end of loop
              releaseRead = case readLock of
                Borrow _ resolver ->
                  [Effect (SignalAwait awaitWrite) $ Effect (SignalResolve [k >:> resolver]) Return]
                _ -> []
              releaseWrite = case writeLock of
                Borrow _ resolver ->
                  [Effect (SignalAwait awaitRead) $ Effect (SignalResolve [k >:> resolver]) Return]
                _ -> []
              future' = FutureBuffer tp (weaken k signal) (weaken k ref)
                (Borrow (k26 >:> SuccIdx ZeroIdx) (SuccIdx $ SuccIdx ZeroIdx))
                (Just $ Borrow (k26 >:> ZeroIdx) ZeroIdx)
            in
              LoopFutureBody
                instr
                k56
                (Just future')
                Nothing
                (releaseRead ++ releaseWrite)
loopFuture _ k01 (FutureBuffer tp signal ref readLock (Just writeLock)) Nothing (Just SyncWrite)
  -- "Write-in-step"
  -- A writeable buffer used only in the step.
  -- We need to add two signals (and accompanying signal resolvers) to the
  -- state of the loop to synchronize read and write access.
  = LoopFuture
      (InputOutputRpair InputOutputRsignal InputOutputRsignal)
      (weakenSucc $ weakenSucc weakenId)
      (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle BaseRsignal)
      (TupRsingle (Var BaseRsignal $ lockSignal readLock) `TupRpair` TupRsingle (Var BaseRsignal $ lockSignal writeLock))
      $ \k23 ->
        LoopFutureOutput
          (weakenSucc $ weakenSucc weakenId)
          (LeftHandSideSingle BaseRsignalResolver `LeftHandSidePair` LeftHandSideSingle BaseRsignalResolver)
          $ \k45 ->
            let
              instr = id
              k25 = k45 .> weakenSucc (weakenSucc weakenId) .> k23
              k = k25 .> weakenSucc (weakenSucc weakenId) .> k01

              -- Release at end of loop
              releaseRead = case readLock of
                Borrow _ resolver ->
                  [Effect (SignalAwait [k25 >:> SuccIdx ZeroIdx]) $ Effect (SignalResolve [k >:> resolver]) Return]
                _ -> []
              releaseWrite = case writeLock of
                Borrow _ resolver ->
                  [Effect (SignalAwait [k25 >:> ZeroIdx]) $ Effect (SignalResolve [k >:> resolver]) Return]
                _ -> []
              future' = FutureBuffer tp (weaken k signal) (weaken k ref)
                -- When this iteration is done reading, the next may get write access.
                -- Note that an operation needs both read and write access to perform
                -- updates to a buffer, so the next iteration will indirectly also wait
                -- for this iteration to be done with writing.
                (Borrow (k25 >:> SuccIdx ZeroIdx) (k45 >:> ZeroIdx))
                -- When this iteration is done writing, the next may get read access.
                (Just $ Borrow (k25 >:> ZeroIdx) (k45 >:> SuccIdx ZeroIdx))
            in
              LoopFutureBody
                instr
                weakenId
                Nothing
                (Just future')
                (releaseRead ++ releaseWrite)

-- Cases with only read permissions
loopFuture resolved k01 (FutureBuffer tp signal ref (Borrow acquireRead releaseRead) Nothing) (Just SyncRead) (Just SyncRead)
  -- "Read-before-read"
  -- A borrowed buffer, used in both the condition and the body.
  -- We need one signal in the state of the loop, to denote that the previous
  -- iterations have finished working with the array.  The accompanying signal
  -- resolver is resolved when this signal is finished and the current
  -- iteration is done working with the array. When the loop has finished and
  -- those signals are resolved, we will also release the entire buffer by
  -- resolving 'releaseRead'.
  --
  -- This buffer is used in both the condition and the step function. Hence we
  -- need two signals and two signal resolvers to synchronize this.
  = LoopFuture
      InputOutputRsignal
      (weakenSucc weakenId)
      (LeftHandSideSingle BaseRsignal)
      (TupRsingle $ Var BaseRsignal resolved)
      $ \k23 ->
        LoopFutureOutput
          (weakenSucc weakenId)
          (LeftHandSideSingle BaseRsignalResolver)
          $ \k45 ->
            let
              awaits = [k26 >:> ZeroIdx, SuccIdx ZeroIdx, SuccIdx $ SuccIdx $ SuccIdx ZeroIdx]
              instr = \i ->
                Alet lhsSignal NewSignal
                $ Alet lhsSignal NewSignal
                $ Fork i
                $ Effect (SignalAwait awaits) $ Effect (SignalResolve [k46 >:> ZeroIdx]) Return
              release = Effect (SignalAwait awaits) $ Effect (SignalResolve [k >:> releaseRead]) Return
              k56 = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId
              k46 = k56 .> k45
              k26 = k46 .> weakenSucc weakenId .> k23
              k = k26 .> weakenSucc weakenId .> k01
            in
              LoopFutureBody
                instr
                k56
                (Just $ FutureBuffer tp (weaken k signal) (weaken k ref) (Borrow (weaken k acquireRead) $ SuccIdx $ SuccIdx ZeroIdx) Nothing)
                (Just $ FutureBuffer tp (weaken k signal) (weaken k ref) (Borrow (weaken k acquireRead) ZeroIdx) Nothing)
                [release]
loopFuture resolved k01 (FutureBuffer tp signal ref (Borrow acquireRead releaseRead) Nothing) mleft mright
  | left || right
  -- "Single-read"
  -- A borrowed buffer, used in only one subterm of the loop (condition or step).
  -- This is similar to the previous case, but slightly simpler. We only need
  -- to declare one signal and one signal resolver to synchronize this.
  = LoopFuture
      InputOutputRsignal
      (weakenSucc weakenId)
      (LeftHandSideSingle BaseRsignal)
      (TupRsingle $ Var BaseRsignal resolved)
      $ \k23 ->
        LoopFutureOutput
          (weakenSucc weakenId)
          (LeftHandSideSingle BaseRsignalResolver)
          $ \k45 ->
            let
              instr = \i ->
                Alet lhsSignal NewSignal
                $ Fork i
                $ Effect (SignalAwait [k26 >:> ZeroIdx, SuccIdx ZeroIdx]) $ Effect (SignalResolve [k46 >:> ZeroIdx]) Return
              future' = FutureBuffer tp (weaken k signal) (weaken k ref) (Borrow (weaken k acquireRead) ZeroIdx) Nothing
              release
                -- If the buffer is only used in the left subterm (the condition),
                -- then wait on the previous iteration and the signal from the condition.
                | left = Effect (SignalAwait [k26 >:> ZeroIdx, SuccIdx ZeroIdx]) $ Effect (SignalResolve [k >:> releaseRead]) Return
                -- If the buffer is only used in the right subterm (the step function),
                -- then don't wait on the signal from this subterm. The release instruction
                -- is executed when the condition is false, so the step function is not
                -- executed any more in this iteration.
                -- We do resolve the signal for this subterm, to assure that any other
                -- threads waiting on this signal can proceed; they don't have to wait
                -- on the step function to finish.
                | otherwise = Effect (SignalAwait [k26 >:> ZeroIdx]) $ Effect (SignalResolve [k >:> releaseRead, ZeroIdx]) Return
              k56 = weakenSucc $ weakenSucc  weakenId
              k46 = k56 .> k45
              k26 = k46 .> weakenSucc weakenId .> k23
              k = k26 .> weakenSucc weakenId .> k01
            in
              LoopFutureBody
                instr
                k56
                (fmap (const future') mleft)
                (fmap (const future') mright)
                [release]
  where
    left = isJust mleft
    right = isJust mright
loopFuture _ k01 future left right
  -- A buffer with Move read lock or a scalar, no further synchronisation needed
  = LoopFuture
      InputOutputRunit
      weakenId
      (LeftHandSideWildcard TupRunit)
      TupRunit
      $ \k23 ->
        LoopFutureOutput
          weakenId
          (LeftHandSideWildcard TupRunit)
          $ \k45 ->
          let
            future' = weaken (k45 .> k23 .> k01) future
          in
            LoopFutureBody
              id
              weakenId
              (if isScalar || isJust left  then Just future' else Nothing)
              (if isScalar || isJust right then Just future' else Nothing)
              []
  where
    isScalar
      | FutureScalar{} <- future = True
      | otherwise = False

lhsSignal :: LeftHandSide BaseR (Signal, SignalResolver) fenv ((fenv, Signal), SignalResolver)
lhsSignal = LeftHandSidePair (LeftHandSideSingle BaseRsignal) (LeftHandSideSingle BaseRsignalResolver)

lhsRef :: GroundR tp -> LeftHandSide BaseR (Ref tp, OutputRef tp) fenv ((fenv, Ref tp), OutputRef tp)
lhsRef tp = LeftHandSidePair (LeftHandSideSingle $ BaseRref tp) (LeftHandSideSingle $ BaseRrefWrite tp)

-- Set of identifiers which are reused as a destination and thus do not need to 
-- be passed in the FutureEnv. For instance, in this program:
--
-- x = ..
-- ..code..
-- return (x, y)
--
-- where 'code' doesn't use x, we do not create new signals and references to
-- store the result for x. We can directly write the result of x to the output
-- destination of this program. Hence x shouldn't be present in the FutureEnv
-- when compiling 'code'. We store x in ReusedVars to handle this.
--
newtype ReusedVars genv = ReusedVars { reusedVarsSet :: IdxSet genv }

removeReusedVars :: ReusedVars genv -> SyncEnv genv -> SyncEnv genv
removeReusedVars (ReusedVars (IdxSet.IdxSet reused)) env = diffPartialEnv env reused

syncEnv' :: ReusedVars genv -> PartialSchedule kernel genv t -> SyncEnv genv
syncEnv' reused = removeReusedVars reused . syncEnv

syncEnvFun' :: ReusedVars genv -> PartialScheduleFun kernel genv t -> SyncEnv genv
syncEnvFun' reused = removeReusedVars reused . syncEnvFun

lhsReusedVars :: GLeftHandSide t genv genv' -> TupR (Destination r) t -> ReusedVars genv -> ReusedVars genv'
lhsReusedVars (LeftHandSideWildcard _) _ reused = reused
lhsReusedVars (LeftHandSideSingle _)   (TupRsingle DestinationNew)     (ReusedVars vars) = ReusedVars $ IdxSet.skip vars
lhsReusedVars (LeftHandSideSingle _)   (TupRsingle DestinationReuse{}) (ReusedVars vars) = ReusedVars $ IdxSet.push vars
lhsReusedVars (LeftHandSidePair l1 l2) (TupRpair d1 d2)                reused            = lhsReusedVars l2 d2 $ lhsReusedVars l1 d1 reused
lhsReusedVars (LeftHandSidePair l1 l2) (TupRsingle DestinationNew)     reused
  = lhsReusedVars (LeftHandSidePair l1 l2) (TupRsingle DestinationNew `TupRpair` TupRsingle DestinationNew) reused
lhsReusedVars _ _ _ = internalError "Impossible case"

-- Similar to 'fromPartial', but also applies the sub-environment rule 
fromPartialSub
  :: forall kernel fenv genv t r.
     HasCallStack
  => OutputEnv t r
  -> BaseVars fenv r
  -> FutureEnv fenv genv
  -> ReusedVars genv
  -> PartialSchedule kernel genv t
  -> UniformSchedule kernel fenv
fromPartialSub outputEnv outputVars env reused partial
  = sub env (syncEnv' reused partial) (\env' -> fromPartial outputEnv outputVars env' reused partial)

fromPartialFun
  :: forall kernel fenv genv t.
     HasCallStack
  => FutureEnv fenv genv
  -> ReusedVars genv
  -> PartialScheduleFun kernel genv t
  -> UniformScheduleFun kernel fenv (Scheduled UniformScheduleFun t)
fromPartialFun env reused = \case
  Pbody body
    | grounds <- groundsR body
    , Refl <- reprIsBody @UniformScheduleFun $ grounds
    , DeclareOutput k1 lhs k2 instr outputEnv outputVars <- declareOutput grounds
    -> Slam lhs $ Sbody $ instr $ fromPartial outputEnv (outputVars weakenId) (mapPartialEnv (weaken (k2 .> k1)) env) reused body
  Plam lhs fun
    | DeclareInput _ lhs' env' <- declareInput env lhs
    -> Slam lhs' $ fromPartialFun (env' weakenId) (ReusedVars $ IdxSet.skip' lhs $ reusedVarsSet reused) fun

fromPartial
  :: forall kernel fenv genv t r.
     HasCallStack
  => OutputEnv t r
  -> BaseVars fenv r
  -> FutureEnv fenv genv
  -> ReusedVars genv
  -> PartialSchedule kernel genv t
  -> UniformSchedule kernel fenv
fromPartial outputEnv outputVars env reused = \case
    PartialDo outputEnv' convertEnv (schedule :: UniformSchedule kernel fenv') ->
      let
        kEnv = partialDoSubstituteOutput outputEnv' outputEnv outputVars
        kEnv' :: Env (NewIdx fenv) fenv'
        kEnv' = partialDoSubstituteConvertEnv convertEnv env kEnv

        k :: ReindexPartialN Identity fenv' fenv
        k idx = Identity $ prj' idx kEnv'
      in
        runIdentity $ reindexSchedule k schedule -- Something with a substitution
    PartialReturn _ vars -> travReturn vars
    PartialDeclare _ lhs dest uniquenesses bnd body
      | reused' <- lhsReusedVars lhs dest reused
      , ChainFutureEnv splitInstr k1 envBnd envBody <- chainFutureEnvironment weakenId env (syncEnv' reused bnd) (environmentDropLHS (syncEnv' reused' body) lhs)
      , DeclareBinding k2 instr outputEnvBnd outputVarsBnd envBody' bndSignals <- declareBinding outputEnv (mapTupR (weaken k1) outputVars) envBody lhs dest uniquenesses ->
        splitInstr
        $ instr
        $ forkUnless
          (fromPartial outputEnvBnd (outputVarsBnd weakenId) (mapPartialEnv (weaken k2) envBnd) reused bnd)
          (fromPartialSub outputEnv (mapTupR (weaken $ k2 .> k1) outputVars) (envBody' weakenId) reused' body)
          (bndSignals weakenId)
    PartialAcond _ condition true false -> acond condition true false
    PartialAwhile _ uniquenesses condition step initial -> awhile uniquenesses condition step initial
  where
    travReturn :: GroundVars genv t -> UniformSchedule kernel fenv
    travReturn vars = forks (uncurry await <$> travReturn' outputEnv outputVars vars [])

    travReturn' :: OutputEnv t' r' -> BaseVars fenv r' -> GroundVars genv t' -> [([Idx fenv Signal], UniformSchedule kernel fenv)] -> [([Idx fenv Signal], UniformSchedule kernel fenv)]
    travReturn' (OutputEnvPair o1 o2) (TupRpair r1 r2) (TupRpair v1 v2) accum = travReturn' o1 r1 v1 $ travReturn' o2 r2 v2 accum
    travReturn' (OutputEnvScalar tp') (TupRpair (TupRsingle destSignal) (TupRsingle destRef)) (TupRsingle (Var tp ix)) accum = task : accum
      where
        task = case prjPartial ix env of
          Nothing -> ( [], Return ) -- No need to copy, as output was already written at the declaration of the variable using destination-passing-style
          Just (FutureScalar _ signal ref) ->
            ( [signal]
            , Alet (LeftHandSideSingle $ BaseRground tp) (RefRead $ Var (BaseRref tp) ref)
              $ Effect (RefWrite (weaken (weakenSucc weakenId) destRef) (Var (BaseRground tp) ZeroIdx))
              $ Effect (SignalResolve [weakenSucc weakenId >:> varIdx destSignal])
                Return
            )
          Just FutureBuffer{} -> bufferImpossible tp'
    travReturn' OutputEnvShared (TupRpair (TupRsingle destSignalRef `TupRpair` TupRsingle destSignalRead) (TupRsingle destRef)) (TupRsingle (Var tp ix)) accum = task : accum
      where
        task = case prjPartial ix env of
          Nothing -> ( [], Return ) -- No need to copy, as output was already written at the declaration of the variable using destination-passing-style
          Just (FutureScalar tp' _ _) -> bufferImpossible tp'
          Just (FutureBuffer _ signal ref readAccess _) ->
            ( [signal]
            , Alet (LeftHandSideSingle $ BaseRground tp) (RefRead $ Var (BaseRref tp) ref)
              $ Effect (RefWrite (weaken (weakenSucc weakenId) destRef) (Var (BaseRground tp) ZeroIdx))
              $ Effect (SignalResolve [weakenSucc weakenId >:> varIdx destSignalRef])
              $ Effect (SignalAwait [weakenSucc weakenId >:> lockSignal readAccess])
              $ Effect (SignalResolve [weakenSucc weakenId >:> varIdx destSignalRead])
                Return
            )
    travReturn' OutputEnvUnique (TupRpair (TupRpair (TupRsingle destSignalRef `TupRpair` TupRsingle destSignalRead) (TupRsingle destSignalWrite)) (TupRsingle destRef)) (TupRsingle (Var tp ix)) accum = task : accum
      where
        task = case prjPartial ix env of
          Nothing -> ( [], Return ) -- No need to copy, as output was already written at the declaration of the variable using destination-passing-style
          Just (FutureScalar tp' _ _) -> bufferImpossible tp'
          Just (FutureBuffer _ _ _ _ Nothing) -> internalError "Expected FutureBuffer with write access"
          Just (FutureBuffer _ signal ref readAccess (Just writeAccess)) ->
            ( [signal]
            , Alet (LeftHandSideSingle $ BaseRground tp) (RefRead $ Var (BaseRref tp) ref)
              $ Effect (RefWrite (weaken (weakenSucc weakenId) destRef) (Var (BaseRground tp) ZeroIdx))
              $ Effect (SignalResolve [weakenSucc weakenId >:> varIdx destSignalRef])
              $ Effect (SignalAwait [weakenSucc weakenId >:> lockSignal readAccess])
              $ Effect (SignalResolve [weakenSucc weakenId >:> varIdx destSignalRead])
              $ Effect (SignalAwait [weakenSucc weakenId >:> lockSignal writeAccess])
              $ Effect (SignalResolve [weakenSucc weakenId >:> varIdx destSignalWrite])
                Return
            )
    -- Destination was reused. No need to copy
    travReturn' OutputEnvIgnore _ _ accum = accum
    travReturn' _ _ _ _ = internalError "Invalid variables"

    acond :: ExpVar genv PrimBool -> PartialSchedule kernel genv t -> PartialSchedule kernel genv t -> UniformSchedule kernel fenv
    acond (Var _ condition) true false = case prjPartial condition env of
      Just (FutureScalar _ signal ref) ->
        -- Wait on the signal 
        Effect (SignalAwait [signal])
          -- Read the value of the condition
          $ Alet (LeftHandSideSingle $ BaseRground $ GroundRscalar scalarType) (RefRead $ Var (BaseRref $ GroundRscalar scalarType) ref)
          $ Acond
            (Var scalarType ZeroIdx)
            (fromPartialSub outputEnv outputVars' env' reused true)
            (fromPartialSub outputEnv outputVars' env' reused false)
            Return
      Nothing -> internalError "Variable not found"
      where
        outputVars' = mapTupR (weaken (weakenSucc weakenId)) outputVars
        env' = mapPartialEnv (weaken (weakenSucc weakenId)) env

    awhile
      :: Uniquenesses t
      -> PartialScheduleFun kernel genv (t -> PrimBool)
      -> PartialScheduleFun kernel genv (t -> t)
      -> GroundVars genv t
      -> UniformSchedule kernel fenv
    awhile = fromPartialAwhile outputEnv outputVars env reused

debugFutureEnv :: FutureEnv fenv genv -> String
debugFutureEnv (PPush env e) = debugFutureEnv env ++ " " ++ e'
  where
    e' = case e of
      FutureScalar{} -> "S"
      FutureBuffer _ _ _ _ Nothing -> "R"
      FutureBuffer _ _ _ _ Just{}  -> "W"
debugFutureEnv (PNone env) = debugFutureEnv env ++ " _"
debugFutureEnv PEnd = "FutureEnv"

-- TODO: How do the condition and step synchronize access between the variables from the state?

fromPartialAwhile
  :: forall kernel fenv genv t r.
     HasCallStack
  => OutputEnv t r
  -> BaseVars fenv r
  -> FutureEnv fenv genv
  -> ReusedVars genv
  -> Uniquenesses t
  -> PartialScheduleFun kernel genv (t -> PrimBool)
  -> PartialScheduleFun kernel genv (t -> t)
  -> GroundVars genv t
  -> UniformSchedule kernel fenv
fromPartialAwhile outputEnv outputVars env reused uniquenesses conditionFun@(Plam lhsC (Pbody condition)) stepFun@(Plam lhsS (Pbody step)) initial
  -- Split environment for initial vars and body
  | ChainFutureEnv instrSplit k0 envInitial envLoop <- chainFutureEnvironment (weakenSucc $ weakenSucc weakenId) env (variablesToSyncEnv uniquenesses initial) (unionPartialEnv max (syncEnvFun' reused conditionFun) (syncEnvFun' reused stepFun))
  -- Create a LHS which brings variables in scope for both the condition and
  -- the step function. This is needed as they may have wildcards at different
  -- locations
  , Exists groundLhs <- unionLeftHandSides lhsC lhsS
  -- Create the input and output representations for the loop
  , AwhileInputOutput io k1 lhsInput envLoop' initial' outputEnv' outputRepr <- awhileInputOutput envInitial (\k -> mapPartialEnv (weaken k) envLoop) uniquenesses initial groundLhs
  -- We still need to manipulate the environment for proper synchronisation of
  -- free variables. Hence we can only use the variables bound in 'groundLhs'
  -- from this environment. We extract that part of the environment in
  -- envLambdaInput.
  , FutureEnvOuter _ envLambdaInput <- futureEnvOuter groundLhs (envLoop' weakenId)
  -- In the loop, we must synchronize access to free buffer variables. This is
  -- especially difficult as loops can be executed asynchronously: different
  -- parts of different loops can be executed at the same time, if the
  -- dependencies allow that. For readonly buffers, we must release the buffer
  -- when all iterations have finished working with that buffer. We introduce
  -- a signal in the state of the loop to denote that all iterations up to that
  -- iteration have finished working with the buffer. For writeable buffers
  -- we must add two signals, one to denote that the previous iteration has
  -- finished reading and one to denote that the previous iteration has
  -- finished writing. Note that this now only regards the previous iteration,
  -- as the desire to write already adds more barriers and hence the
  -- synchronisation is "more local".
  , LoopFutureEnv syncLoopIo k2 lhsSyncLoopInput loopSyncInitial syncLoopOutput <- loopFutureEnvironment (k0 >:> defaultSignal) k1 envLoop (syncEnvFun' reused conditionFun) (syncEnvFun' reused stepFun)
  -- The body of the loop is a function which outputs a boolean to denote
  -- whether the loop should continue ...
  , lhsOutputBool <- LeftHandSideSingle BaseRsignalResolver `LeftHandSidePair` LeftHandSideSingle (BaseRrefWrite $ GroundRscalar scalarType)
  -- ... and outputs the next state of the loop.
  , DeclareVars lhsOutput k3 outputVars' <- declareVars outputRepr
  -- The synchronisation of free buffer variables introduces new signals for
  -- the state of the loop. In thus also introduces new output variables.
  -- Because of the typed environment, we can only now really construct those.
  , LoopFutureEnvOutput k4 lhsSyncLoopOutput syncLoopBody <- syncLoopOutput (weakenSucc $ weakenSucc k3)
  -- The synchronisation may also need to introduce new local signals in the
  -- body of the loop. For instance, for a free readonly borrowed buffer
  -- variable, we must introduce a signal to denote that the current iteration,
  -- say i, has finished working with the buffer. We can then resolve the signal
  -- which denotes that iterations up to and including i are done with the
  -- buffer (i.e. the output signal resolver of this iteration) if that local
  -- signal and the input signal from the state (i.e. the signal that denotes
  -- that iterations up to i are done with the buffer) are resolved.
  -- Adding new local signals is handled by 'syncLoopInstr' and 'k5'.
  --
  -- We also construct environments with the free variables for the condition
  -- and step functions, respectively envC' and envS'.
  --
  -- When the loop is finished, we must release the free buffers variables that
  -- we used. This is handled by 'syncLoopRelease'.
  , LoopFutureEnvBody syncLoopInstr k5 envC' envS' syncLoopRelease <- syncLoopBody weakenId
  -- envC' and envS' only contain bindings for the free buffer variables. We
  -- must now add the variables for the bound variables from the state of the
  -- loop, handled by envLambdaInput (originating from futureEnvOuter).
  -- Then we must create a sub-environment, only containing the part of the
  -- loop state which is actually used: it might be that lhsC and lhsS
  -- do not bind all variables and have wildcards at different locations.
  , envC <- environmentForSubLHS (envLambdaInput (k5 .> k4 .> k3 .> weakenSucc' (weakenSucc' k2)) envC') groundLhs lhsC
  , envS <- environmentForSubLHS (envLambdaInput (k5 .> k4 .> k3 .> weakenSucc' (weakenSucc' k2)) envS') groundLhs lhsS
  = let
      -- Create the loop function:
      -- Accept arguments for the input state (and additional signals in the
      -- state for synchronization of free buffer variables).
      f = Slam (LeftHandSidePair lhsInput lhsSyncLoopInput)
        -- Accept an output argument (destination) for the condition
        $ Slam lhsOutputBool
        -- and the next state (only used if condition is True), including
        -- additional signal resolvers for synchronization.
        $ Slam (LeftHandSidePair lhsOutput lhsSyncLoopOutput)
        $ Sbody
        -- Add additional local signals for synchronizing free buffer variables
        -- if needed. This may also introduce forks to perform synchronization,
        -- e.g. wait on some signals and then resolve some other signal.
        $ syncLoopInstr
        -- Create a signal to be filled when the condition is executed.
        $ Alet lhsSignal NewSignal
        -- We first bind the condition locally before writing the reference
        -- from the output argument. This is needed to check whether we should
        -- perform another iteration in the loop.
        $ Alet (lhsRef $ GroundRscalar scalarType) (NewRef $ GroundRscalar scalarType)
        -- Execute the condition and then, if needed, another iteration of the
        -- loop. Note that 'serial' tries to execute the two schedules serially
        -- but does not guarantee that. Hence we still need the synchronisation
        -- with the signal.
        $ serial
          [ fromPartialSub
              (OutputEnvScalar scalarType)
              -- Write output to the locally defined signal resolver and
              -- reference
              (TupRsingle (Var BaseRsignalResolver $ SuccIdx $ SuccIdx ZeroIdx) `TupRpair` TupRsingle (Var (BaseRrefWrite $ GroundRscalar scalarType) ZeroIdx))
              -- Use the previously constructed environment for the condition
              -- (envC) and weaken it as we introduced a signal (resolver) and
              -- (writeable) reference (2 * 2 variables).
              (mapPartialEnv (weaken $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId) envC)
              (ReusedVars $ IdxSet.skip' lhsC $ reusedVarsSet reused)
              condition
          , -- Wait on signal of condition
            Effect (SignalAwait [SuccIdx $ SuccIdx $ SuccIdx ZeroIdx])
            -- Read condition
            $ Alet (LeftHandSideSingle $ BaseRground $ GroundRscalar scalarType) (RefRead $ Var (BaseRref $ GroundRscalar scalarType) $ SuccIdx ZeroIdx)
            -- Write to output variable for condition.
            -- Note that you can see that the reference (the first Var passed
            -- to RefWrite) originates from 'lhsOutputBool' as it was weakened
            -- by k5, k4 and k3 and lhsOutputBool was introduced just before
            -- k3.
            $ Effect (RefWrite (Var (BaseRrefWrite $ GroundRscalar scalarType) ((weakenSucc' $ weakenSucc' $ weakenSucc' $ weakenSucc' $ weakenSucc' $ k5 .> k4 .> k3) >:> ZeroIdx)) (Var (BaseRground $ GroundRscalar scalarType) ZeroIdx))
            -- Resolve the condition-signal to inform the loop that the
            -- reference can be read. Similar to the previous comment,
            -- the signal variable originates from 'lhsOutputBool'.
            $ Effect (SignalResolve [(weakenSucc' $ weakenSucc' $ weakenSucc' $ weakenSucc' $ weakenSucc' $ k5 .> k4 .> k3) >:> SuccIdx ZeroIdx])
            -- Branch on the condition
            $ Acond (Var scalarType ZeroIdx)
              ( -- Condition is true, perform next iteration
                fromPartialSub
                  outputEnv'
                  -- Write to the destinations passed in the output argument
                  -- (lhsOutput).
                  (outputVars' $ weakenSucc' $ weakenSucc' $ weakenSucc' $ weakenSucc' $ weakenSucc' $ k5 .> k4)
                  -- Use the previously constructed environment for the step
                  -- function and weaken it as we introduced a signal and
                  -- reference for the condition, and a variable to store
                  -- the value from the reference to the condition.
                  (mapPartialEnv (weaken $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId) envS)
                  (ReusedVars $ IdxSet.skip' lhsS $ reusedVarsSet reused)
                  step
              )
              ( -- Condition is false. The loop should not continue. We must
                -- write the output to the output / destination variables of
                -- the loop. This is handled by 'awhileWriteResult'. Note that
                -- we don't always have a 1-1 mapping between the state of the
                -- loop and the destination of the loop. It can happen that a
                -- buffer is unique inside the loop, but is returned as a
                -- shared array. This can for instance happen in a program of
                -- this form:
                --
                -- acond ..
                --   a
                --   awhile ...
                -- 
                -- where 'a' is a variable of a shared buffer. The loop may
                -- still have a unique buffer internally, but write its output
                -- to a destination for a shared buffer.
                --
                -- We must also release free buffer variables. This is handled
                -- by 'syncLoopRelease'. 
                forks $ syncLoopRelease (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId)
                  ++ awhileWriteResult
                      outputEnv
                      (mapTupR (weaken $ weakenSucc' $ weakenSucc' $ weakenSucc' $ weakenSucc' $ weakenSucc' k5 .> k4 .> k3 .> weakenSucc' (weakenSucc' k2) .> k1 .> weakenSucc (weakenSucc k0)) outputVars)
                      io
                      (mapTupR (weaken $ weakenSucc' $ weakenSucc' $ weakenSucc' $ weakenSucc' $ weakenSucc' k5 .> k4 .> k3 .> weakenSucc' (weakenSucc' k2)) $ fromMaybe (internalError "Expected a complete LHS") $ lhsFullVars lhsInput)
              )
              Return
          ]
    in
      -- Create a directly resolved signal. For synchronizing free buffer
      -- variables we need signals to denote that iterations up to the
      -- current one are done with the buffer in the state of the loop.
      -- We need to initialize this with a signal to denote that all
      -- iterations before the first iteration are done (i.e., no
      -- iteration at all). We thus need a signal which is already
      -- resolved and introduce that here.
      Alet lhsSignal NewSignal
      $ Effect (SignalResolve [ZeroIdx])
      -- Instructions to split the environment into an environment for the
      -- initial state of the loop (envInitial, which constructs initial')
      -- and an environment for the body of the loop (envLoop, which we
      -- later split into separate environments for the condition and step
      -- function).
      $ instrSplit
      -- And finally, the actual loop!
      $ Awhile (InputOutputRpair io syncLoopIo) f (TupRpair initial' loopSyncInitial) Return
  where
    defaultSignal :: Idx ((fenv, Signal), SignalResolver) Signal
    defaultSignal = SuccIdx ZeroIdx
fromPartialAwhile _ _ _ _ _ _ _ _ = internalError "Function impossible"

awhileInputOutput :: FutureEnv fenv0 genv0 -> (forall fenv''. fenv :> fenv'' -> FutureEnv fenv'' genv) -> Uniquenesses t -> GroundVars genv0 t -> GLeftHandSide t genv genv' -> AwhileInputOutput fenv0 fenv genv genv' t
awhileInputOutput env0 env (TupRpair u1 u2) (TupRpair v1 v2) (LeftHandSidePair lhs1 lhs2)
  | AwhileInputOutput io1 k1 lhs1' env1 i1 outputEnv1 g1 <- awhileInputOutput env0 env  u1 v1 lhs1
  , AwhileInputOutput io2 k2 lhs2' env2 i2 outputEnv2 g2 <- awhileInputOutput env0 env1 u2 v2 lhs2
  = AwhileInputOutput
      (InputOutputRpair io1 io2)
      (k2 .> k1)
      (LeftHandSidePair lhs1' lhs2')
      env2
      (TupRpair i1 i2)
      (OutputEnvPair outputEnv1 outputEnv2)
      (TupRpair g1 g2)
awhileInputOutput env0 env uniquenesses vars (LeftHandSideWildcard (TupRpair t1 t2)) = awhileInputOutput env0 env uniquenesses vars (LeftHandSideWildcard t1 `LeftHandSidePair` LeftHandSideWildcard t2)
awhileInputOutput _ env TupRunit TupRunit (LeftHandSideWildcard TupRunit)
  = AwhileInputOutput
      InputOutputRunit
      weakenId
      (LeftHandSideWildcard TupRunit)
      env
      TupRunit
      OutputEnvIgnore
      TupRunit
awhileInputOutput env0 env (TupRsingle uniqueness) (TupRsingle (Var groundR idx)) (LeftHandSideSingle _)
  | GroundRbuffer tp <- groundR -- Unique buffer
  , Unique <- uniqueness
  = let
      initial = case prjPartial idx env0 of
        Just (FutureBuffer tp' signal ref (Move signalRead) (Just (Move signalWrite))) ->
          TupRsingle (Var BaseRsignal signal)
          `TupRpair`
          TupRsingle (Var BaseRsignal signalRead)
          `TupRpair`
          TupRsingle (Var BaseRsignal signalWrite)
          `TupRpair`
          TupRsingle (Var (BaseRref $ GroundRbuffer tp') ref)
        Just (FutureBuffer _ _ _ _ Nothing) -> internalError "Expected a Future with write permissions."
        Just FutureBuffer{} -> internalError "Expected Move. Cannot Borrow a variable into a loop."
        Just _ -> internalError "Illegal variable"
        Nothing -> internalError "Variable not found"
    in
      AwhileInputOutput
        (InputOutputRpair (InputOutputRpair (InputOutputRpair InputOutputRsignal InputOutputRsignal) InputOutputRsignal) InputOutputRref)
        -- Input
        (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId)
        (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle (BaseRref groundR))
        (\k -> env (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc k) `PPush`
                FutureBuffer tp (k >:> SuccIdx (SuccIdx $ SuccIdx ZeroIdx)) (k >:> ZeroIdx) (Move (k >:> SuccIdx (SuccIdx ZeroIdx))) (Just $ Move (k >:> SuccIdx ZeroIdx)))
        initial
        -- Output
        OutputEnvUnique
        (TupRsingle BaseRsignalResolver `TupRpair` TupRsingle BaseRsignalResolver `TupRpair` TupRsingle BaseRsignalResolver `TupRpair` TupRsingle (BaseRrefWrite groundR))
  | GroundRbuffer tp <- groundR -- Shared buffer
  = let
      initial = case prjPartial idx env0 of
        Just (FutureBuffer tp' signal ref (Move signalRead) _) ->
          TupRsingle (Var BaseRsignal signal)
          `TupRpair`
          TupRsingle (Var BaseRsignal signalRead)
          `TupRpair`
          TupRsingle (Var (BaseRref $ GroundRbuffer tp') ref)
        Just (FutureBuffer _ _ _ (Borrow _ _) _) -> internalError "Expected Move. Cannot Borrow a variable into a loop."
        Just _ -> internalError "Illegal variable"
        Nothing -> internalError "Variable not found"
    in
      AwhileInputOutput
        (InputOutputRpair (InputOutputRpair InputOutputRsignal InputOutputRsignal) InputOutputRref)
        -- Input
        (weakenSucc $ weakenSucc $ weakenSucc weakenId)
        (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle (BaseRref groundR))
        (\k -> env (weakenSucc $ weakenSucc $ weakenSucc k) `PPush`
                FutureBuffer tp (k >:> SuccIdx (SuccIdx ZeroIdx)) (k >:> ZeroIdx) (Move (k >:> SuccIdx ZeroIdx)) Nothing)
        initial
        -- Output
        OutputEnvShared
        (TupRsingle BaseRsignalResolver `TupRpair` TupRsingle BaseRsignalResolver `TupRpair` TupRsingle (BaseRrefWrite groundR))
  | GroundRscalar tp <- groundR -- Scalar
  = let
      initial = case prjPartial idx env0 of
        Just (FutureScalar tp' signal ref) ->
          TupRsingle (Var BaseRsignal signal)
          `TupRpair`
          TupRsingle (Var (BaseRref $ GroundRscalar tp') ref)
        Just _ -> internalError "Illegal variable"
        Nothing -> internalError "Variable not found"
    in
      AwhileInputOutput
        (InputOutputRpair InputOutputRsignal InputOutputRref)
        -- Input
        (weakenSucc $ weakenSucc weakenId)
        (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle (BaseRref groundR))
        (\k -> env (weakenSucc $ weakenSucc k) `PPush` FutureScalar tp (k >:> SuccIdx ZeroIdx) (k >:> ZeroIdx))
        initial
        -- Output
        (OutputEnvScalar tp)
        (TupRsingle BaseRsignalResolver `TupRpair` TupRsingle (BaseRrefWrite groundR))
awhileInputOutput env0 env uniquenesses vars (LeftHandSideWildcard (TupRsingle groundR))
  | AwhileInputOutput io k lhs env' i outputEnv g <- awhileInputOutput env0 env uniquenesses vars (LeftHandSideSingle groundR)
  = AwhileInputOutput io k lhs (partialEnvTail . env') i outputEnv g
awhileInputOutput env0 env (TupRsingle Shared) vars lhs@LeftHandSidePair{}
  = awhileInputOutput env0 env (TupRsingle Shared `TupRpair` TupRsingle Shared) vars lhs
awhileInputOutput _ _ _ _ _ = internalError "Mismatch in GroundVars and LeftHandSide"

data AwhileInputOutput fenv0 fenv genv genv' t where
  AwhileInputOutput
    :: InputOutputR input output
    -- Input
    -> (fenv :> fenv')
    -> BLeftHandSide input fenv fenv'
    -> (forall fenv''. fenv' :> fenv'' -> FutureEnv fenv'' genv')
    -> BaseVars fenv0 input
    -- Output
    -> OutputEnv t output
    -> BasesR output
    -> AwhileInputOutput fenv0 fenv genv genv' t

typeFromRef :: BaseR (Ref t) -> GroundR t
typeFromRef (BaseRref tp) = tp
typeFromRef (BaseRground (GroundRscalar _)) = internalError "Reference impossible"

-- Note that the result of the loop (type variable 'result') does not
-- have to match with the result of an iteration (type variable 'output').
-- It can happen that a buffer is unique inside the loop, but is returned
-- as a shared array. This can for instance happen in a program of this
-- form:
--
-- acond ..
--   a
--   awhile ...
-- 
-- where 'a' is a variable of a shared buffer. The loop may still have
-- a unique buffer internally, but write its output to a destination for
-- a shared buffer.
--
awhileWriteResult
  :: OutputEnv t result
  -> BaseVars fenv result
  -> InputOutputR input output
  -> BaseVars fenv input
  -> [UniformSchedule kernel fenv]
awhileWriteResult = \env resVars io vars -> go env resVars io vars []
  where
    go :: OutputEnv t result
       -> BaseVars fenv result
       -> InputOutputR input output
       -> BaseVars fenv input
       -> [UniformSchedule kernel fenv]
       -> [UniformSchedule kernel fenv]
    go (OutputEnvPair e1 e2) (TupRpair r1 r2) (InputOutputRpair io1 io2) (TupRpair i1 i2) = go e1 r1 io1 i1 . go e2 r2 io2 i2
    go (OutputEnvPair _ _)   _                _                          _                = internalError "Expected pair"
    go OutputEnvUnique (TupRsingle resSignal `TupRpair` TupRsingle resReadAccess `TupRpair` TupRsingle resWriteAccess `TupRpair` TupRsingle resRef) io input
    -- Internally unique buffer to unique buffer in result
      | InputOutputRpair (InputOutputRpair (InputOutputRpair InputOutputRsignal InputOutputRsignal) InputOutputRsignal) InputOutputRref <- io
      , TupRsingle signal `TupRpair` TupRsingle readAccess `TupRpair` TupRsingle writeAccess `TupRpair` TupRsingle ref <- input
      , ground' <- typeFromRef $ varType ref
      , Just Refl <- matchGroundR ground ground'
      = (:)
      $ Effect (SignalAwait [varIdx signal])
      $ Alet (LeftHandSideSingle $ BaseRground ground) (RefRead ref)
      $ Effect (RefWrite (weaken k resRef) $ Var (BaseRground ground) ZeroIdx)
      $ Effect (SignalResolve [weaken k $ varIdx resSignal])
      $ Effect (SignalAwait [weaken k $ varIdx readAccess])
      $ Effect (SignalResolve [weaken k $ varIdx resReadAccess])
      $ Effect (SignalAwait [weaken k $ varIdx writeAccess])
      $ Effect (SignalResolve [weaken k $ varIdx resWriteAccess])
        Return
      | otherwise = internalError "Mismatch with unique buffer"
      where
        k = weakenSucc weakenId
        ground = case varType resRef of
                   BaseRrefWrite t -> t
                   _ -> internalError "Mismatch in BaseR"
    go OutputEnvShared outputVars@(TupRsingle resSignal `TupRpair` TupRsingle resReadAccess `TupRpair` TupRsingle resRef) io input
    -- Internally shared buffer to shared buffer in result
      | InputOutputRpair (InputOutputRpair InputOutputRsignal InputOutputRsignal) InputOutputRref <- io
      , TupRsingle signal `TupRpair` TupRsingle readAccess `TupRpair` TupRsingle ref <- input
      , ground' <- typeFromRef $ varType ref
      , Just Refl <- matchGroundR ground ground'
      = (:)
      $ Effect (SignalAwait [varIdx signal])
      $ Alet (LeftHandSideSingle $ BaseRground ground) (RefRead ref)
      $ Effect (RefWrite (weaken k resRef) $ Var (BaseRground ground) ZeroIdx)
      $ Effect (SignalResolve [weaken k $ varIdx resSignal])
      $ Effect (SignalAwait [weaken k $ varIdx readAccess])
      $ Effect (SignalResolve [weaken k $ varIdx resReadAccess])
        Return
    -- Internally unique buffer to shared buffer in result
      | InputOutputRpair (InputOutputRpair (InputOutputRpair InputOutputRsignal InputOutputRsignal) InputOutputRsignal) InputOutputRref <- io
      , TupRsingle signal `TupRpair` TupRsingle readAccess `TupRpair` _ `TupRpair` TupRsingle ref <- input
      = go
          OutputEnvShared
          outputVars
          (InputOutputRpair (InputOutputRpair InputOutputRsignal InputOutputRsignal) InputOutputRref)
          (TupRsingle signal `TupRpair` TupRsingle readAccess `TupRpair` TupRsingle ref)
      | otherwise = internalError "Mismatch with unique buffer"
      where
        k = weakenSucc weakenId
        ground = case varType resRef of
                   BaseRrefWrite t -> t
                   _ -> internalError "Mismatch in BaseR"
    go (OutputEnvScalar tp) (TupRsingle resSignal `TupRpair` TupRsingle resRef) io input
    -- Internally shared buffer to shared buffer in result
      | InputOutputRpair InputOutputRsignal InputOutputRref <- io
      , TupRsingle signal `TupRpair` TupRsingle ref <- input
      , ground <- typeFromRef $ varType ref
      , Just Refl <- matchGroundR (GroundRscalar tp) ground
      = (:)
      $ Effect (SignalAwait [varIdx signal])
      $ Alet (LeftHandSideSingle $ BaseRground ground) (RefRead ref)
      $ Effect (RefWrite (weaken k resRef) $ Var (BaseRground ground) ZeroIdx)
      $ Effect (SignalResolve [weaken k $ varIdx resSignal])
        Return
      where
        k = weakenSucc weakenId
    go OutputEnvIgnore _ _ _ = (Return :)
    go _ _ _ _ = internalError "OutputEnv and InputOutputR don't match"

partialDoSubstituteOutput :: forall fenv fenv' t r ro. PartialDoOutput () fenv t r -> OutputEnv t ro -> BaseVars fenv' ro -> Env (NewIdx fenv') fenv
partialDoSubstituteOutput = go Env.Empty
  where
    go :: Env (NewIdx fenv') fenv1 -> PartialDoOutput fenv1 fenv2 t' r' -> OutputEnv t' ro' -> BaseVars fenv' ro' -> Env (NewIdx fenv') fenv2
    go env (PartialDoOutputPair o1 o2) (OutputEnvPair e1 e2) (TupRpair v1 v2)
      = go (go env o1 e1 v1) o2 e2 v2
    go env PartialDoOutputUnit OutputEnvIgnore TupRunit
      = env
    go env (PartialDoOutputScalar _) (OutputEnvScalar _) (TupRpair (TupRsingle v1) (TupRsingle v2))
      = env `Push` NewIdxJust (varIdx v2) `Push` NewIdxJust (varIdx v1)
    go env (PartialDoOutputShared _) OutputEnvShared (TupRpair (TupRpair (TupRsingle v1) (TupRsingle v2)) (TupRsingle v3))
      = env `Push` NewIdxJust (varIdx v3) `Push` NewIdxJust (varIdx v2) `Push` NewIdxJust (varIdx v1)
    go env (PartialDoOutputUnique _) OutputEnvUnique (TupRpair (TupRpair (TupRpair (TupRsingle v1) (TupRsingle v2)) (TupRsingle v3)) (TupRsingle v4))
      = env `Push` NewIdxJust (varIdx v4) `Push` NewIdxJust (varIdx v3) `Push` NewIdxJust (varIdx v2) `Push` NewIdxJust (varIdx v1)
    -- Unique buffer written to shared buffer destination
    go env (PartialDoOutputUnique _) OutputEnvShared (TupRpair (TupRpair (TupRsingle v1) (TupRsingle v2)) (TupRsingle v3))
      = env `Push` NewIdxJust (varIdx v3) `Push` NewIdxJust (varIdx v2) `Push` NewIdxJust (varIdx v1) `Push` NewIdxNoResolver
    -- Shared buffer written to unique buffer destination
    go _   (PartialDoOutputShared _) OutputEnvUnique _
      = internalError "Cannot write shared buffer to unique buffer destination"
    go _ _ _ _ = internalError "Mismatch in PartialDoOutput and OutputEnv"

partialDoSubstituteConvertEnv :: forall genv fenv1 fenv2 fenv'. ConvertEnv genv fenv1 fenv2 -> FutureEnv fenv' genv -> Env (NewIdx fenv') fenv1 -> Env (NewIdx fenv') fenv2
partialDoSubstituteConvertEnv ConvertEnvNil _ env = env
partialDoSubstituteConvertEnv (ConvertEnvSeq c1 c2) fenv env = partialDoSubstituteConvertEnv c2 fenv $ partialDoSubstituteConvertEnv c1 fenv env
partialDoSubstituteConvertEnv (ConvertEnvAcquire (Acquire m var)) fenv env
  | Just (FutureBuffer _ _ _ read mWrite) <- prjPartial (varIdx var) fenv =
    let
      lock
        | In <- m = read
        | Just write <- mWrite = write
        | otherwise = internalError "Requested write access to a buffer, but the FutureBuffer only has read permissions"
      (signal, resolver)
        | Borrow s r <- lock = (NewIdxJust s, NewIdxJust r)
        | Move   s   <- lock = (NewIdxJust s, NewIdxNoResolver)
    in
      env `Push` signal `Push` resolver
  | otherwise = internalError "Requested access to a buffer, but the FutureBuffer was not found in the environment"
partialDoSubstituteConvertEnv (ConvertEnvFuture var) fenv env
  | Just future <- prjPartial (varIdx var) fenv =
    let
      (signal, ref)
        | FutureScalar _ s r     <- future = (s, r)
        | FutureBuffer _ s r _ _ <- future = (s, r)
    in
      env `Push` NewIdxJust signal `Push` NewIdxJust ref
  | otherwise = internalError $ "Requested access to a variable " % fromString (show $ idxToInt $ varIdx var) % " of type " % fromString (show $ prettyGroundR $ varType var) % ", but the Future was not found in the environment"

data DeclareInput fenv genv' t where
  DeclareInput :: fenv :> fenv'
               -> BLeftHandSide (Input t) fenv fenv'
               -> (forall fenv''. fenv' :> fenv'' -> FutureEnv fenv'' genv')
               -> DeclareInput fenv genv' t

declareInput
  :: forall t fenv genv genv'.
     FutureEnv fenv genv
  -> GLeftHandSide t genv genv'
  -> DeclareInput fenv genv' t
declareInput = \fenv -> go (\k -> mapPartialEnv (weaken k) fenv)
  where
    go :: forall fenv' genv1 genv2 s. (forall fenv''. fenv' :> fenv'' -> FutureEnv fenv'' genv1) -> GLeftHandSide s genv1 genv2 -> DeclareInput fenv' genv2 s
    go fenv (LeftHandSidePair lhs1 lhs2)
      | DeclareInput k1 lhs1' fenv1 <- go fenv  lhs1
      , DeclareInput k2 lhs2' fenv2 <- go fenv1 lhs2
      = DeclareInput (k2 .> k1) (LeftHandSidePair lhs1' lhs2') fenv2
    go fenv (LeftHandSideWildcard grounds) = DeclareInput weakenId (LeftHandSideWildcard $ inputR grounds) fenv
    go fenv (LeftHandSideSingle (GroundRscalar tp)) -- Scalar
      | Refl <- inputSingle $ GroundRscalar tp
      = DeclareInput
          (weakenSucc $ weakenSucc weakenId)
          (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle (BaseRref $ GroundRscalar tp))
          (\k' -> PPush (fenv $ weakenSucc $ weakenSucc k')
                    $ FutureScalar
                        tp
                        (k' >:> SuccIdx ZeroIdx)
                        (k' >:> ZeroIdx))
    go fenv (LeftHandSideSingle (GroundRbuffer tp)) -- Buffer
      = DeclareInput
          (weakenSucc $ weakenSucc weakenId)
          (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle (BaseRref $ GroundRbuffer tp))
          (\k' -> PPush (fenv $ weakenSucc $ weakenSucc k')
                    $ FutureBuffer
                        tp
                        (k' >:> SuccIdx ZeroIdx)
                        (k' >:> ZeroIdx)
                        (Move (k' >:> SuccIdx ZeroIdx))
                        Nothing)

data DeclareOutput kernel fenv t where
  DeclareOutput :: fenv :> fenv'
                -> BLeftHandSide (Output t) fenv fenv'
                -> fenv' :> fenv''
                -> (UniformSchedule kernel fenv'' -> UniformSchedule kernel fenv')
                -> OutputEnv t r
                -> (forall fenv'''. fenv'' :> fenv''' -> BaseVars fenv''' r)
                -> DeclareOutput kernel fenv t

data DeclareOutputInternal kernel fenv' t where
  DeclareOutputInternal :: fenv' :> fenv''
                        -> (UniformSchedule kernel fenv'' -> UniformSchedule kernel fenv')
                        -> OutputEnv t r
                        -> (forall fenv'''. fenv'' :> fenv''' -> BaseVars fenv''' r)
                        -> DeclareOutputInternal kernel fenv' t

declareOutput
  :: forall kernel fenv t.
     GroundsR t
  -> DeclareOutput kernel fenv t
declareOutput grounds
  | DeclareVars lhs k1 value <- declareVars $ outputR grounds
  , DeclareOutputInternal k2 instr outputEnv outputVars <- go weakenId grounds (value weakenId)
  = DeclareOutput k1 lhs k2 instr outputEnv outputVars
  where
    go :: fenv1 :> fenv2 -> GroundsR s -> BaseVars fenv1 (Output s) -> DeclareOutputInternal kernel fenv2 s
    go _ TupRunit TupRunit
      = DeclareOutputInternal
          weakenId
          id
          OutputEnvIgnore
          $ const TupRunit
    go k (TupRpair gL gR) (TupRpair vL vR)
      | DeclareOutputInternal kL instrL outL varsL' <- go k         gL vL
      , DeclareOutputInternal kR instrR outR varsR' <- go (kL .> k) gR vR
      = DeclareOutputInternal
          (kR .> kL)
          (instrL . instrR)
          (OutputEnvPair outL outR)
          $ \k' -> varsL' (k' .> kR) `TupRpair` varsR' k'
    go k (TupRsingle (GroundRbuffer _)) (TupRsingle signal `TupRpair` TupRsingle ref)
      = DeclareOutputInternal
          (weakenSucc $ weakenSucc weakenId)
          (Alet lhsSignal NewSignal)
          OutputEnvShared
          $ \k' ->
            let k'' = k' .> weakenSucc' (weakenSucc' k)
            in TupRsingle (Var BaseRsignalResolver $ weaken k' ZeroIdx)
                `TupRpair` TupRsingle (weaken k'' signal)
                `TupRpair` TupRsingle (weaken k'' ref)
    go k (TupRsingle (GroundRscalar tp)) vars
      | Refl <- inputSingle $ GroundRscalar tp
      , TupRsingle signal `TupRpair` TupRsingle ref <- vars
      = DeclareOutputInternal
          weakenId
          id
          (OutputEnvScalar tp)
          $ \k' ->
            let k'' = k' .> k
            in TupRsingle (weaken k'' signal)
                `TupRpair` TupRsingle (weaken k'' ref)
    go _ _ _ = internalError "Mismatch between GroundsR and output variables"

data DeclareBinding kernel fenv genv' t where
  DeclareBinding :: fenv :> fenv'
                 -> (UniformSchedule kernel fenv' -> UniformSchedule kernel fenv)
                 -> OutputEnv t r
                 -> (forall fenv''. fenv' :> fenv'' -> BaseVars fenv'' r)
                 -> (forall fenv''. fenv' :> fenv'' -> FutureEnv fenv'' genv')
                 -- A list of signals which will be resolved in this binding.
                 -- If the body of a 'let' statement directly waits on all
                 -- these signals, then we can execute the statement serially.
                 -- If not, then we execute it in parallel: the body might be
                 -- able to do some work before the binding has finished.
                 -> (forall fenv''. fenv' :> fenv'' -> Maybe [Idx fenv'' Signal])
                 -> DeclareBinding kernel fenv genv' t

declareBinding
  :: forall kernel fenv genv genv' bnd ret retR.
     OutputEnv ret retR
  -> BaseVars fenv retR
  -> FutureEnv fenv genv
  -> GLeftHandSide bnd genv genv'
  -> TupR (Destination ret) bnd
  -> TupR Uniqueness bnd
  -> DeclareBinding kernel fenv genv' bnd
declareBinding retOutputEnv retOutputVars = \fenv -> go weakenId (\k -> mapPartialEnv (weaken k) fenv)
  where
    go :: forall fenv' genv1 genv2 t. (fenv :> fenv') -> (forall fenv''. fenv' :> fenv'' -> FutureEnv fenv'' genv1) -> GLeftHandSide t genv1 genv2 -> TupR (Destination ret) t -> TupR Uniqueness t -> DeclareBinding kernel fenv' genv2 t
    go k fenv (LeftHandSidePair lhs1 lhs2) (TupRpair dest1 dest2) (TupRpair u1 u2)
      | DeclareBinding k1 instr1 out1 vars1 fenv1 signals1 <- go k fenv  lhs1 dest1 u1
      , DeclareBinding k2 instr2 out2 vars2 fenv2 signals2 <- go (k1 .> k) fenv1 lhs2 dest2 u2
      = DeclareBinding (k2 .> k1) (instr1 . instr2) (OutputEnvPair out1 out2) (\k' -> TupRpair (vars1 $ k' .> k2) (vars2 k')) fenv2 (\k' -> (++) <$> signals1 (k' .> k2) <*> signals2 k')
    go _ fenv (LeftHandSideWildcard _) _ _
      = DeclareBinding
          weakenId
          id
          OutputEnvIgnore
          (const TupRunit)
          fenv
          (const $ Just [])
    go k fenv (LeftHandSideSingle _) (TupRsingle (DestinationReuse idx)) _
      | OutputEnvAndVars outputEnv outputVars <- prjDest retOutputEnv retOutputVars idx
      = DeclareBinding
          weakenId
          id
          outputEnv
          (\k' -> mapTupR (weaken (k' .> k)) outputVars)
          (PNone . fenv)
          (const Nothing)
    go _ fenv (LeftHandSideSingle (GroundRscalar tp)) _ _
      = DeclareBinding
          (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId)
          instr
          (OutputEnvScalar tp)
          (\k' -> TupRpair
                    (TupRsingle $ Var BaseRsignalResolver $ k' >:> idx2)
                    (TupRsingle $ Var (BaseRrefWrite $ GroundRscalar tp) $ k' >:> idx0))
          (\k' -> PPush (fenv $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc k')
                    $ FutureScalar
                        tp
                        (k' >:> idx3)
                        (k' >:> idx1))
          (\k' -> Just [k' >:> idx3])
      where
        instr
          = Alet lhsSignal NewSignal
          . Alet (lhsRef $ GroundRscalar tp) (NewRef $ GroundRscalar tp)

        idx0 = ZeroIdx
        idx1 = SuccIdx ZeroIdx
        idx2 = SuccIdx $ SuccIdx ZeroIdx
        idx3 = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    go _ fenv (LeftHandSideSingle (GroundRbuffer tp)) _ (TupRsingle Unique)
      = DeclareBinding
          (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId)
          instr
          OutputEnvUnique
          (\k' -> TupRpair
                    ( TupRpair
                      ( TupRpair
                        (TupRsingle $ Var BaseRsignalResolver $ k' >:> idx6)
                        (TupRsingle $ Var BaseRsignalResolver $ k' >:> idx4)
                      )
                      (TupRsingle $ Var BaseRsignalResolver $ k' >:> idx2)
                    )
                    (TupRsingle $ Var (BaseRrefWrite $ GroundRbuffer tp) $ k' >:> idx0))
          (\k' -> PPush (fenv $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc k')
                    $ FutureBuffer
                        tp
                        (k' >:> idx7)
                        (k' >:> idx1)
                        (Move (k' >:> idx5))
                        $ Just $ Move $ k' >:> idx3)
          (\k' -> Just [k' >:> idx7, k' >:> idx5, k' >:> idx3])
      where
        instr
          = Alet lhsSignal NewSignal -- Signal to grant access to the reference (idx7, idx6)
          . Alet lhsSignal NewSignal -- Signal to grant read access to the array (idx5, idx4)
          . Alet lhsSignal NewSignal -- Signal to grant write access to the array (idx3, idx2)
          . Alet (lhsRef $ GroundRbuffer tp) (NewRef $ GroundRbuffer tp) -- (idx1, idx0)

        idx0 = ZeroIdx
        idx1 = SuccIdx ZeroIdx
        idx2 = SuccIdx $ SuccIdx ZeroIdx
        idx3 = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
        idx4 = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
        idx5 = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
        idx6 = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
        idx7 = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    go _ fenv (LeftHandSideSingle (GroundRbuffer tp)) _ (TupRsingle Shared)
      = DeclareBinding
          (weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId)
          instr
          OutputEnvShared
          (\k' -> TupRpair
                    ( TupRpair
                      (TupRsingle $ Var BaseRsignalResolver $ k' >:> idx4)
                      (TupRsingle $ Var BaseRsignalResolver $ k' >:> idx2)
                    )
                    (TupRsingle $ Var (BaseRrefWrite $ GroundRbuffer tp) $ k' >:> idx0))
          (\k' -> PPush (fenv $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc k')
                    $ FutureBuffer
                        tp
                        (k' >:> idx5)
                        (k' >:> idx1)
                        (Move (k' >:> idx3))
                        Nothing)
          (\k' -> Just [k' >:> idx5, k' >:> idx3])
      where
        instr
          = Alet lhsSignal NewSignal
          . Alet lhsSignal NewSignal
          . Alet (lhsRef $ GroundRbuffer tp) (NewRef $ GroundRbuffer tp)

        idx0 = ZeroIdx
        idx1 = SuccIdx ZeroIdx
        idx2 = SuccIdx $ SuccIdx ZeroIdx
        idx3 = SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
        idx4 = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
        idx5 = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    go k fenv lhs@LeftHandSidePair{} (TupRsingle DestinationNew) uniquenesses
      = go k fenv lhs (TupRsingle DestinationNew `TupRpair` TupRsingle DestinationNew) uniquenesses
    go k fenv lhs@LeftHandSidePair{} destinations (TupRsingle Shared)
      = go k fenv lhs destinations (TupRsingle Shared `TupRpair` TupRsingle Shared)
    go _ _    LeftHandSidePair{} (TupRsingle DestinationReuse{}) _ = internalError "Pair impossible"

    prjDest :: OutputEnv ret' retR' -> BaseVars fenv retR' -> TupleIdx ret' t -> OutputEnvAndVars fenv t
    prjDest outputEnv outputVars TupleIdxSelf = OutputEnvAndVars outputEnv outputVars
    prjDest (OutputEnvPair o _) (TupRpair v _) (TupleIdxLeft  idx) = prjDest o v idx
    prjDest (OutputEnvPair _ o) (TupRpair _ v) (TupleIdxRight idx) = prjDest o v idx
    prjDest _ _ _ = internalError "Pair impossible"

data OutputEnvAndVars fenv t where
  OutputEnvAndVars :: OutputEnv t r -> BaseVars fenv r -> OutputEnvAndVars fenv t

unionLeftHandSides :: LeftHandSide s t env env1' -> LeftHandSide s t env env2' -> Exists (LeftHandSide s t env)
unionLeftHandSides = unionLeftHandSides'

unionLeftHandSides' :: LeftHandSide s t env1 env1' -> LeftHandSide s t env2 env2' -> Exists (LeftHandSide s t env3)
unionLeftHandSides' (LeftHandSideSingle tp)  _                        = Exists $ LeftHandSideSingle tp
unionLeftHandSides' _                        (LeftHandSideSingle tp)  = Exists $ LeftHandSideSingle tp
unionLeftHandSides' (LeftHandSideWildcard _) l                        = rebuildLHS l
unionLeftHandSides' l                        (LeftHandSideWildcard _) = rebuildLHS l
unionLeftHandSides' (LeftHandSidePair a1 a2) (LeftHandSidePair b1 b2)
  | Exists a <- unionLeftHandSides' a1 b1
  , Exists b <- unionLeftHandSides' a2 b2 = Exists $ LeftHandSidePair a b

-- The second LHS should be a sub environment of the first, i.e. it may only contain bindings which are also present in the second.
environmentForSubLHS :: PartialEnv f env1 -> LeftHandSide s t env env1 -> LeftHandSide s t env env2 -> PartialEnv f env2
environmentForSubLHS = \env lhs1 lhs2 -> go id lhs1 lhs2 env
  where
    go :: (PartialEnv f env1 -> PartialEnv f env2) -> LeftHandSide s t env1 env1' -> LeftHandSide s t env2 env2' -> PartialEnv f env1' -> PartialEnv f env2'
    go g (LeftHandSidePair a1 a2) (LeftHandSidePair b1 b2) = g2
      where
        g1 = go g  a1 b1
        g2 = go g1 a2 b2
    go g (LeftHandSideSingle _) (LeftHandSideSingle _) = \case
      PEnd        -> PEnd
      PPush env a -> PPush (g env) a
      PNone env   -> PNone (g env)
    go g lhs (LeftHandSideWildcard _) = g . remove lhs
    go _ _ _ = internalError "Second LHS is not a sub environment of the first LHS"

    remove :: LeftHandSide s t env env' -> PartialEnv f env' -> PartialEnv f env
    remove = flip environmentDropLHS

environmentDropLHS :: PartialEnv f env1 -> LeftHandSide s t env env1 -> PartialEnv f env
environmentDropLHS env (LeftHandSideWildcard _) = env
environmentDropLHS env (LeftHandSideSingle _)   = partialEnvTail env
environmentDropLHS env (LeftHandSidePair l1 l2) = environmentDropLHS (environmentDropLHS env l2) l1
