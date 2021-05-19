{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
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
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.Substitution
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Schedule.Uniform (
) where

import Prelude hiding (read)

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import qualified Data.Array.Accelerate.AST.IdxSet       as IdxSet
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.AST.Environment
import qualified Data.Array.Accelerate.AST.Partitioned  as C
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Operation.Substitution (strengthenArrayInstr)
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import Data.Maybe
import Data.List
import qualified Data.Set                               as S
import GHC.Stack

instance IsExecutableAcc exe => Sink' (UniformSchedule exe) where
  weaken' _ Return                        = Return
  weaken' k (Alet lhs b s)                
    | Exists lhs' <- rebuildLHS lhs       = Alet lhs' (weaken k b) (weaken' (sinkWithLHS lhs lhs' k) s)
  weaken' k (Effect effect s)             = Effect (weaken' k effect) (weaken' k s)
  weaken' k (Acond cond true false s)     = Acond (weaken k cond) (weaken' k true) (weaken' k false) (weaken' k s)
  weaken' k (Awhile io cond step input s) = Awhile io (weaken k cond) (weaken k step) (mapTupR (weaken k) input) (weaken' k s)
  weaken' k (Fork s1 s2)                  = Fork (weaken' k s1) (weaken' k s2)

instance IsExecutableAcc exe => Sink (UniformScheduleFun exe) where
  weaken k (Slam lhs f)
    | Exists lhs' <- rebuildLHS lhs = Slam lhs' $ weaken (sinkWithLHS lhs lhs' k) f
  weaken k (Sbody s)    = Sbody $ weaken' k s

instance Sink Binding where
  weaken k (Compute e)         = Compute $ mapArrayInstr (weaken k) e
  weaken _ (NewSignal)         = NewSignal
  weaken _ (NewRef r)          = NewRef r
  weaken k (Alloc shr tp size) = Alloc shr tp $ mapTupR (weaken k) size
  weaken _ (Use tp buffer)     = Use tp buffer
  weaken k (Unit var)          = Unit $ weaken k var
  weaken k (RefRead ref)       = RefRead $ weaken k ref

instance IsExecutableAcc exe => Sink' (Effect exe) where
  weaken' k (Exec exe) = Exec $ runIdentity $ reindexExecPartial (weakenReindex k) exe
  weaken' k (SignalAwait vars) = SignalAwait $ map (weaken k) vars
  weaken' k (SignalResolve vars) = SignalResolve $ map (weaken k) vars
  weaken' k (RefWrite ref value) = RefWrite (weaken k ref) (weaken k value)

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

data Strengthen env env' where
  StrengthenId :: Strengthen env env
  StrengthenSucc :: Strengthen env env' -> Strengthen (env, t) env'

strengthenIdx :: Strengthen env env' -> env :?> env'
strengthenIdx StrengthenId       idx           = Just idx
strengthenIdx (StrengthenSucc k) (SuccIdx idx) = strengthenIdx k idx
strengthenIdx (StrengthenSucc _) ZeroIdx       = Nothing

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
-}
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

{-

awaitFuture :: FEnv senv genv -> GroundVars genv t -> (forall senv'. senv :> senv' -> BaseVars senv' t -> UniformSchedule exe senv') -> UniformSchedule exe senv
awaitFuture env1 vars1
  = let (symbols, res) = go env1 vars1
  where
    go :: FEnv senv genv -> GroundVars genv t -> (forall senv'. senv :> senv' -> BaseVars senv' t -> UniformSchedule exe senv') -> ([Var senv Signal], UniformSchedule exe senv)
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

data Acquire genv t where
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
          -> Acquire genv (Signal, SignalResolver)

data ConvertEnv genv fenv fenv' where
  ConvertEnvNil     :: ConvertEnv genv fenv fenv

  ConvertEnvSeq     :: ConvertEnv genv fenv1 fenv2
                    -> ConvertEnv genv fenv2 fenv3
                    -> ConvertEnv genv fenv1 fenv3

  ConvertEnvAcquire :: Acquire genv (Signal, SignalResolver)
                    -> ConvertEnv genv fenv ((fenv, Signal), SignalResolver)

  ConvertEnvFuture  :: GroundVar genv e
                    -> ConvertEnv genv fenv ((fenv, Signal), Ref e)

data OutputEnv fenv fenv' t r where
  OutputEnvPair     :: OutputEnv fenv1 fenv2 t  r
                    -> OutputEnv fenv2 fenv3 t' r'
                    -> OutputEnv fenv1 fenv3 (t, t') (r, r')

  -- First SignalResolver grants read access, second guarantees that all reads have been finished.
  -- Together they thus grant write access.
  OutputEnvUnique   :: BLeftHandSide ((SignalResolver, SignalResolver), OutputRef (Buffer t)) fenv fenv'
                    -> GroundR (Buffer t)
                    -> OutputEnv fenv  fenv' (Buffer t) ((SignalResolver, SignalResolver), OutputRef (Buffer t))

  -- Scalar values or shared buffers
  OutputEnvShared   :: BLeftHandSide (SignalResolver, OutputRef t) fenv fenv'
                    -> GroundR t
                    -> OutputEnv fenv  fenv' t (SignalResolver, OutputRef t)

  OutputEnvUnit     :: OutputEnv fenv  fenv () ()

data OutputVars t r where
  OutputVarsPair :: OutputVars t  r
                 -> OutputVars t' r'
                 -> OutputVars (t, t') (r, r')

  OutputVarsUnique :: OutputVars (Buffer t) ((SignalResolver, SignalResolver), OutputRef (Buffer t))

  OutputVarsShared :: OutputVars t (SignalResolver, OutputRef t)

  -- No need to propagate the output, as we reused the same variables (using Destination in PartialDeclare)
  -- Also used for Unit
  OutputVarsIgnore :: OutputVars t r

data DeclareOutput fenv t where
  DeclareOutput :: OutputEnv fenv fenv' t r
                -> fenv :> fenv'
                -> (forall fenv'' . fenv' :> fenv'' -> BaseVars fenv'' r)
                -> DeclareOutput fenv t

declareOutput :: forall fenv t.
                 GroundsR t
              -> Uniquenesses t
              -> DeclareOutput fenv t
declareOutput (TupRsingle tp)  (TupRsingle Unique)   = DeclareOutput env subst value
  where
    env = OutputEnvUnique lhs tp
    lhs = LeftHandSidePair lhsSignalResolver lhsSignalResolver `LeftHandSidePair` LeftHandSideSingle (BaseRrefWrite tp)

    subst = weakenSucc $ weakenSucc $ weakenSucc weakenId

    value :: forall fenv''. (((fenv, SignalResolver), SignalResolver), OutputRef t) :> fenv'' -> BaseVars fenv'' ((SignalResolver, SignalResolver), OutputRef t)
    value k = (TupRsingle (Var BaseRsignalResolver $ k >:> SuccIdx (SuccIdx ZeroIdx)) `TupRpair` TupRsingle (Var BaseRsignalResolver $ k >:> SuccIdx ZeroIdx)) `TupRpair` TupRsingle (Var (BaseRrefWrite tp) (k >:> ZeroIdx))
declareOutput (TupRsingle tp)  _                     = DeclareOutput env subst value
  where
    env = OutputEnvShared lhs tp
    lhs = lhsSignalResolver `LeftHandSidePair` LeftHandSideSingle (BaseRrefWrite tp)

    subst = weakenSucc $ weakenSucc weakenId

    value :: forall fenv''. ((fenv, SignalResolver), OutputRef t) :> fenv'' -> BaseVars fenv'' (SignalResolver, OutputRef t)
    value k = TupRsingle (Var BaseRsignalResolver $ k >:> SuccIdx ZeroIdx) `TupRpair` TupRsingle (Var (BaseRrefWrite tp) (k >:> ZeroIdx))
declareOutput (TupRpair t1 t2) us
  | DeclareOutput env1 subst1 value1 <- declareOutput t1 u1
  , DeclareOutput env2 subst2 value2 <- declareOutput t2 u2 = DeclareOutput (OutputEnvPair env1 env2) (subst2 .> subst1) (\k -> value1 (k .> subst2) `TupRpair` value2 k)
  where
    (u1, u2) = pairUniqueness us
declareOutput TupRunit         _                     = DeclareOutput OutputEnvUnit weakenId (const TupRunit)

writeOutput :: OutputEnv fenv fenv' t r -> BaseVars fenv'' r -> BaseVars fenv'' t -> UniformSchedule (Cluster op) fenv''
writeOutput outputEnv outputVars valueVars = go outputEnv outputVars valueVars Return
  where
    go :: OutputEnv fenv fenv' t r -> BaseVars fenv'' r -> BaseVars fenv'' t -> UniformSchedule (Cluster op) fenv'' -> UniformSchedule (Cluster op) fenv''
    go OutputEnvUnit _ _ = id
    go (OutputEnvPair o1 o2) (TupRpair r1 r2) (TupRpair v1 v2) = go o1 r1 v1 . go o2 r2 v2
    go (OutputEnvShared _ _) (TupRpair (TupRsingle signal) (TupRsingle ref)) (TupRsingle v)
      = Effect (RefWrite ref v)
      . Effect (SignalResolve [varIdx signal])
    go (OutputEnvUnique _ _) (TupRpair (TupRpair (TupRsingle s1) (TupRsingle s2)) (TupRsingle ref)) (TupRsingle v)
      = Effect (RefWrite ref v)
      . Effect (SignalResolve [varIdx s1])
      . Effect (SignalResolve [varIdx s2])

data ReEnv genv fenv where
  ReEnvEnd  :: ReEnv genv fenv
  ReEnvSkip :: ReEnv genv fenv -> ReEnv (genv, t) fenv
  ReEnvKeep :: ReEnv genv fenv -> ReEnv (genv, t) (fenv, t)

reEnvIdx :: ReEnv genv fenv -> genv :?> fenv
reEnvIdx (ReEnvKeep _) ZeroIdx = Just ZeroIdx
reEnvIdx (ReEnvKeep r) (SuccIdx ix) = SuccIdx <$> reEnvIdx r ix
reEnvIdx (ReEnvSkip r) (SuccIdx ix) = reEnvIdx r ix
reEnvIdx _             _            = Nothing
{-
data ConvertEnvRead op genv fenv1 where
  ConvertEnvRead :: (UniformSchedule (Cluster op) fenv2 -> UniformSchedule (Cluster op) fenv1)
                 -> (forall fenv3. ReEnv genv fenv2 fenv3 -> ReEnv genv fenv1 fenv3) -- TODO: This doesn't work. We need to assure that genv and fenv are in the same order
                 -> fenv1 :> fenv2
                 -> ConvertEnvRead op genv fenv1
-}
-- Void data type with orphan type argument.
-- Used to mark that a variable of the ground environment is used.
--
data FutureRef fenv t = FutureRef (BaseVar fenv (Ref t))

convertEnvRefs :: forall genv fenv fenv'. ConvertEnv genv fenv fenv' -> PartialEnv (FutureRef fenv') genv
convertEnvRefs env = partialEnvFromList const $ snd $ go weakenId env []
  where
    go :: fenv2 :> fenv' -> ConvertEnv genv fenv1 fenv2 -> [EnvBinding (FutureRef fenv') genv] -> (fenv1 :> fenv', [EnvBinding (FutureRef fenv') genv])
    go k ConvertEnvNil                 accum = (k, accum)
    go k (ConvertEnvSeq e1 e2)         accum = (k1, bs')
      where
        (k2, bs) = go k e2 accum
        (k1, bs') = go k2 e1 bs
    go k (ConvertEnvAcquire _)         accum = (weakenSucc $ weakenSucc k, accum)
    go k (ConvertEnvFuture (Var tp ix)) accum = (weakenSucc $ weakenSucc k, EnvBinding ix (FutureRef $ Var (BaseRref tp) $ k >:> ZeroIdx) : accum)

data Reads exe genv fenv where
  Reads :: ReEnv genv fenv'
        -> (fenv :> fenv')
        -> (UniformSchedule exe fenv' -> UniformSchedule exe fenv)
        -> Reads exe genv fenv

readRefs :: PartialEnv (FutureRef fenv) genv -> Reads exe genv fenv
readRefs PEnd = Reads ReEnvEnd weakenId id
readRefs (PPush env (FutureRef (Var tp idx)))
  | Reads r k f <- readRefs env =
    let
      tp' = case tp of
        BaseRref t -> BaseRground t
        _ -> error "Impossible Ref base type"
      r' = ReEnvKeep r
      k' = weakenSucc' k
      f' = f . Alet (LeftHandSideSingle tp') (RefRead $ Var tp $ k >:> idx)
    in
      Reads r' k' f'
readRefs (PNone env)
  | Reads r k f <- readRefs env = Reads (ReEnvSkip r) k f

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

convertEnvVar :: Var AccessGroundR genv t -> Exists (ConvertEnv genv fenv)
convertEnvVar (Var (AccessGroundRscalar   tp) ix) = Exists $ ConvertEnvFuture $ Var (GroundRscalar tp) ix
convertEnvVar (Var (AccessGroundRbuffer m tp) ix) = Exists $ ConvertEnvFuture var `ConvertEnvSeq` ConvertEnvAcquire (Acquire m var)
  where
    var = Var (GroundRbuffer tp) ix

lhsSignalResolver :: BLeftHandSide SignalResolver fenv (fenv, SignalResolver)
lhsSignalResolver = LeftHandSideSingle BaseRsignalResolver

-- In PartialDeclare, we try to reuse the return address of the computation,
-- if this variable will be returned.
--
data Destination r t where
  DestinationNew   :: Destination r t
  DestinationReuse :: TupleIdx r t -> Destination r t

data TupleIdx s t where
  TupleIdxLeft  :: TupleIdx l t -> TupleIdx (l, r) t
  TupleIdxRight :: TupleIdx r t -> TupleIdx (l, r) t
  TupleIdxSelf  :: TupleIdx t t

data PartialSchedule op genv t where
  PartialDo     :: OutputEnv () fenv t r
                -> ConvertEnv genv fenv fenv'
                -> UniformSchedule (Cluster op) fenv'
                -> PartialSchedule op genv t

  -- Returns a tuple of variables. Note that (some of) these
  -- variables may already have been resolved, as they may be
  -- annotated in PartialDeclare. We allow variables to unify,
  -- to prevent additional signals and references to be created.
  --
  PartialReturn :: Uniquenesses t
                -> GroundVars genv t
                -> PartialSchedule op genv t

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
                -> PartialSchedule op genv  bnd
                -> PartialSchedule op genv' t
                -> PartialSchedule op genv  t

  PartialAcond  :: SyncEnv genv -- Stored for efficiency reasons to avoid recomputing it.
                -> ExpVar genv PrimBool
                -> PartialSchedule op genv t
                -> PartialSchedule op genv t
                -> PartialSchedule op genv t

  PartialAwhile :: SyncEnv genv
                -> Uniquenesses t
                -> PartialScheduleFun op genv (t -> PrimBool)
                -> PartialScheduleFun op genv (t -> t)
                -> GroundVars genv t
                -> PartialSchedule op genv t

partialDeclare  :: GLeftHandSide bnd genv genv'
                -> TupR (Destination t) bnd
                -> Uniquenesses bnd
                -> PartialSchedule op genv  bnd
                -> PartialSchedule op genv' t
                -> PartialSchedule op genv  t
partialDeclare lhs dest us bnd sched = PartialDeclare sync lhs dest us bnd sched
  where
    sync = unionPartialEnv max (syncEnv bnd) (weakenSyncEnv lhs $ syncEnv sched)

partialAcond    :: ExpVar genv PrimBool
                -> PartialSchedule op genv t
                -> PartialSchedule op genv t
                -> PartialSchedule op genv t
partialAcond cond t f = PartialAcond sync cond t f
  where
    sync = unionPartialEnv max (syncEnv t) (syncEnv f)

partialAwhile   :: Uniquenesses t
                -> PartialScheduleFun op genv (t -> PrimBool)
                -> PartialScheduleFun op genv (t -> t)
                -> GroundVars genv t
                -> PartialSchedule op genv t
partialAwhile us cond f vars = PartialAwhile sync us cond f vars
  where
    sync = unionPartialEnv max (syncEnvFun cond) $ unionPartialEnv max (syncEnvFun f) $ variablesToSyncEnv us vars

data PartialScheduleFun op genv t where
  Plam  :: GLeftHandSide s genv genv'
        -> PartialScheduleFun op genv' t
        -> PartialScheduleFun op genv (s -> t)

  Pbody :: PartialSchedule    op genv  t
        -> PartialScheduleFun op genv  t

data MaybeVar genv t where
  NoVars    :: MaybeVar genv t
  ReturnVar :: GroundVar genv t -> MaybeVar genv t
type MaybeVars genv = TupR (MaybeVar genv)

weakenMaybeVar :: LeftHandSide s t genv genv' -> MaybeVar genv' u -> MaybeVar genv u
weakenMaybeVar _ NoVars = NoVars
weakenMaybeVar (LeftHandSideWildcard _) v = v
weakenMaybeVar (LeftHandSideSingle _) (ReturnVar (Var t ix)) = case ix of
  SuccIdx ix' -> ReturnVar $ Var t ix'
  ZeroIdx     -> NoVars
weakenMaybeVar (LeftHandSidePair l1 l2) v = weakenMaybeVar l1 $ weakenMaybeVar l2 v

weakenMaybeVars :: LeftHandSide s t genv genv' -> MaybeVars genv' u -> MaybeVars genv u
weakenMaybeVars lhs = mapTupR (weakenMaybeVar lhs)

-- We can only reuse the resulting address of a variable if the local binding is not used elsewhere.
-- For instance, we may reuse the return address for x in `let x = .. in x`,
-- but that is not allowed in `let x = .. in let y = .. x .. in (x, y)`
-- or `let x = .. in (x, x)`.
-- This function removes a set of variables and can be used to remove for instance the set of variables
-- used in another binding or effect.
removeMaybeVars :: forall genv u. MaybeVars genv u -> IdxSet genv -> MaybeVars genv u
removeMaybeVars vars remove = mapTupR f vars
  where
    f :: MaybeVar genv t -> MaybeVar genv t
    f var@(ReturnVar (Var _ idx))
      | idx `IdxSet.member` remove = NoVars
      | otherwise         = var
    f NoVars = NoVars

lhsDestination :: GLeftHandSide t genv genv' -> MaybeVars genv' u -> TupR (Destination u) t
lhsDestination (LeftHandSidePair l1 l2) vars = lhsDestination l1 (weakenMaybeVars l2 vars) `TupRpair` lhsDestination l2 vars
lhsDestination (LeftHandSideWildcard t) _    = mapTupR (const DestinationNew) t
lhsDestination (LeftHandSideSingle _)   vars = case findVar vars of
    Just ix -> TupRsingle $ DestinationReuse ix
    Nothing -> TupRsingle DestinationNew
  where
    findVar :: MaybeVars (env, t) s -> Maybe (TupleIdx s t)
    findVar (TupRpair a b) = case (findVar a, findVar b) of
      (Just i , _     ) -> Just $ TupleIdxLeft i
      (Nothing, Just i) -> Just $ TupleIdxRight i
      _                 -> Nothing
    findVar (TupRsingle (ReturnVar (Var _ ZeroIdx))) = Just TupleIdxSelf
    findVar TupRunit = Nothing -- Should be unreachable

joinVars :: MaybeVars genv t -> MaybeVars genv t -> MaybeVars genv t
joinVars m@(TupRsingle (ReturnVar (Var _ x))) (TupRsingle (ReturnVar (Var _ y)))
  | x == y = m
joinVars (TupRpair x1 x2) (TupRpair y1 y2) = joinVars x1 y1 `TupRpair` joinVars x2 y2
joinVars TupRunit         _                = TupRunit
joinVars _                TupRunit         = TupRunit
joinVars _                _                = TupRsingle NoVars

data Exists' (a :: (* -> * -> *) -> *) where
  Exists' :: a m -> Exists' a

partialSchedule :: forall op genv1 t1. C.PartitionedAcc op genv1 t1 -> PartialSchedule op genv1 t1
partialSchedule = (\(s, _, _) -> s) . travA (TupRsingle Shared)
  where
    travA :: forall genv t. Uniquenesses t -> C.PartitionedAcc op genv t -> (PartialSchedule op genv t, IdxSet genv, MaybeVars genv t)
    travA _  (C.Exec cluster)
      | Exists env <- convertEnvFromList $ map (foldr1 combineMod) $ groupBy (\(Exists v1) (Exists v2) -> isJust $ matchIdx (varIdx v1) (varIdx v2)) $ execVars cluster -- TODO: Remove duplicates more efficiently
      , Reads reEnv k inputBindings <- readRefs $ convertEnvRefs env
      , Just cluster' <- reindexExecPartial (reEnvIdx reEnv) cluster
        = let
            signals = convertEnvSignals env
            resolvers = convertEnvSignalResolvers k env
          in
            ( PartialDo OutputEnvUnit env
                $ Effect (SignalAwait signals)
                $ inputBindings
                $ Effect (Exec cluster')
                $ Effect (SignalResolve resolvers)
                $ Return
            , undefined
            , TupRunit
            )
      | otherwise = error "partialSchedule: reindexExecPartial returned Nothing. Probably some variable is missing in 'execVars'"
      where
        combineMod :: Exists (Var AccessGroundR env) -> Exists (Var AccessGroundR env) -> Exists (Var AccessGroundR env)
        combineMod (Exists (Var (AccessGroundRbuffer m1 tp) ix)) var@(Exists (Var (AccessGroundRbuffer m2 _) _))
          | Exists' m <- combineMod' m1 m2 = Exists $ Var (AccessGroundRbuffer m tp) ix
          | otherwise = var

        combineMod' :: Modifier m -> Modifier m' -> Exists' Modifier
        combineMod' In  In  = Exists' In
        combineMod' Out Out = Exists' Out
        combineMod' _   _   = Exists' Mut
    travA us (C.Return vars)  = (PartialReturn us vars, IdxSet.fromList $ map (\(Exists (Var _ idx)) -> Exists idx) $ flattenTupR vars, mapTupR f vars)
      where
        duplicates = map head $ filter (\g -> length g >= 2) $ group $ sort $ map (\(Exists (Var _ ix)) -> idxToInt ix) $ flattenTupR vars

        f :: GroundVar genv t' -> MaybeVar genv t'
        f v@(Var _ idx)
          | idxToInt idx `elem` duplicates = NoVars
          | otherwise = ReturnVar v
    travA _  (C.Compute e)    = partialLift (mapTupR GroundRscalar $ expType e) f (expGroundVars e)
      where
        f :: genv :?> fenv -> Maybe (Binding fenv t)
        f k = Compute <$> strengthenArrayInstr k e
    travA us (C.Alet lhs us' bnd a) = (partialDeclare lhs dest us' bnd' a', used1 `IdxSet.union` IdxSet.drop' lhs used2, vars')
      where
        dest = lhsDestination lhs vars
        (bnd', used1, _) = travA us' bnd
        (a', used2, vars) = travA us a
        vars' = weakenMaybeVars lhs vars `removeMaybeVars` used1
    travA _  (C.Alloc shr tp sh) = partialLift1 (TupRsingle $ GroundRbuffer tp) (Alloc shr tp) sh
    travA _  (C.Use tp buffer) = partialLift1 (TupRsingle $ GroundRbuffer tp) (const $ Use tp buffer) TupRunit
    travA _  (C.Unit var@(Var tp _)) = partialLift1 (TupRsingle $ GroundRbuffer tp) f (TupRsingle var)
      where
        f (TupRsingle var') = Unit var'
    travA us (C.Acond c t f) = (partialAcond c t' f', IdxSet.union used1 used2, vars)
      where
        (t', used1, vars1) = travA us t
        (f', used2, vars2) = travA us f
        vars = joinVars vars1 vars2
    travA _  (C.Awhile us c f vars) = (partialAwhile us c' f' vars, undefined, TupRsingle NoVars)
      where
        c' = partialScheduleFun c
        f' = partialScheduleFun f

partialScheduleFun :: C.PartitionedAfun op genv t -> PartialScheduleFun op genv t
partialScheduleFun (C.Alam lhs f) = Plam lhs $ partialScheduleFun f
partialScheduleFun (C.Abody b)    = Pbody $ partialSchedule b

partialLift1 :: GroundsR s -> (forall fenv. ExpVars fenv t -> Binding fenv s) -> ExpVars genv t -> (PartialSchedule op genv s, IdxSet genv, MaybeVars genv s)
partialLift1 tp f vars = partialLift tp (\k -> f <$> strengthenVars k vars) (expVarsList vars)

expVarsList :: ExpVars genv t -> [Exists (GroundVar genv)]
expVarsList = (`go` [])
  where
    go :: ExpVars genv t -> [Exists (GroundVar genv)] -> [Exists (GroundVar genv)]
    go TupRunit                 accum = accum
    go (TupRsingle (Var tp ix)) accum = Exists (Var (GroundRscalar tp) ix) : accum
    go (TupRpair v1 v2)         accum = go v1 $ go v2 accum

strengthenVars :: genv :?> fenv -> Vars s genv t -> Maybe (Vars s fenv t)
strengthenVars k TupRunit                = pure TupRunit
strengthenVars k (TupRsingle (Var t ix)) = TupRsingle . Var t <$> k ix
strengthenVars k (TupRpair v1 v2)        = TupRpair <$> strengthenVars k v1 <*> strengthenVars k v2

partialLift :: forall op genv s. GroundsR s -> (forall fenv. genv :?> fenv -> Maybe (Binding fenv s)) -> [Exists (GroundVar genv)] -> (PartialSchedule op genv s, IdxSet genv, MaybeVars genv s)
partialLift tp f vars
  | DeclareOutput outputEnv kOut varsOut <- declareOutput @() @s tp (mapTupR uniqueIfBuffer tp)
  , Exists env <- convertEnvReadonlyFromList $ nubBy (\(Exists v1) (Exists v2) -> isJust $ matchVar v1 v2) vars -- TODO: Remove duplicates more efficiently
  , Reads reEnv k inputBindings <- readRefs $ convertEnvRefs env
  , DeclareVars lhs k' value <- declareVars $ mapTupR BaseRground tp
  , Just binding <- f (reEnvIdx reEnv)
  =
    let
      signals = convertEnvSignals env
      resolvers = convertEnvSignalResolvers (k' .> k) env
    in
      ( PartialDo outputEnv env
          $ Effect (SignalAwait signals)
          $ inputBindings
          $ Alet lhs binding
          $ Effect (SignalResolve resolvers)
          $ writeOutput outputEnv (varsOut (k' .> k .> convertEnvWeaken env)) (value weakenId)
      , undefined
      , mapTupR (const NoVars) tp
      )

uniqueIfBuffer :: GroundR t -> Uniqueness t
uniqueIfBuffer (GroundRbuffer _) = Unique
uniqueIfBuffer _                 = Shared

syncEnv :: PartialSchedule op genv t -> SyncEnv genv
syncEnv (PartialDo _ env _)          = convertEnvToSyncEnv env
syncEnv (PartialReturn u vars)       = variablesToSyncEnv u vars
syncEnv (PartialDeclare s _ _ _ _ _) = s
syncEnv (PartialAcond s _ _ _)       = s
syncEnv (PartialAwhile s _ _ _ _)    = s

syncEnvFun :: PartialScheduleFun op genv t -> SyncEnv genv
syncEnvFun (Plam lhs f) = weakenSyncEnv lhs $ syncEnvFun f
syncEnvFun (Pbody s)    = syncEnv s

convertEnvToSyncEnv :: ConvertEnv genv fenv fenv' -> SyncEnv genv
convertEnvToSyncEnv = partialEnvFromList (error "convertEnvToSyncEnv: Variable occurs multiple times") . (`go` [])
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
variablesToSyncEnv uniquenesses vars = partialEnvFromList (error "convertEnvToSyncEnv: Variable occurs multiple times") $ go uniquenesses vars []
  where
    go :: Uniquenesses t -> GroundVars genv t -> [EnvBinding Sync genv] -> [EnvBinding Sync genv]
    go (TupRsingle Unique) (TupRsingle (Var (GroundRbuffer _) ix))
                          accum = EnvBinding ix SyncWrite : accum
    go (TupRsingle Shared) (TupRsingle (Var (GroundRbuffer _) ix))
                          accum = EnvBinding ix SyncRead : accum
    go u (TupRpair v1 v2) accum = go u1 v1 $ go u2 v2 accum
      where (u1, u2) = pairUniqueness u
    go _ _                accum = accum

pairUniqueness :: Uniquenesses (s, t) -> (Uniquenesses s, Uniquenesses t)
pairUniqueness (TupRpair u1 u2)    = (u1, u2)
pairUniqueness (TupRsingle Shared) = (TupRsingle Shared, TupRsingle Shared)

{-
-- Combines two sync values from two subterms, where the first subterm uses
-- the buffers first. At this location we must introduce new signals to
-- synchronize that.
-- Returns:
--   * Number of signals to grant write access (ie one per read operation,
--     indicating that the read has finished and the data can be overriden.)
--   * Number of signals to grant read access (ie one per write operation)
--     Note that one has to wait on both the read access signals and the
--     write access signals to get write access.
--   * A merged Sync value
--
combineSync :: Sync t -> Sync t -> (Int, Int, Sync t)
combineSync (SyncRead  r)   (SyncRead  r')    = (0, 0, SyncRead (r + r'))
combineSync (SyncRead  r)   (SyncWrite r' w') = (r, 0, SyncWrite r' w')
combineSync (SyncWrite r w) (SyncWrite r' w') = (r, w, SyncWrite r' w')
combineSync (SyncWrite r w) (SyncRead  r')    = (0, 0, SyncWrite (r + r') w)

combineSync' :: Sync t -> Sync t -> Sync t
combineSync' a b = c
  where (_, _, c) = combineSync a b
-}
weakenSyncEnv :: GLeftHandSide t env env' -> SyncEnv env' -> SyncEnv env
weakenSyncEnv _                        PEnd          = PEnd
weakenSyncEnv (LeftHandSideWildcard _) env           = env
weakenSyncEnv (LeftHandSideSingle _)   (PPush env _) = env
weakenSyncEnv (LeftHandSideSingle _)   (PNone env)   = env
weakenSyncEnv (LeftHandSidePair l1 l2) env           = weakenSyncEnv l1 $ weakenSyncEnv l2 env
{-
maxSync :: Sync t -> Sync t -> Sync t
maxSync (SyncRead r)    (SyncRead r')     = SyncRead (max r r')
maxSync (SyncRead r)    (SyncWrite w' r') = SyncWrite w' (max r r')
maxSync (SyncWrite w r) (SyncRead r')     = SyncWrite w (max r r')
maxSync (SyncWrite w r) (SyncWrite w' r') = SyncWrite (max w w') (max r r') 
-}

-- TODO: Better name
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

-- Implementation of the sub-environment rule, by restricting the futures
-- in the FutureEnv to the abilities required by the SyncEnv.
-- Creates a sub-environment, providing only the futures needed in some subterm.
-- Also returns a list of locks which are not used in this sub-environment
-- (because the buffer is not used in that sub-term, or the sub-term doesn't require
-- write access for that buffer). Those locks should be resolved, ie, we should fork
-- a thread, wait on the signal and resolve the resolver, such that later operations
-- can get access to the resource.
--
subFutureEnvironment :: forall fenv genv op. FutureEnv fenv genv -> SyncEnv genv -> (FutureEnv fenv genv, [UniformSchedule (Cluster op) fenv])
subFutureEnvironment (PNone fenv) senv = (PNone fenv', actions)
  where
    (fenv', actions) = subFutureEnvironment fenv $ partialEnvTail senv
subFutureEnvironment (PPush fenv f@(FutureScalar _ _ _)) senv = (PPush fenv' f, actions)
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
subFutureEnvironment (PPush fenv (FutureBuffer tp signal ref read write)) (PNone senv) = (PNone fenv', action ++ actions)
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

sub :: forall fenv genv op. FutureEnv fenv genv -> SyncEnv genv -> (FutureEnv fenv genv -> UniformSchedule (Cluster op) fenv) -> UniformSchedule (Cluster op) fenv
sub fenv senv body = forks (body fenv' : actions)
  where
    (fenv', actions) = subFutureEnvironment fenv senv

-- Data type for the existentially qualified type variable fenv' used in chainFuture
data ChainFutureEnv op fenv genv where
  ChainFutureEnv :: (UniformSchedule (Cluster op) fenv' -> UniformSchedule (Cluster op) fenv) -> fenv :> fenv' -> FutureEnv fenv' genv -> FutureEnv fenv' genv -> ChainFutureEnv op fenv genv

chainFutureEnvironment :: fenv :> fenv' -> FutureEnv fenv genv -> SyncEnv genv -> SyncEnv genv -> ChainFutureEnv op fenv' genv
chainFutureEnvironment _ PEnd PEnd PEnd = ChainFutureEnv id weakenId PEnd PEnd
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
  = ChainFutureEnv instr k1 (PPush fenvLeft (weaken (k1 .> k) f)) (partialEnvSkip fenvRight)
-- Only used in right subterm
chainFutureEnvironment k (PPush fenv f) senvLeft (PPush senvRight _)
  | ChainFutureEnv instr k1 fenvLeft fenvRight <- chainFutureEnvironment k fenv (partialEnvTail senvLeft) senvRight
  = ChainFutureEnv instr k1 (partialEnvSkip fenvLeft) (PPush fenvRight (weaken (k1 .> k) f))
-- Index not present
chainFutureEnvironment k (PNone fenv) senvLeft senvRight
  | ChainFutureEnv instr k1 fenvLeft fenvRight <- chainFutureEnvironment k fenv (partialEnvTail senvLeft) (partialEnvTail senvRight)
  = ChainFutureEnv instr k1 (partialEnvSkip fenvLeft) (partialEnvSkip fenvRight)
chainFutureEnvironment _ _ _ _ = internalError "Illegal case. The keys of the FutureEnv should be the union of the keys of the two SyncEnvs."

-- Data type for the existentially qualified type variable fenv' used in chainFuture
data ChainFuture op fenv t where
  ChainFuture :: (UniformSchedule (Cluster op) fenv' -> UniformSchedule (Cluster op) fenv) -> fenv :> fenv' -> Future fenv' t -> Future fenv' t -> ChainFuture op fenv t

chainFuture :: Future fenv t -> Sync t -> Sync t -> ChainFuture op fenv t
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
    resolver1 = SuccIdx $ SuccIdx $ ZeroIdx
    signal2   = SuccIdx $ ZeroIdx
    resolver2 = ZeroIdx

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
          (Just $ Borrow (weaken k $ writeSignal) writeResolver)
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
    writeSignal2  = SuccIdx $ ZeroIdx
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
    resolver1 = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ ZeroIdx
    signal2   = SuccIdx $ SuccIdx $ SuccIdx $ ZeroIdx
    resolver2 = SuccIdx $ SuccIdx $ ZeroIdx
    signal3   = SuccIdx $ ZeroIdx
    resolver3 = ZeroIdx

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
    signal1   = SuccIdx $ ZeroIdx
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
    resolver1 = SuccIdx $ SuccIdx $ ZeroIdx
    signal2   = SuccIdx $ ZeroIdx
    resolver2 = ZeroIdx

-- Write before write
--          Left     Right
-- Read  --> X       > X -->
--             \   /
--               X
--             /   \
-- Write --> X ------> X -->
chainFuture (FutureBuffer tp signal ref read mwrite) SyncWrite SyncWrite
  | Nothing <- mwrite = internalError "Expected a FutureBuffer with write lock"
  | Just write <- mwrite
  = ChainFuture
      -- Create two signals (signal1 and signal2) to let the first subterm
      -- inform that respectively its read or write operations have finished.
      -- Also create a signal (signal3) which is resolved when signal1 and
      -- signal2 are both resolved.
      ( Alet lhsSignal NewSignal
        . Alet lhsSignal NewSignal
        . Alet lhsSignal NewSignal
        . Fork (Effect (SignalAwait [signal1, signal2]) $ Effect (SignalResolve [resolver3]) Return)
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
          (Just $ setLockSignal signal3 $ weaken' k write)
      )
  where
    k = weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc $ weakenSucc weakenId

    signal1   = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx
    resolver1 = SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ ZeroIdx
    signal2   = SuccIdx $ SuccIdx $ SuccIdx $ ZeroIdx
    resolver2 = SuccIdx $ SuccIdx $ ZeroIdx
    signal3   = SuccIdx $ ZeroIdx
    resolver3 = ZeroIdx

lhsSignal :: LeftHandSide BaseR (Signal, SignalResolver) fenv ((fenv, Signal), SignalResolver)
lhsSignal = LeftHandSidePair (LeftHandSideSingle BaseRsignal) (LeftHandSideSingle BaseRsignalResolver)

-- Similar to 'fromPartial', but also applies the sub-environment rule 
fromPartialSub
  :: forall op fenv genv t r.
     HasCallStack
  => OutputVars t r
  -> BaseVars fenv r
  -> FutureEnv fenv genv
  -> PartialSchedule (Cluster op) genv t
  -> UniformSchedule (Cluster op) fenv
fromPartialSub outputEnv outputVars env partial
  = sub env (syncEnv partial) (\env' -> fromPartial outputEnv outputVars env' partial)

fromPartial :: forall op fenv genv t r.
               HasCallStack
            => OutputVars t r
            -> BaseVars fenv r
            -> FutureEnv fenv genv
            -> PartialSchedule (Cluster op) genv t
            -> UniformSchedule (Cluster op) fenv
fromPartial outputEnv outputVars env = \case
    PartialDo outputEnv' convertEnv schedule -> undefined -- Something with a substitution
    PartialReturn uniquenesses vars -> travReturn vars 
    PartialDeclare syncEnv lhs dest uniquenesses bnd body -> undefined -- Something with fork
    PartialAcond syncEnv condition true false -> acond condition true false
    PartialAwhile syncEnv uniquenesses condition step vars -> undefined
  where
    travReturn :: GroundVars genv t -> UniformSchedule (Cluster op) fenv
    travReturn vars = forks ((\(signals, s) -> await signals s) <$> travReturn' outputEnv outputVars vars [])

    travReturn' :: OutputVars t' r' -> BaseVars fenv r' -> GroundVars genv t' -> [([Idx fenv Signal], UniformSchedule (Cluster op) fenv)] -> [([Idx fenv Signal], UniformSchedule (Cluster op) fenv)]
    travReturn' (OutputVarsPair o1 o2) (TupRpair r1 r2) (TupRpair v1 v2) accum = travReturn' o1 r1 v1 $ travReturn' o2 r2 v2 accum
    travReturn' OutputVarsIgnore _ _ accum = accum
    travReturn' OutputVarsShared (TupRpair (TupRsingle signal) (TupRsingle ref)) (TupRsingle (Var tp ix)) accum = task : accum
      where
        task = case prjPartial ix env of
          Nothing -> internalError "Variable not present in environment"
          Just (FutureScalar _ signal ref) -> ([signal], undefined)
          Just (FutureBuffer _ signal ref readAccess _) -> ([signal, lockSignal readAccess], Alet (LeftHandSideSingle $ BaseRground tp) (RefRead $ Var (BaseRref tp) ref) $ Effect (RefWrite undefined undefined) $ Effect (SignalResolve undefined) $ Return)
    travReturn' OutputVarsUnique (TupRpair (TupRpair (TupRsingle signalRead) (TupRsingle signalWrite)) (TupRsingle ref)) (TupRsingle v) accum = undefined : accum

    acond :: ExpVar genv PrimBool -> PartialSchedule (Cluster op) genv t -> PartialSchedule (Cluster op) genv t -> UniformSchedule (Cluster op) fenv
    acond (Var _ condition) true false = case prjPartial condition env of
      Just (FutureScalar _ signal ref) ->
        -- Wait on the signal 
        Effect (SignalAwait [signal])
          -- Read the value of the condition
          $ Alet (LeftHandSideSingle $ BaseRground $ GroundRscalar scalarType) (RefRead $ Var (BaseRref $ GroundRscalar scalarType) ref)
          $ Acond
            (Var scalarType ZeroIdx)
            (fromPartialSub outputEnv outputVars' env' true)
            (fromPartialSub outputEnv outputVars' env' false)
            Return
      Nothing -> internalError "Variable not found"
      where
        outputVars' = mapTupR (weaken (weakenSucc weakenId)) outputVars
        env' = mapPartialEnv (weaken (weakenSucc weakenId)) env

forks :: [UniformSchedule (Cluster op) fenv] -> UniformSchedule (Cluster op) fenv
forks [] = Return
forks [u] = u
forks (u:us) = Fork (forks us) u

serial :: forall op fenv. [UniformSchedule (Cluster op) fenv] -> UniformSchedule (Cluster op) fenv
serial = go weakenId
  where
    go :: forall fenv1. fenv :> fenv1 -> [UniformSchedule (Cluster op) fenv] -> UniformSchedule (Cluster op) fenv1
    go _  [] = Return
    go k1 (u:us) = trav k1 (weaken' k1 u)
      where
        trav :: forall fenv'. fenv :> fenv' -> UniformSchedule (Cluster op) fenv' -> UniformSchedule (Cluster op) fenv'
        trav k = \case
          Return -> go k us
          Alet lhs bnd u' -> Alet lhs bnd $ trav (weakenWithLHS lhs .> k) u'
          Effect effect u' -> Effect effect $ trav k u'
          Acond cond true false u' -> Acond cond true false $ trav k u'
          Awhile io cond step input u' -> Awhile io cond step input $ trav k u'
          Fork u' u'' -> Fork (trav k u') u''

data DeclareBinding op fenv genv' t where
  DeclareBinding :: fenv :> fenv'
                 -> (UniformSchedule (Cluster op) fenv' -> UniformSchedule (Cluster op) fenv)
                 -> OutputVars t r
                 -> (forall fenv''. fenv' :> fenv'' -> BaseVars fenv'' r)
                 -> (forall fenv''. fenv' :> fenv'' -> FutureEnv fenv'' genv')
                 -> DeclareBinding op fenv genv' t

declareBinding
  :: forall op fenv genv genv' bnd ret ret'.
     OutputVars ret ret'
  -> BaseVars fenv ret'
  -> FutureEnv fenv genv
  -> GLeftHandSide bnd genv genv'
  -> TupR (Destination ret) bnd
  -> TupR Uniqueness bnd
  -> DeclareBinding op fenv genv' bnd
declareBinding retEnv retVars = \fenv -> go weakenId (\k -> mapPartialEnv (weaken k) fenv)
  where
    go :: forall fenv' genv1 genv2 t. fenv :> fenv' -> (forall fenv''. fenv' :> fenv'' -> FutureEnv fenv'' genv1) -> GLeftHandSide t genv1 genv2 -> TupR (Destination ret) t -> TupR Uniqueness t -> DeclareBinding op fenv' genv2 t
    go k fenv (LeftHandSidePair lhs1 lhs2) (TupRpair dest1 dest2) (TupRpair u1 u2)
      | DeclareBinding k1 instr1 out1 vars1 fenv1 <- go k         fenv  lhs1 dest1 u1
      , DeclareBinding k2 instr2 out2 vars2 fenv2 <- go (k1 .> k) fenv1 lhs2 dest2 u2
      = DeclareBinding (k2 .> k1) (instr1 . instr2) (OutputVarsPair out1 out2) (\k' -> TupRpair (vars1 $ k' .> k2) (vars2 k')) fenv2
    go k fenv (LeftHandSideSingle _) (TupRsingle (DestinationReuse idx)) _
      = DeclareBinding
          weakenId
          id
          undefined
          undefined
          undefined
    go k fenv (LeftHandSideSingle (GroundRscalar tp)) _ _ = undefined
