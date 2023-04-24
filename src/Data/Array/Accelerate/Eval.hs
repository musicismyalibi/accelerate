{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE BlockArguments         #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE PatternGuards          #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Data.Array.Accelerate.Eval where

import Prelude                                                      hiding (take, (!!), sum)
import Data.Array.Accelerate.AST.Partitioned hiding (Empty)
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.LeftHandSide
import qualified Data.Array.Accelerate.AST.Partitioned as P
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Desugar
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (BackendCluster, MakesILP (BackendClusterArg))
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Pretty.Partitioned ()


import Data.Array.Accelerate.Trafo.Schedule.Uniform ()
import Data.Array.Accelerate.Pretty.Schedule.Uniform ()
import Data.Kind (Type)
import Data.Bifunctor (bimap)
import Data.Biapplicative (biliftA2)
import Data.Functor.Compose
import Data.Type.Equality
import Data.Maybe (fromJust)
import Data.Function ((&))
import Data.Array.Accelerate.Type (ScalarType)
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.Representation.Shape (ShapeR)
import Data.Composition ((.*))
import Data.Array.Accelerate.Pretty.Exp (IdxF(..))
import Data.Array.Accelerate.AST.Idx (Idx (..))
import Data.Array.Accelerate.Pretty.Operation
import qualified Debug.Trace


type BackendArgs op env = PreArgs (BackendClusterArg2 op env)
type BackendEnv op env = Env (BackendEnvElem op env)
data BackendEnvElem op env arg = BEE (ToArg env arg) (BackendClusterArg2 op env arg)
type BackendArgEnv op env = Env (BackendArgEnvElem op env)
data BackendArgEnvElem op env arg = BAE (FromArg env (Embed op arg)) (BackendClusterArg2 op env arg)
newtype FromArg' op env a = FromArg (FromArg env (Embed op a))
pattern PushFA :: () => (e' ~ (e, x)) => FromArg env (Embed op x) -> Env (FromArg' op env) e -> Env (FromArg' op env) e'
pattern PushFA x env = Push env (FromArg x)
{-# COMPLETE Empty, PushFA #-}

-- TODO make actually static, i.e. by using `Fun env (Int -> Int)` instead in the interpreter
class (MakesILP op, forall env arg. Eq (BackendClusterArg2 op env arg)) => StaticClusterAnalysis (op :: Type -> Type) where
  -- give better name
  data BackendClusterArg2 op env arg
  onOp :: op args -> BackendArgs op env (OutArgsOf args) -> Args env args -> Env (EnvF op) env -> BackendArgs op env args
  def :: Arg env arg -> Env (EnvF op) env -> BackendClusterArg op arg -> BackendClusterArg2 op env arg
  valueToIn    :: BackendClusterArg2 op env (Value sh e)     -> BackendClusterArg2 op env (In    sh e)
  valueToOut   :: BackendClusterArg2 op env (Value sh e)     -> BackendClusterArg2 op env (Out   sh e)
  inToValue    :: BackendClusterArg2 op env (In    sh e)     -> BackendClusterArg2 op env (Value sh e)
  outToValue   :: BackendClusterArg2 op env (Out   sh e)     -> BackendClusterArg2 op env (Value sh e)
  outToSh      :: BackendClusterArg2 op env (Out   sh e)     -> BackendClusterArg2 op env (Sh    sh e)
  shToOut      :: BackendClusterArg2 op env (Sh    sh e)     -> BackendClusterArg2 op env (Out   sh e)
  shToValue    :: BackendClusterArg2 op env (Sh    sh e)     -> BackendClusterArg2 op env (Value sh e)
  varToValue   :: BackendClusterArg2 op env (Var'  sh)       -> BackendClusterArg2 op env (Value sh e)
  varToSh      :: BackendClusterArg2 op env (Var'  sh)       -> BackendClusterArg2 op env (Sh    sh e)
  shToVar      :: BackendClusterArg2 op env (Sh    sh e)     -> BackendClusterArg2 op env (Var'  sh  )
  shrinkOrGrow :: BackendClusterArg2 op env (m     sh e')    -> BackendClusterArg2 op env (m     sh e)
  addTup       :: BackendClusterArg2 op env (v     sh e)     -> BackendClusterArg2 op env (v     sh ((), e))
  unitToVar    :: BackendClusterArg2 op env (m     sh ())    -> BackendClusterArg2 op env (Var'  sh  )  
  varToUnit    :: BackendClusterArg2 op env (Var' sh)        -> BackendClusterArg2 op env (m     sh ())  
  pairinfo     :: BackendClusterArg2 op env (m sh a)         -> BackendClusterArg2 op env (m sh b) -> BackendClusterArg2 op env (m sh (a,b))
  pairinfo a b = if shrinkOrGrow a == b then shrinkOrGrow a else error "pairing unequal"
  unpairinfo   :: BackendClusterArg2 op env (m sh (a,b))     -> (BackendClusterArg2 op env (m sh a),  BackendClusterArg2 op env (m sh b))
  unpairinfo x = (shrinkOrGrow x, shrinkOrGrow x)

-- use ScopedTypeVariables for op and env, but not for the args (so we call them arguments instead)
makeBackendArg :: forall op env arguments. StaticClusterAnalysis op => Args env arguments -> Env (EnvF op) env -> Cluster op arguments -> BackendArgs op env arguments
makeBackendArg args env (Cluster info (Cluster' io ast)) = let o = getOutputEnv io args info
                                                               i = fromAST ast o
                                                          in fromInputEnv io i
  where
    fromAST :: ClusterAST op i o -> BackendEnv op env o -> BackendEnv op env i
    fromAST None o = o
    fromAST (Bind lhs op ast) o = let o' = fromAST ast o
                                  in lhsArgsEnv lhs o' (uncurry (onOp op) (first' onlyOut $ lhsEnvArgs lhs o') env)

    onlyOut :: BackendArgs op env args -> Args env args -> BackendArgs op env (OutArgsOf args)
    onlyOut ArgsNil ArgsNil = ArgsNil
    onlyOut (b :>: bs) (ArgArray Out _ _ _ :>: as) = b :>: onlyOut bs as
    onlyOut (_ :>: bs) (a                  :>: as) = case a of
      ArgArray In  _ _ _ -> onlyOut bs as
      ArgArray Mut _ _ _ -> onlyOut bs as
      ArgExp{} -> onlyOut bs as
      ArgVar{} -> onlyOut bs as
      ArgFun{} -> onlyOut bs as

    lhsEnvArgs :: LeftHandSideArgs body env' scope -> BackendEnv op env scope -> (BackendArgs op env body, Args env body)
    lhsEnvArgs Base Empty = (ArgsNil, ArgsNil)
    lhsEnvArgs (Reqr _ t   lhs) env = case tupRindex env t of
      Info (Compose (BEE (ArrArg r sh buf) f)) -> bimap (valueToIn  f :>:) (ArgArray In  r sh buf :>:) $ lhsEnvArgs lhs env
      _ -> error "urk"
    lhsEnvArgs (Make t1 t2 lhs) env = case takeBuffers t1 env of
      (Info (Compose (BEE (ArrArg r sh buf) f)), env') -> bimap (valueToOut f :>:) (ArgArray Out r sh buf :>:) $ lhsEnvArgs lhs env'
      _ -> error "urk"
    lhsEnvArgs (ExpArg lhs) (Push env (BEE (Others _ arg) f)) = bimap (f :>:) (arg :>:) $ lhsEnvArgs lhs env
    lhsEnvArgs (Adju   lhs) (Push env (BEE (Others _ arg) f)) = bimap (f :>:) (arg :>:) $ lhsEnvArgs lhs env
    lhsEnvArgs (Ignr lhs) (Push env _) = lhsEnvArgs lhs env

    lhsArgsEnv :: LeftHandSideArgs body env' scope -> BackendEnv op env scope -> BackendArgs op env body -> BackendEnv op env env'
    lhsArgsEnv Base                   _                ArgsNil            = Empty
    lhsArgsEnv (Reqr t1 t2 lhs)       env              (f :>: args) = case tupRindex env t2 of
      Info (Compose (BEE arg _)) ->
        overwriteInBackendEnv t1 (Compose (BEE arg $ inToValue f)) $ lhsArgsEnv lhs env args
      NoInfo _ -> lhsArgsEnv lhs env args
    lhsArgsEnv (Make t1 t2 lhs)       env              (f :>: args) = case takeBuffers t1 env of
      (Info (Compose (BEE (ArrArg r sh buf) _)), env') -> consBuffers t2 (BEE (OutArg r sh buf) (outToSh f)) (lhsArgsEnv lhs env' args)
      _ -> error "urk"
    lhsArgsEnv (ExpArg     lhs) (Push env (BEE arg _)) (f :>: args) = Push (lhsArgsEnv lhs env  args) (BEE arg f)
    lhsArgsEnv (Adju       lhs) (Push env (BEE arg _)) (f :>: args) = Push (lhsArgsEnv lhs env  args) (BEE arg f)
    lhsArgsEnv (Ignr       lhs) (Push env arg)                      args  = Push (lhsArgsEnv lhs env  args) arg

    getOutputEnv :: ClusterIO args i o -> Args env args -> BackendCluster op args -> BackendEnv op env o
    getOutputEnv P.Empty       ArgsNil           _ = Empty
    getOutputEnv (Vertical t r io) (arg@(ArgVar vars) :>: args) (info :>: infos) = put' t (BEE (ArrArg r (toGrounds vars) (error "accessing a fused away buffer")) (varToValue $ def arg env info)) (getOutputEnv io args infos) -- there is no buffer!
    getOutputEnv (Input io) (arg@(ArgArray In r sh buf) :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (ArrArg r sh buf) (inToValue $ def arg env info))
    getOutputEnv (Output t s e io) (arg@(ArgArray Out r sh buf) :>: args) (info :>: infos) = put' t (BEE (ArrArg (ArrayR (arrayRshape r) e) sh (biggenBuffers s buf)) (outToValue $ shrinkOrGrow $ def arg env info)) (getOutputEnv io args infos)
    getOutputEnv (MutPut     io) (arg :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (Others "mut" arg) (def arg env info))
    getOutputEnv (ExpPut     io) (arg :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (Others "exp" arg) (def arg env info))
    getOutputEnv (VarPut     io) (arg :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (Others "var" arg) (def arg env info))
    getOutputEnv (FunPut     io) (arg :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (Others "fun" arg) (def arg env info))
    getOutputEnv (Trivial    io) (arg@(ArgArray _ _ sh _) :>: args) (info :>: infos) = Push (getOutputEnv io args infos) (BEE (Others "trv" $ ArgVar $ fromGrounds sh ) (unitToVar $ def arg env info))

    biggenBuffers :: SubTupR e e' -> GroundVars env (Buffers e') -> GroundVars env (Buffers e)
    biggenBuffers SubTupRskip _ = error "accessing a simplified away buffer"
    biggenBuffers SubTupRkeep vars = vars
    biggenBuffers (SubTupRpair _ _) (TupRsingle _) = error "impossible???"
    biggenBuffers (SubTupRpair sl sr) (TupRpair bufl bufr) = TupRpair (biggenBuffers sl bufl) (biggenBuffers sr bufr)

    fromInputEnv :: ClusterIO args input output -> BackendEnv op env input -> BackendArgs op env args
    fromInputEnv P.Empty       Empty = ArgsNil
    fromInputEnv (Vertical _ _ io) (Push env (BEE _ f)) = shToVar f                :>: fromInputEnv io env
    fromInputEnv (Input        io) (Push env (BEE _ f)) = valueToIn f              :>: fromInputEnv io env
    fromInputEnv (Output _ _ _ io) (Push env (BEE _ f)) = shrinkOrGrow (shToOut f) :>: fromInputEnv io env
    fromInputEnv (MutPut       io) (Push env (BEE _ f)) = f                        :>: fromInputEnv io env
    fromInputEnv (ExpPut'      io) (Push env (BEE _ f)) = f                        :>: fromInputEnv io env
    fromInputEnv (Trivial      io) (Push env (BEE _ f)) = varToUnit f              :>: fromInputEnv io env

    overwriteInBackendEnv :: TupR (IdxF (Value sh) env') e -> Compose (BackendEnvElem op env) (Value sh) e -> BackendEnv op env env' -> BackendEnv op env env'
    overwriteInBackendEnv TupRunit _ env = env
    overwriteInBackendEnv (TupRpair l r) (unpair' -> (beeL, beeR)) env = overwriteInBackendEnv l beeL $ overwriteInBackendEnv r beeR env
    overwriteInBackendEnv (TupRsingle (IdxF idx)) (Compose bee) env = overwrite idx bee env
      where
        overwrite :: Idx env' (Value sh e) -> BackendEnvElem op env (Value sh e) -> BackendEnv op env env' -> BackendEnv op env env'
        overwrite ZeroIdx bee (Push env _) = Push env bee
        overwrite (SuccIdx idx) bee (Push env e) = Push (overwrite idx bee env) e



fromArgs :: Int -> Val env -> Args env args -> FromIn env args
fromArgs _ _ ArgsNil = ()
fromArgs i env (ArgVar v :>: args) = (fromArgs i env args, v)
fromArgs i env (ArgExp e :>: args) = (fromArgs i env args, e)
fromArgs i env (ArgFun f :>: args) = (fromArgs i env args, f)
fromArgs i env (ArgArray Mut (ArrayR shr t) sh buf :>: args) = (fromArgs i env args, (ArrayDescriptor shr sh buf, t))
fromArgs i env (ArgArray In (ArrayR shr typer) shv buf :>: args) =
  let buf' = varsGetVal buf env
      sh   = varsGetVal shv env
  in (fromArgs i env args, Value (indexBuffers typer buf' i) (Shape shr sh))
fromArgs i env (ArgArray Out (ArrayR shr _) sh _ :>: args) = (fromArgs i env args, Shape shr (varsGetVal sh env))


class (StaticClusterAnalysis op, Monad (EvalMonad op), TupRmonoid (Embed' op))
    => EvalOp op where
  type family EvalMonad op :: Type -> Type
  type family Index op :: Type 
  type family Embed' op :: Type -> Type
  type family EnvF op :: Type -> Type

  -- TODO most of these functions should probably be unnecesary, but adding them is the easiest way to get things working right now
  indexsh :: GroundVars env sh -> Env (EnvF op) env -> EvalMonad op (Embed' op sh)
  indexsh' :: ExpVars env sh -> Env (EnvF op) env -> EvalMonad op (Embed' op sh)
  subtup :: SubTupR e e' -> Embed' op e -> Embed' op e'


  evalOp :: Index op -> op args -> Env (EnvF op) env -> BackendArgEnv op env (InArgs args) -> (EvalMonad op) (Env (FromArg' op env) (OutArgs args))
  writeOutput :: ScalarType e -> GroundVars env sh -> GroundVars env (Buffers e) -> Env (EnvF op) env -> Index op -> Embed' op e -> EvalMonad op ()
  readInput :: ScalarType e -> GroundVars env sh -> GroundVars env (Buffers e) -> Env (EnvF op) env -> BackendClusterArg2 op env (In sh e) -> Index op -> EvalMonad op (Embed' op e)

type family Embed op a where
  Embed op (Value sh e) = Value' op sh e
  Embed op (Sh sh e) = Sh' op sh e
  Embed op e = e -- Mut, Exp', Var', Fun'

data Value' op sh e = Value' (Embed' op e) (Sh' op sh e)
data Sh' op sh e = Shape' (ShapeR sh) (Embed' op sh)

type family Distribute' f a = b | b -> a where
  Distribute' f () = ()
  Distribute' f (a,b) = (Distribute' f a, f b)
  -- Distribute' f (a, b) = (Distribute' f a, Distribute' f b)
  -- Distribute' f (Value sh e) = Value sh (f e)
  -- Distribute' f (Sh sh e) = Sh sh (f e)
distUnit :: forall f a. Distribute' f a ~ () => a :~: ()
distUnit = unsafeCoerce Refl
distPair :: forall f a b c. Distribute' f a ~ (Distribute' f b, f c) => a :~: (b, c)
distPair = unsafeCoerce Refl

evalCluster :: forall op env args. (EvalOp op) => Cluster op args -> Args env args -> Env (EnvF op) env -> Index op -> EvalMonad op ()
evalCluster c@(Cluster _ (Cluster' io ast)) args env ix = do
  let ba = makeBackendArg args env c
  i <- evalIO1 ix io args ba env
  o <- evalAST ix ast env i
  evalIO2 @op ix io args env o

evalIO1 :: forall op args i o env. EvalOp op => Index op -> ClusterIO args i o -> Args env args -> BackendArgs op env args -> Env (EnvF op) env -> (EvalMonad op) (BackendArgEnv op env i)
evalIO1 _ P.Empty                                     ArgsNil    ArgsNil    _ = pure Empty
evalIO1 n (Input io) (ArgArray In (ArrayR shr (TupRsingle tp)) sh buf :>: args) (info :>: infos) env
  | ScalarArrayDict _ _ <- scalarArrayDict tp =
    (\env' e sh -> Push env' (BAE (Value' e (Shape' shr sh)) $ inToValue info))
    <$> evalIO1 n io args infos env
    <*> readInput @op tp sh buf env info n
    <*> indexsh @op sh env
evalIO1 _ (Input io) (ArgArray _ (ArrayR _ TupRunit) _ _ :>: _) _ _ = error "unit"
evalIO1 _ (Input io) (ArgArray _ (ArrayR _ (TupRpair _ _)) _ _ :>: _) _ _ = error "pair"
evalIO1 n (Vertical _ r io) (ArgVar vars         :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> (flip BAE (varToSh info) . Shape' (arrayRshape r) <$> indexsh' @op vars env)
evalIO1 n (Output _ _ _ io) (ArgArray Out r sh _ :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> (flip BAE (outToSh $ shrinkOrGrow info) . Shape' (arrayRshape r) <$> indexsh @op sh env)
evalIO1 n (Trivial      io) (ArgArray _ _ sh _ :>: args)(info :>: infos) env    = Push <$> evalIO1 n io args infos env <*> pure (BAE (fromGrounds sh) $ unitToVar info)
evalIO1 n (ExpPut'      io) (ArgExp e              :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> pure (BAE e info)
evalIO1 n (ExpPut'      io) (ArgVar e              :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> pure (BAE e info)
evalIO1 n (ExpPut'      io) (ArgFun e              :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> pure (BAE e info)
evalIO1 n (MutPut       io) (ArgArray Mut (ArrayR shr t) sh buf :>: args) (info :>: infos) env = Push <$> evalIO1 n io args infos env <*> pure (BAE (ArrayDescriptor shr sh buf, t) info)

evalIO2 :: forall op args i o env. EvalOp op => Index op -> ClusterIO args i o -> Args env args -> Env (EnvF op) env -> Env (FromArg' op env) o -> (EvalMonad op) ()
evalIO2 _ P.Empty ArgsNil _ Empty = pure ()
evalIO2 n (Vertical t _ io) (_ :>: args) env (take' t -> (_, o)) = evalIO2 @op n io args env o
evalIO2 n (Input        io) (_ :>: args) env (PushFA _       o)  = evalIO2 @op n io args env o
evalIO2 n (MutPut       io) (_ :>: args) env (PushFA _       o)  = evalIO2 @op n io args env o
evalIO2 n (ExpPut'      io) (_ :>: args) env (PushFA _       o)  = evalIO2 @op n io args env o
evalIO2 n (Trivial      io) (_ :>: args) env (PushFA _       o)  = evalIO2 @op n io args env o
evalIO2 n (Output t s _ io) (ArgArray Out (arrayRtype -> ~(TupRsingle r)) sh buf :>: args) env o
  = let (FromArg (Value' x _), o') = take' t o in writeOutput @op r sh buf env n (subtup @op s x) >> evalIO2 @op n io args env o'

evalAST :: forall op i o env. EvalOp op => Index op -> ClusterAST op i o -> Env (EnvF op) env -> BackendArgEnv op env i -> (EvalMonad op) (Env (FromArg' op env) o)
evalAST _ None _ Empty = pure Empty
evalAST n None env (Push i (BAE x _)) = flip Push (FromArg x) <$> evalAST n None env i
evalAST n (Bind lhs op ast) env i = do
  let i' = evalLHS1 lhs i env
  o' <- evalOp n op env i'
  let scope = evalLHS2 lhs i env o'
  evalAST n ast env scope

evalLHS1 :: forall op body i scope env. EvalOp op => LeftHandSideArgs body i scope -> BackendArgEnv op env i -> Env (EnvF op) env -> BackendArgEnv op env (InArgs body)
evalLHS1 Base Empty _ = Empty
evalLHS1 (Reqr t _ lhs) i env = let Info (Compose (BAE x info)) = tupRindex i t in Push (evalLHS1 lhs i env) $ BAE x info
evalLHS1 (Make _ t lhs) i env = let (Info (Compose (BAE x info)), i') = unconsBuffers t i in Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (EArg     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (FArg     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (VArg     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (Adju     lhs) (Push i' (BAE x info)) env = Push (evalLHS1 lhs i' env) (BAE x info)
evalLHS1 (Ignr     lhs) (Push i' (BAE _ _   )) env =       evalLHS1 lhs i' env

evalLHS2 :: EvalOp op => LeftHandSideArgs body i scope -> BackendArgEnv op env i -> Env (EnvF op) env -> Env (FromArg' op env) (OutArgs body) -> BackendArgEnv op env scope
evalLHS2 Base Empty _ Empty = Empty
evalLHS2 (Reqr _ _ lhs) i env o = evalLHS2 lhs i env o
evalLHS2 (Make t1 t2 lhs) i env (Push o (FromArg y)) =
  let (info, i') = unconsBuffers t2 i
  in putBuffers t1
    (tupInfoTransform (Compose . (\(BAE _ i) -> BAE undefined (shToValue i)) . getCompose) info & (\case
        Info (Compose (BAE _ i)) -> Info (Compose (BAE y i))
        NoInfo p -> NoInfo p))
    (evalLHS2 lhs i'  env o)
evalLHS2 (EArg   lhs) (Push i (BAE x info)) env o = Push (evalLHS2 lhs i env o) (BAE x info)
evalLHS2 (FArg   lhs) (Push i (BAE x info)) env o = Push (evalLHS2 lhs i env o) (BAE x info)
evalLHS2 (VArg   lhs) (Push i (BAE x info)) env o = Push (evalLHS2 lhs i env o) (BAE x info)
evalLHS2 (Adju   lhs) (Push i (BAE m info)) env o = Push (evalLHS2 lhs i env o) (BAE m info)
evalLHS2 (Ignr   lhs) (Push i (BAE x info)) env o = Push (evalLHS2 lhs i env o) (BAE x info)

first' :: (a -> b -> c) -> (a,b) -> (c,b)
first' f (a,b) = (f a b, b)


instance EvalOp op => TupRmonoid (Value' op sh) where
  pair' (Value' x sh1) (Value' y sh2) = Value' (pair' x y) (pair' sh1 sh2)
  unpair' (Value' x sh) = biliftA2 Value' Value' (unpair' x) (unpair' sh)
  injL (Value' x sh) p = Value' (injL x p) (injL sh p)
  injR (Value' x sh) p = Value' (injR x p) (injR sh p)

instance TupRmonoid (Sh' op sh) where
  pair' (Shape' shr sh) _ = Shape' shr sh
  unpair' (Shape' shr sh) = (Shape' shr sh, Shape' shr sh)
  injL (Shape' shr sh) _ = Shape' shr sh
  injR (Shape' shr sh) _ = Shape' shr sh

instance StaticClusterAnalysis op => TupRmonoid (Compose (BackendEnvElem op env) (Value sh)) where
  pair' (Compose (BEE (ArrArg (ArrayR shr ar) shvars abufs) b))
        (Compose (BEE (ArrArg (ArrayR _ cr) _ cbufs) d))
    = Compose $ BEE
                  (ArrArg (ArrayR shr (TupRpair ar cr)) shvars (TupRpair abufs cbufs))
                  (pairinfo b d)
  pair' (Compose (BEE (Others s arg) _)) _ = Debug.Trace.trace ("fst"<>s) $ 
    -- case arg of
    -- ArgVar{} -> error "v"
    -- ArgExp{} -> error "e"
    -- ArgFun{} -> error "f"
    -- ArgArray m _ _ _ -> error $ show m
    -- _ -> 
      error s
  pair' _ (Compose (BEE (Others s arg) _)) = Debug.Trace.trace ("snd"<>s) $ 
    -- case arg of
    -- ArgVar{} -> error "v"
    -- ArgExp{} -> error "e"
    -- ArgFun{} -> error "f"
    -- ArgArray m _ _ _ -> error $ show m
    -- _ -> 
      error s
  pair' _ _ = error "value not in arrarg"

  unpair' (Compose (BEE (ArrArg (ArrayR shr (TupRpair ar cr)) shvars (TupRpair abufs cbufs)) infos))
    = bimap
        (Compose . BEE (ArrArg (ArrayR shr ar) shvars abufs))
        (Compose . BEE (ArrArg (ArrayR shr cr) shvars cbufs))
        $ unpairinfo infos
  unpair' _ = error "value not in arrarg"

  injL (Compose (BEE (ArrArg (ArrayR shr r) shvars bufs) info)) proof
   = Compose $ BEE (ArrArg (ArrayR shr (TupRpair r (proofToR proof))) shvars (TupRpair bufs (proofToR' @Buffer proof))) (shrinkOrGrow info)
  injL _ _ = error "value not in arrarg"

  injR :: StaticClusterAnalysis op 
    => Compose (BackendEnvElem op env) (Value sh) b
    -> TupUnitsProof a
    -> Compose (BackendEnvElem op env) (Value sh) (a, b)
  injR (Compose (BEE (ArrArg (ArrayR shr r) shvars bufs) info)) proof
   = Compose $ BEE (ArrArg (ArrayR shr (TupRpair (proofToR proof) r)) shvars (TupRpair (proofToR' @Buffer proof) bufs)) (shrinkOrGrow info)
  injR (Compose (BEE (Others s arg) _)) _ = Debug.Trace.trace s $ case arg of
    ArgVar{} -> error "v"
    ArgExp{} -> error "e"
    ArgFun{} -> error "f"
    ArgArray m _ _ _ -> error $ show m
    _ -> error s
  injR _ _ = error "value not in arrarg"

instance StaticClusterAnalysis op => TupRmonoid (Compose (BackendEnvElem op env) (Sh sh)) where
  pair' (Compose (BEE (OutArg (ArrayR shr ar) shvars abufs) b))
        (Compose (BEE (OutArg (ArrayR _ cr) _ cbufs) d))
    = Compose $ BEE
                  (OutArg (ArrayR shr (TupRpair ar cr)) shvars (TupRpair abufs cbufs))
                  (pairinfo b d)
  pair' _ _ = error "value not in arrarg"

  unpair' (Compose (BEE (OutArg (ArrayR shr (TupRpair ar cr)) shvars (TupRpair abufs cbufs)) infos))
    = bimap
        (Compose . BEE (OutArg (ArrayR shr ar) shvars abufs))
        (Compose . BEE (OutArg (ArrayR shr cr) shvars cbufs))
        $ unpairinfo infos
  unpair' _ = error "value not in arrarg"

  injL (Compose (BEE (OutArg (ArrayR shr r) shvars bufs) info)) proof
   = Compose $ BEE (OutArg (ArrayR shr (TupRpair r (proofToR proof))) shvars (TupRpair bufs (proofToR' @Buffer proof))) (shrinkOrGrow info)
  injL _ _ = error "value not in arrarg"

  injR (Compose (BEE (OutArg (ArrayR shr r) shvars bufs) info)) proof
   = Compose $ BEE (OutArg (ArrayR shr (TupRpair (proofToR proof) r)) shvars (TupRpair (proofToR' @Buffer proof) bufs)) (shrinkOrGrow info)
  injR _ _ = error "value not in arrarg"


instance EvalOp op => TupRmonoid (Compose (BackendArgEnvElem op env) (Value sh)) where
  pair' (Compose (BAE x b)) (Compose (BAE y d)) =
    Compose $ BAE (pair' x y) (pairinfo b d)
  unpair' (Compose (BAE x b)) =
    biliftA2
      (Compose .* BAE)
      (Compose .* BAE)
      (unpair' x)
      (unpairinfo b)
  injL (Compose (BAE x b)) p = Compose $ BAE (injL x p) (shrinkOrGrow b)
  injR (Compose (BAE x b)) p = Compose $ BAE (injR x p) (shrinkOrGrow b)

instance EvalOp op => TupRmonoid (Compose (BackendArgEnvElem op env) (Sh sh)) where
  pair' (Compose (BAE x b)) (Compose (BAE y d)) =
    Compose $ BAE (pair' x y) (pairinfo b d)
  unpair' (Compose (BAE x b)) =
    biliftA2
      (Compose .* BAE)
      (Compose .* BAE)
      (unpair' x)
      (unpairinfo b)
  injL (Compose (BAE x b)) p = Compose $ BAE (injL x p) (shrinkOrGrow b)
  injR (Compose (BAE x b)) p = Compose $ BAE (injR x p) (shrinkOrGrow b)

instance TupRmonoid (Compose (Arg' env) (Value sh)) where
  pair' (Compose (ArgArray' (ArgArray m (ArrayR r r1) sh buf1))) (Compose (ArgArray' (ArgArray _ (ArrayR _ r2) _ buf2)))
    = Compose $ ArgArray' $ ArgArray m (ArrayR r $ TupRpair r1 r2) sh (TupRpair buf1 buf2)
  pair' _ _ = error "not argarray'"
  unpair' (Compose (ArgArray' (ArgArray m (ArrayR r (TupRpair r1 r2)) sh (TupRpair buf1 buf2))))
    = (Compose (ArgArray' (ArgArray m (ArrayR r r1) sh buf1)), Compose (ArgArray' (ArgArray m (ArrayR r r2) sh buf2)))
  unpair' _ = error "not argarray'"
  injL (Compose (ArgArray' (ArgArray m (ArrayR r re) sh buf))) p
    = Compose $ ArgArray' $ ArgArray m (ArrayR r (TupRpair re (proofToR p))) sh (TupRpair buf (proofToR' @Buffer p))
  injL _ _ = error "not argarray'"
  injR (Compose (ArgArray' (ArgArray m (ArrayR r re) sh buf))) p
    = Compose $ ArgArray' $ ArgArray m (ArrayR r (TupRpair (proofToR p) re)) sh (TupRpair (proofToR' @Buffer p) buf)
  injR _ _ = error "not argarray'"

instance TupRmonoid (Compose (Arg' env) (Sh sh)) where
  pair' (Compose (ArgArray' (ArgArray m (ArrayR r r1) sh buf1))) (Compose (ArgArray' (ArgArray _ (ArrayR _ r2) _ buf2)))
    = Compose $ ArgArray' $ ArgArray m (ArrayR r $ TupRpair r1 r2) sh (TupRpair buf1 buf2)
  pair' _ _ = error "not argarray'"
  unpair' (Compose (ArgArray' (ArgArray m (ArrayR r (TupRpair r1 r2)) sh (TupRpair buf1 buf2))))
    = (Compose (ArgArray' (ArgArray m (ArrayR r r1) sh buf1)), Compose (ArgArray' (ArgArray m (ArrayR r r2) sh buf2)))
  unpair' _ = error "not argarray'"
  injL (Compose (ArgArray' (ArgArray m (ArrayR r re) sh buf))) p
    = Compose $ ArgArray' $ ArgArray m (ArrayR r (TupRpair re (proofToR p))) sh (TupRpair buf (proofToR' @Buffer p))
  injL _ _ = error "not argarray'"
  injR (Compose (ArgArray' (ArgArray m (ArrayR r re) sh buf))) p
    = Compose $ ArgArray' $ ArgArray m (ArrayR r (TupRpair (proofToR p) re)) sh (TupRpair (proofToR' @Buffer p) buf)
  injR _ _ = error "not argarray'"

justEnv     :: Env a env -> Env (Compose Maybe a) env
justEnv     = mapEnv (Compose . Just)
fromJustEnv :: Env (Compose Maybe a) env -> Env a env
fromJustEnv = mapEnv (fromJust . getCompose)

data Arg' env t where
  ArgArray' :: Arg env (m sh t)   -> Arg' env (m' sh t) -- Used for Value and Sh
  ArgOther' :: Arg env t          -> Arg' env t

instance Sink Arg' where
  weaken k (ArgArray' arg) = ArgArray' $ weaken k arg
  weaken k (ArgOther' arg) = ArgOther' $ weaken k arg


-- Ivo's method:
-- data ClusterOperations op env where
--   ClusterOperations
--     :: TypeR e
--     -> GLeftHandSide (Buffers e) env env'
--     -> [ApplyOperation op env']
--     -> ClusterOperations op env

-- data ApplyOperation op env where
--   ApplyOperation :: op f -> Args env f -> ApplyOperation op env

-- data BoundIO env input output where
--   BoundIO
--     :: TypeR e
--     -> GLeftHandSide (Buffers e) env env'
--     -> Env (Arg' env') input
--     -> Env (Arg' env') output
--     -> BoundIO env input output

-- clusterOperations :: Cluster op f -> Args env f -> ClusterOperations op env
-- clusterOperations (Cluster _ (Cluster' io ast)) args
--   | BoundIO tp lhs input  _ <- bindIO io args
--   = ClusterOperations tp lhs (traverseClusterAST input ast)
--   where
--     bindIO :: ClusterIO f' input output -> Args env f' -> BoundIO env input output
--     bindIO P.Empty ArgsNil = BoundIO TupRunit (LeftHandSideWildcard TupRunit) Empty Empty
--     bindIO (P.Vertical t repr@(ArrayR _ tp) io) (ArgVar sh :>: args)
--       | BoundIO bndTp lhs input output <- bindIO io args
--       , k <- weakenWithLHS lhs
--       -- Create variables for the buffers which were fused away
--       , DeclareVars lhs' k' vars <- declareVars (buffersR tp)
--       , arg <- ArgArray Mut repr (mapVars GroundRscalar $ mapTupR (weaken $ k' .> k) sh) (vars weakenId)
--       , input'  <- mapEnv (weaken k') input
--       , output' <- mapEnv (weaken k') output
--       = BoundIO
--         (bndTp `TupRpair` tp)
--         (lhs `LeftHandSidePair` lhs')
--         (Push input' $ ArgArray' arg)
--         (put' t (ArgArray' arg) output')
--     bindIO (P.Input io) (arg@(ArgArray In _ _ _) :>: args)
--       | BoundIO bndTp lhs input output <- bindIO io args
--       , k <- weakenWithLHS lhs
--       = BoundIO bndTp lhs
--         (Push input  $ ArgArray' $ weaken k arg)
--         (Push output $ ArgArray' $ weaken k arg)
--     bindIO (P.Output t s tp io) (arg :>: args)
--       -- Output which was fully preserved
--       | Just Refl <- subTupPreserves tp s
--       , BoundIO bndTp lhs input output <- bindIO io args
--       , k <- weakenWithLHS lhs
--       , arg' <- weaken k arg
--       = BoundIO bndTp lhs
--         (Push input $ ArgArray' arg')
--         (put' t (ArgArray' arg') output)
--     bindIO (P.Output t s tp io) (ArgArray Out (ArrayR shr _) sh buffers :>: args)
--       -- Part of the output is used. The operation has more output, but doesn't use that.
--       -- We need to declare variables for those buffers here.
--       | BoundIO bndTp lhs input output <- bindIO io args
--       , k <- weakenWithLHS lhs
--       , DeclareMissingDistributedVars tp' lhs' k' buffers' <-
--           declareMissingDistributedVars @Buffer tp (buffersR tp) s $ mapTupR (weaken k) buffers
--       , arg' <- ArgArray Out (ArrayR shr tp) (mapTupR (weaken $ k' .> k) sh) (buffers' weakenId)
--       , input'  <- mapEnv (weaken k') input
--       , output' <- mapEnv (weaken k') output
--       = BoundIO (bndTp `TupRpair` tp') (LeftHandSidePair lhs lhs')
--         (Push input' $ ArgArray' arg')
--         (put' t (ArgArray' arg') output')
--     -- For Mut, Exp, Var and Fun we must simply put them on top of the environments.
--     bindIO (P.MutPut io) (arg :>: args)
--       | BoundIO bndTp lhs input output <- bindIO io args
--       , k <- weakenWithLHS lhs
--       , arg' <- weaken k arg
--       = BoundIO bndTp lhs
--         (Push input  $ ArgOther' arg')
--         (Push output $ ArgOther' arg')
--     bindIO (P.ExpPut io) (arg :>: args)
--       | BoundIO bndTp lhs input output <- bindIO io args
--       , k <- weakenWithLHS lhs
--       , arg' <- weaken k arg
--       = BoundIO bndTp lhs
--         (Push input  $ ArgOther' arg')
--         (Push output $ ArgOther' arg')
--     bindIO (P.VarPut io) (arg :>: args)
--       | BoundIO bndTp lhs input output <- bindIO io args
--       , k <- weakenWithLHS lhs
--       , arg' <- weaken k arg
--       = BoundIO bndTp lhs
--         (Push input  $ ArgOther' arg')
--         (Push output $ ArgOther' arg')
--     bindIO (P.FunPut io) (arg :>: args)
--       | BoundIO bndTp lhs input output <- bindIO io args
--       , k <- weakenWithLHS lhs
--       , arg' <- weaken k arg
--       = BoundIO bndTp lhs
--         (Push input  $ ArgOther' arg')
--         (Push output $ ArgOther' arg')
--     bindIO (P.Trivial io) (arg :>: args)
--       | BoundIO bndTp lhs input output <- bindIO io args
--       , k <- weakenWithLHS lhs
--       , arg' <- weaken k arg
--       = BoundIO (_ bndTp) lhs 
--           (Push input _  ) 
--           (_ output )

--     traverseClusterAST
--       :: Env (Arg' env') input
--       -> ClusterAST op input output
--       -> [ApplyOperation op env']
--     traverseClusterAST _     None = []
--     traverseClusterAST input (Bind lhs op ast) =
--       ApplyOperation op (prjArgs input lhs)
--       : traverseClusterAST (lhsArgsOutput retypeSh lhs input) ast

--     prjArgs
--       :: Env (Arg' env') input
--       -> LeftHandSideArgs f input output
--       -> Args env' f
--     prjArgs input = \case
--       Base -> ArgsNil
--       Reqr idxEnv _ lhs
--         -> case tupRindex input idxEnv of
--             Info (Compose (ArgArray' arg@(ArgArray In _ _ _))) -> arg :>: prjArgs input lhs
--             _ -> error "nope"
--       -- Make _ lhs
--       --   | input' `Push` arg <- input
--       --   -> case arg of
--       --       ArgArray' (ArgArray _ repr sh buffers) -> ArgArray Out repr sh buffers :>: prjArgs input' lhs
--       --       ArgOther' (ArgArray m _ _ _) -> case m of {}
--       Make _ cb lhs
--         | (Info (Compose arg), input') <- unconsBuffers cb input
--         -> case arg of
--           ArgArray' arg@(ArgArray Out _ _ _) -> arg :>: prjArgs input' lhs
--           _ -> error "nope"
--         | otherwise -> error "nope"
--       Adju lhs
--         | input' `Push` arg <- input
--         -> case arg of
--             ArgArray' (ArgArray _ repr sh buffers) -> ArgArray Mut repr sh buffers :>: prjArgs input' lhs
--             ArgOther' (ArgArray _ repr sh buffers) -> ArgArray Mut repr sh buffers :>: prjArgs input' lhs
--       Ignr lhs
--         | input' `Push` _ <- input
--         -> prjArgs input' lhs
--       EArg lhs
--         | input' `Push` ArgOther' arg <- input
--         -> arg :>: prjArgs input' lhs
--       VArg lhs
--         | input' `Push` ArgOther' arg <- input
--         -> arg :>: prjArgs input' lhs
--       FArg lhs
--         | input' `Push` ArgOther' arg <- input
--         -> arg :>: prjArgs input' lhs

--     retypeSh :: Arg' env (Sh sh t) -> Arg' env (m' sh t)
--     retypeSh (ArgArray' arg) = ArgArray' arg
--     retypeSh (ArgOther' (ArgArray m _ _ _)) = case m of {}

lhsArgsOutput
  :: forall f t input output
  .  (forall sh'. TupRmonoid (Compose f (Sh sh')), forall sh'. TupRmonoid (Compose f (Value sh')))
  => (forall sh e. f (Sh sh e) -> f (Value sh e))
  -> LeftHandSideArgs t input output
  -> Env f input
  -> Env f output
lhsArgsOutput make lhsArgs input = case lhsArgs of
  Base -> Empty
  Reqr _ _ args
    -> go args input
  Make tb cb args
    -> case unconsBuffers cb input of
      (Info (Compose arg), input') -> putBuffers tb (Info . Compose $ make arg) $ go args input'
      (NoInfo p,           input') -> putBuffers tb (NoInfo p) $ go args input'
  Adju args
    | input' `Push` arg <- input
    -> go args input' `Push` arg
  Ignr args
    | input' `Push` arg <- input
    -> go args input' `Push` arg
  EArg args
    | input' `Push` arg <- input
    -> go args input' `Push` arg
  VArg args
    | input' `Push` arg <- input
    -> go args input' `Push` arg
  FArg args
    | input' `Push` arg <- input
    -> go args input' `Push` arg
  where
    go :: LeftHandSideArgs t' input' output' -> Env f input' -> Env f output'
    go = lhsArgsOutput make
