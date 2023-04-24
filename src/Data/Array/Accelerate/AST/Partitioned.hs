{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE TypeFamilyDependencies#-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- |
-- Module      : Data.Array.Accelerate.AST.Partitioned
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
module Data.Array.Accelerate.AST.Partitioned (
  module Data.Array.Accelerate.AST.Partitioned,
  GroundR(..), GroundsR, GroundVar, GroundVars, NFData'(..), Arg(..),
  AccessGroundR(..),
  PreArgs(..), Args, Modifier(..),
  Exp', Var', Fun', In, Out, Mut
) where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Operation

import Prelude hiding ( take )
import Data.Bifunctor
import Data.Array.Accelerate.Trafo.Desugar (ArrayDescriptor(..))
import Data.Array.Accelerate.Representation.Array (Array, Buffers, ArrayR (ArrayR), rnfArrayR)
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Shape (ShapeR)
import Data.Type.Equality
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Representation.Type (TypeR, rnfTypeR, TupR (..), mapTupR, Distribute)
import Control.DeepSeq (NFData (rnf))
import Data.Array.Accelerate.Trafo.Operation.Simplify (SimplifyOperation(..))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (BackendCluster, MakesILP (BackendClusterArg))
import Data.Kind (Type)
import Data.Array.Accelerate.Type (ScalarType (..), SingleType (..), NumType (..), IntegralType (..))
import Data.Array.Accelerate.AST.Environment ((:>), weakenId, (.>), weakenSucc', weakenKeep, Env, prj')
import Data.Array.Accelerate.Trafo.Operation.Substitution (weaken, Sink)
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Array.Accelerate.Pretty.Exp (IdxF (..))

import qualified Debug.Trace
import Data.Maybe (fromJust)

-- In this model, every thread has one input element per input array,
-- and one output element per output array. That works perfectly for
-- a Map, Generate, ZipWith - but the rest requires some fiddling:
--
-- - Folds and Scans need to cooperate, and not every thread will
--   return a value. We can model the lack of a value somewhere in the interpreter/code generator, and
--   ignore that in this representation. We do the same for cooperation: This representation suggests that
--   each thread is independent, but they do not need to be.
--
-- - Fusing Backpermute and Stencil does not translate well to this composition of loop
--   bodies. Instead, we will need a pass (after construction of these clusters)
--   that propagates them to the start of each cluster (or the 
--   originating generate, if fused). This is currently implemented (ugly-ly) in the Interpreter.
--   There, we will treat Stencil as Backpermutes with a zipwith. In llvm backends, we should want to do better.

type PartitionedAcc  op = PreOpenAcc  (Cluster op)
type PartitionedAfun op = PreOpenAfun (Cluster op)

-- TODO parametrize Cluster over the backendargs; to allow a backend to not have them
-- currently using backendarg = () for this
data Cluster op args where
  Cluster :: BackendCluster op args
          -> Cluster' op args
          -> Cluster op args

-- | A cluster of operations, in total having `args` as signature
data Cluster' op args where
  Cluster' :: ClusterIO args input output
           -> ClusterAST op  input output
           -> Cluster' op args

-- | Internal AST of `Cluster`, simply a list of let-bindings.
-- Note that all environments hold scalar values, not arrays! (aside from Mut)
data ClusterAST op env result where
  None :: ClusterAST op env env
  -- `Bind _ x y` reads as `do x; in the resulting environment, do y`
  Bind :: LeftHandSideArgs body env scope
       -> op body
       -> ClusterAST op scope result
       -> ClusterAST op env   result

-- | A version of `LeftHandSide` that works on the function-separated environments: 
-- Given environment `env`, we can execute `body`, yielding environment `scope`.
data LeftHandSideArgs body env scope where
  Base :: LeftHandSideArgs () () ()
  -- The body has an input array
  Reqr :: TupR (IdxF (Value sh) env  ) e
       -> TupR (IdxF (Value sh) scope) e -- perhaps not needed, but it should always be there (because each buffer in the reqr is based on an ignr later)
       -> LeftHandSideArgs              body  env            scope
       -> LeftHandSideArgs (In  sh e -> body) env            scope
  -- The body creates an array
  Make :: TakeBuffers (Value sh) e escope scope
       -> ConsBuffers (Sh sh) e eenv env
       -> LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (Out sh e -> body) eenv            escope
  -- Used for Permute: Each 'thread' gets atomic update acess to all values. Behaves like Exp', Var' and Fun'.
  Adju :: LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (Mut sh e -> body) (env, Mut sh e) (scope, Mut sh e)
  -- Does nothing to this part of the environment
  Ignr :: LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs              body  (env, e)        (scope, e)
  Triv :: LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (m sh ()  -> body) (env, Var' sh)  (scope, Var' sh)
  -- Expressions, variables and functions are not fused
  EArg :: LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (Exp'   e -> body) (env, Exp' e)   (scope, Exp' e)
  VArg :: LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (Var'   e -> body) (env, Var' e)   (scope, Var' e)
  FArg :: LeftHandSideArgs              body   env             scope
       -> LeftHandSideArgs (Fun'   e -> body) (env, Fun' e)   (scope, Fun' e)

-- input ~ InArgs args, and output is a permuted version of OutArgs args
data ClusterIO args input output where
  Empty  :: ClusterIO () () ()
  -- Even when an array is fused away, we'll still need its shape sometimes!
  Vertical :: Take (Value sh e) eoutput output
           -> ArrayR (Array sh e)
           -> ClusterIO             args   input            output
           -> ClusterIO (Var' sh -> args) (input, Sh sh e) eoutput
  Input  :: ClusterIO              args   input               output
         -> ClusterIO (In  sh e -> args) (input, Value sh e) (output, Value sh e)
  Output :: Take (Value sh e) eoutput output
         -> SubTupR e e' -- since the latest refactor, we can replace the SubTup and the TypeR with a ScalarType, because this is always a scalar
         -> TypeR e
         -> ClusterIO              args   input               output
         -> ClusterIO (Out sh e' -> args) (input, Sh sh e)    eoutput
  MutPut :: ClusterIO              args   input             output
         -> ClusterIO (Mut sh e -> args) (input, Mut sh e) (output, Mut sh e)
  ExpPut :: ClusterIO              args   input             output
         -> ClusterIO (Exp'   e -> args) (input, Exp' e)   (output, Exp' e)
  VarPut :: ClusterIO              args   input             output
         -> ClusterIO (Var'   e -> args) (input, Var' e)   (output, Var' e)
  FunPut :: ClusterIO              args   input             output
         -> ClusterIO (Fun'   e -> args) (input, Fun' e)   (output, Fun' e)
  Trivial :: ClusterIO args input output
          -> ClusterIO (m sh () -> args) (input, Var' sh) (output, Var' sh)


instance NFData' (IdxF f env) where
  rnf' = rnf

instance Sink (IdxF f) where
  weaken w (IdxF i) = IdxF (weaken w i)

pattern SuccIdxF :: IdxF f (env, s) a -> IdxF f env a
pattern SuccIdxF i <- (succIdxF -> i)
  where
    SuccIdxF (IdxF (SuccIdx i)) = IdxF i
succIdxF :: IdxF f env a -> IdxF f (env, s) a
succIdxF (IdxF i) = IdxF (SuccIdx i)

there' :: TupR (IdxF f env) a -> TupR (IdxF f (env, x)) a
there' = mapTupR (\(IdxF i) -> IdxF (SuccIdx i))
wIdxF :: env :> env' -> TupR (IdxF f env) a -> TupR (IdxF f env') a
wIdxF w = mapTupR (\(IdxF i) -> IdxF (weaken w i))

-- like a Take, except it works per buffer instead of for the entire array.
-- Required to e.g. fuse Zips, and anything else where two sets of buffers overlap but aren't equal
data TakeBuffers (f :: Type -> Type) e exs xs where
  TakeUnit :: TakeBuffers f () xs xs
  -- Invariant: represents a single buffer!
  TakeSingle :: Take (f e) exs xs ->
    TakeBuffers f e exs xs
  TakePair :: TakeBuffers f e         exs  xs
           -> TakeBuffers f e'      e'exs exs
           -> TakeBuffers f (e, e') e'exs  xs

data ConsBuffers (f :: Type -> Type) e exs xs where
  ConsUnit :: ConsBuffers f () xs xs
  -- Invariant: represents a single buffer!
  ConsSingle ::
    ConsBuffers f e (xs, f e) xs
  ConsPair :: ConsBuffers f e         exs  xs
           -> ConsBuffers f e'      e'exs exs
           -> ConsBuffers f (e, e') e'exs  xs
  -- ConsUnitFusedAway :: ConsBuffers f e exs xs -> ConsBuffers f e (exs, y) (xs, y)

tbThere :: TakeBuffers f x exs xs -> TakeBuffers f x (exs, y) (xs, y)
tbThere TakeUnit = TakeUnit
tbThere (TakeSingle t) = TakeSingle (There t)
tbThere (TakePair l r) = TakePair (tbThere l) (tbThere r)

tbWeaken :: TakeBuffers f e exs xs -> xs :> exs
tbWeaken TakeUnit = weakenId
tbWeaken (TakeSingle t) = wTake t
tbWeaken (TakePair l r) = tbWeaken r .> tbWeaken l

cbWeaken :: ConsBuffers f e exs xs -> xs :> exs
cbWeaken ConsUnit = weakenId
cbWeaken ConsSingle = weakenSucc' weakenId
cbWeaken (ConsPair l r) = cbWeaken r .> cbWeaken l
-- cbWeaken (ConsUnitFusedAway cb) = weakenKeep $ cbWeaken cb

tbHere :: forall e f xs. TypeR e -> TakeBuffers f e (Append f e xs) xs
tbHere TupRunit = TakeUnit
tbHere (TupRpair l r) = TakePair (tbHere l) (tbHere r)
tbHere (TupRsingle ty) = case fromScalar @e @f @xs ty of Refl -> TakeSingle Here

cbHere :: forall e f xs. TypeR e -> ConsBuffers f e (Append f e xs) xs
cbHere TupRunit = ConsUnit
cbHere (TupRpair l r) = ConsPair (cbHere l) (cbHere r)
cbHere (TupRsingle ty) = case fromScalar @e @f @xs ty of Refl -> ConsSingle

type family Append f e xs where
  Append f (e1, e2) xs = Append f e2 (Append f e1 xs)
  Append f () xs = xs
  Append f e xs = (xs, f e)

fromScalar :: forall e f xs. ScalarType e -> Append f e xs :~: (xs, f e)
fromScalar _ = unsafeCoerce Refl -- trivially true for all cases, but there's a lot of them
                                 -- yes, I tried it for vector types too

instance NFData (TakeBuffers f e exs xs) where
  rnf TakeUnit = ()
  rnf (TakePair l r) = rnf l `seq` rnf r
  rnf (TakeSingle t) = rnf t

instance NFData (ConsBuffers f e exs xs) where
  rnf ConsUnit = ()
  rnf ConsSingle = ()
  rnf (ConsPair l r) = rnf l `seq` rnf r
  -- rnf (ConsUnitFusedAway c) = rnf c

pattern ExpArg :: ()
                => forall e args body scope. (args' ~ (e -> args), body' ~ (body, e), scope' ~ (scope, e))
                => LeftHandSideArgs args body scope
                -> LeftHandSideArgs args' body' scope'
pattern ExpArg lhs <- (unExpArg -> Just (E lhs Refl))
{-# COMPLETE Base, Reqr, Make, Adju, Ignr, ExpArg #-}
unExpArg :: LeftHandSideArgs args' i' o' -> Maybe (ExpArgExistential args' i' o')
unExpArg (EArg lhs) = Just (E lhs Refl)
unExpArg (VArg lhs) = Just (E lhs Refl)
unExpArg (FArg lhs) = Just (E lhs Refl)
unExpArg _ = Nothing
data ExpArgExistential args i o where
  E :: LeftHandSideArgs args i o -> (args', i', o') :~: (e -> args, (i,e), (o,e)) -> ExpArgExistential args' i' o'

pattern ExpPut' :: ()
                => forall e args i o. (args' ~ (e -> args), i' ~ (i, e), o' ~ (o, e))
                => ClusterIO args  i  o
                -> ClusterIO args' i' o'
pattern ExpPut' io <- (unExpPut' -> Just (P io Refl))
{-# COMPLETE Empty, Vertical, Input, Output, MutPut, ExpPut', Trivial #-}
unExpPut' :: ClusterIO args' i' o' -> Maybe (ExpPutExistential args' i' o')
unExpPut' (ExpPut io) = Just (P io Refl)
unExpPut' (VarPut io) = Just (P io Refl)
unExpPut' (FunPut io) = Just (P io Refl)
unExpPut' _ = Nothing
data ExpPutExistential args i o where
  P :: ClusterIO args i o -> (args', i', o') :~: (e -> args, (i, e), (o, e)) -> ExpPutExistential args' i' o'



-- | `xargs` is a type-level list which contains `x`. 
-- Removing `x` from `xargs` yields `args`.
data Take x xargs args where
  Here  :: Take x ( args, x)  args
  There :: Take x  xargs      args
        -> Take x (xargs, y) (args, y)

wTake :: Take x xargs args -> args :> xargs
wTake Here = weakenSucc' weakenId
wTake (There t) = weakenKeep $ wTake t

takeStrengthen :: Idx xs x -> Take y xs zs -> Idx (zs, y) x
takeStrengthen i Here = i
takeStrengthen ZeroIdx (There _) = SuccIdx ZeroIdx
takeStrengthen (SuccIdx i) (There t) = case takeStrengthen i t of
  ZeroIdx -> ZeroIdx
  SuccIdx i' -> SuccIdx $ SuccIdx i'

-- unsafe: fails if (f a) is y.
takeStrengthenF :: IdxF f xs a -> Take y xs env -> IdxF f env a
takeStrengthenF (IdxF i) t = IdxF . (\(SuccIdx i') -> i') $ takeStrengthen i t

takeIdx :: Take x xargs args -> Idx xargs x
takeIdx Here      = ZeroIdx
takeIdx (There t) = SuccIdx $ takeIdx t

-- A cluster from a single node
-- TODO just use conscluster for this
unfused :: op args -> BackendCluster op args -> Args env args -> Cluster op args
unfused = undefined -- iolhs args $ \io lhs -> Cluster b $ Cluster' io (Bind lhs op None)

-- iolhs :: Args env args -> (forall x y. ClusterIO args x y -> LeftHandSideArgs args x y -> r) -> r
-- iolhs ArgsNil                     f =                       f  Empty            Base
-- iolhs (ArgArray In  _ _ _ :>: as) f = iolhs as $ \io lhs -> f (Input  _ _    io) (Reqr Here Here lhs)
-- iolhs (ArgArray Out r _ _ :>: as) f = iolhs as $ \io lhs -> f (Output Here SubTupRkeep (arrayRtype r) io) (Make Here lhs)
-- iolhs (ArgArray Mut _ _ _ :>: as) f = iolhs as $ \io lhs -> f (MutPut io) (Adju lhs)
-- iolhs (ArgExp _           :>: as) f = iolhs as $ \io lhs -> f (ExpPut      io) (EArg lhs)
-- iolhs (ArgVar _           :>: as) f = iolhs as $ \io lhs -> f (VarPut      io) (VArg lhs)
-- iolhs (ArgFun _           :>: as) f = iolhs as $ \io lhs -> f (FunPut      io) (FArg lhs)

mkBase :: ClusterIO args i o -> LeftHandSideArgs () i i
mkBase Empty = Base
mkBase (Input ci) = Ignr $ mkBase ci
mkBase (Output _ _ _ ci) = Ignr (mkBase ci)
mkBase (MutPut   ci) = Ignr (mkBase ci)
mkBase (ExpPut'   ci) = Ignr (mkBase ci)
mkBase (Vertical _ _ ci) = Ignr (mkBase ci)
mkBase (Trivial ci) = Ignr $ mkBase ci

fromArgsTake :: forall env a ab b. Take a ab b -> Take (FromArg env a) (FromArgs env ab) (FromArgs env b)
fromArgsTake Here = Here
fromArgsTake (There t) = There (fromArgsTake @env t)

take :: Take a ab b -> ab -> (a, b)
take Here (b, a) = (a, b)
take (There t) (ab', c) = second (,c) $ take t ab'

put :: Take a ab b -> a -> b -> ab
put Here a b = (b, a)
put (There t) a (b, c) = (put t a b, c)

take' :: Take a ab b -> Env.Env f ab -> (f a, Env.Env f b)
take' Here (Env.Push env x) = (x, env)
take' (There t) (Env.Push env x) = second (`Env.Push` x) $ take' t env

put' :: Take a ab b -> f a -> Env.Env f b -> Env.Env f ab
put' Here a env = Env.Push env a
put' (There t) a (Env.Push env c) = Env.Push (put' t a env) c

weakenTakeWithLHS :: LeftHandSide s t xenv xenv' -> Take x xenv env -> Exists (Take x xenv')
weakenTakeWithLHS (LeftHandSideWildcard _) t = Exists t
weakenTakeWithLHS (LeftHandSideSingle _)   t = Exists $ There t
weakenTakeWithLHS (LeftHandSidePair l1 l2) t
  | Exists t1 <- weakenTakeWithLHS l1 t = weakenTakeWithLHS l2 t1

ttake :: Take x xas as -> Take y xyas xas -> (forall yas. Take x xyas yas -> Take y yas as -> r) -> r
ttake  tx           Here       k = k (There tx)   Here
ttake  Here        (There t)   k = k  Here        t
ttake  (There tx)  (There ty)  k = ttake tx ty $ \t1 t2 -> k (There t1) (There t2)

ttake' :: Take' x xas as -> Take' y xyas xas -> (forall yas. Take' x xyas yas -> Take' y yas as -> r) -> r
ttake' tx           Here'      k = k (There' tx)   Here'
ttake' Here'       (There' t)  k = k  Here'        t
ttake' (There' tx) (There' ty) k = ttake' tx ty $ \t1 t2 -> k (There' t1) (There' t2)

data Take' x xargs args where
  Here'  :: Take' x (x ->  args)       args
  There' :: Take' x       xargs        args
         -> Take' x (y -> xargs) (y -> args)

type family InArg a = b | b -> a where
  InArg (In sh e ) = Value sh e
  InArg (Mut sh e) = Mut sh e
  InArg (Exp'   e) = Exp' e
  InArg (Fun'   e) = Fun' e
  InArg (Var'   e) = Var' e
  InArg (Out sh e) = Sh sh e
type family InArgs a = b | b -> a where
  InArgs  ()       = ()
  InArgs  (a -> x) = (InArgs x, InArg a)

-- unsafeCoerce is needed because fundeps are stupid and we can't inverse type families, but take'Take below shows that this makes sense
takeTake' :: Take (InArg a) (InArgs axs) (InArgs xs) -> Take' a axs xs
takeTake' Here = unsafeCoerce Here'
takeTake' (There t) = unsafeCoerce $ There' $ takeTake' $ unsafeCoerce t

take'Take :: Take' a axs xs -> Take (InArg a) (InArgs axs) (InArgs xs)
take'Take Here' = Here
take'Take (There' t) = There $ take'Take t


type family OutArgs a where
  OutArgs ()              = ()
  OutArgs (Out sh e -> x) = (OutArgs x, Value sh e)
  OutArgs (_  -> x)       =  OutArgs x
type family OutArgsOf a where
  OutArgsOf () = ()
  OutArgsOf (Out sh e -> x) = Out sh e -> OutArgsOf x
  OutArgsOf (_ -> x) = OutArgsOf x

data ToArg env a where
  ArrArg :: ArrayR (Array sh e)
         -> GroundVars env sh
         -> GroundVars env (Buffers e)
         -> ToArg env (Value sh e)
  OutArg :: ArrayR (Array sh e)
         -> GroundVars env sh
         -> GroundVars env (Buffers e)
         -> ToArg env (Sh sh e)
  Others :: String -> Arg env a -> ToArg env a


-- getIn :: LeftHandSideArgs body i o -> i -> InArgs body
-- getIn Base () = ()
-- getIn (Reqr t1 _ lhs) i = let x = collectValue $ mapTupR (\(IdxF idx) -> _ i idx) t1 in (getIn lhs i, x)
-- getIn (Make _ _ lhs) i = let (sh, i') = _ i in (getIn lhs i', sh)
-- getIn (Adju lhs)   (i, x)  = (getIn lhs i, x)
-- getIn (Ignr lhs)   (i, _)  =  getIn lhs i
-- getIn (EArg lhs)   (i, x)  = (getIn lhs i, x)
-- getIn (VArg lhs)   (i, x)  = (getIn lhs i, x)
-- getIn (FArg lhs)   (i, x)  = (getIn lhs i, x)
--
-- collectValue :: TupR (Value sh) e -> Value sh e
-- collectValue TupRunit = Value () (error "no shape info")
-- collectValue (TupRsingle v) = v
-- collectValue (TupRpair (collectValue -> (Value l (Shape shr sh))) (collectValue -> (Value r _))) = Value (l,r) (Shape shr sh)
--
-- genOut :: LeftHandSideArgs body i o -> i -> OutArgs body -> o
-- genOut Base             ()    _     =
--   ()
-- genOut (Reqr t1 t2 lhs) i     o     = genOut lhs i o
-- genOut (Make t _ lhs)    (i, _) (o, x) =
--   putBuf t x (genOut lhs i o)
-- genOut (Adju lhs) (i, _)    (o, x) =
--   (genOut lhs i o, x)
-- genOut (Ignr lhs)      (i, x) o     =
--   (genOut lhs i o, x)
-- genOut (EArg lhs)      (i, x) o     =
--   (genOut lhs i o, x)
-- genOut (VArg lhs)      (i, x) o     =
--   (genOut lhs i o, x)
-- genOut (FArg lhs)      (i, x) o     =
--   (genOut lhs i o, x)

type family FromArg env a where
  FromArg env (Exp'     e) = Exp     env e
  FromArg env (Var'     e) = ExpVars env e
  FromArg env (Fun'     e) = Fun     env e
  FromArg env (Mut   sh e) = (ArrayDescriptor env (Array sh e), TypeR e)
  FromArg env x = x

type family FromArgs env a where
  FromArgs env ()            = ()
  FromArgs env (a, x) = (FromArgs env a, FromArg env x)
  -- FromArgs env (x, Exp'   e) = (FromArgs env x, Exp     env e)
  -- FromArgs env (x, Var'   e) = (FromArgs env x, ExpVars env e)
  -- FromArgs env (x, Fun'   e) = (FromArgs env x, Fun     env e)
  -- FromArgs env (x, Mut sh e) = (FromArgs env x, ArrayDescriptor env (Array sh e))
  -- FromArgs env (x, Value sh e) = (FromArgs env x,       Value sh    e)
  -- FromArgs env (x, Sh    sh e) = (FromArgs env x,         Sh sh e)

type FromIn  env args = FromArgs env ( InArgs args)
type FromOut env args = FromArgs env (OutArgs args)


-- helps for type inference and safety: If we instead use 'e', it can match all the other options too. 
data Value sh e = Value e (Sh sh e)
-- e is phantom
data Sh sh e    = Shape (ShapeR sh) sh

instance (NFData' (Cluster' op), NFData' (BackendCluster op)) => NFData' (Cluster op) where
  rnf' (Cluster b c) = rnf' b `seq` rnf' c

instance NFData' op => NFData' (Cluster' op) where
  rnf' (Cluster' io ast) = rnf io `seq` rnf ast

instance NFData (ClusterIO args input output) where
  rnf Empty = ()
  rnf (Vertical t repr io) = rnf t `seq` rnfArrayR repr `seq` rnf io
  rnf (Input io) = rnf io
  rnf (Output t s tp io) = rnf t `seq` rnf s `seq` rnfTypeR tp `seq` rnf io
  rnf (MutPut io) = rnf io
  rnf (ExpPut' io) = rnf io
  rnf (Trivial io) = rnf io

instance NFData (Take x xargs args) where
  rnf Here = ()
  rnf (There t) = rnf t

instance NFData' op => NFData (ClusterAST op env result) where
  rnf None = ()
  rnf (Bind lhsArgs op ast) = rnf lhsArgs `seq` rnf' op `seq` rnf ast

instance NFData (LeftHandSideArgs body env scope) where
  rnf Base = ()
  rnf (Reqr take1 take2 args) = rnf take1 `seq` rnf take2 `seq` rnf args
  rnf (Make t1 t2 args) = rnf t1 `seq` rnf t2 `seq` rnf args
  rnf (Adju args) = rnf args
  rnf (Ignr args) = rnf args
  rnf (EArg args) = rnf args
  rnf (VArg args) = rnf args
  rnf (FArg args) = rnf args

instance SimplifyOperation op => SimplifyOperation (Cluster op) where
  -- TODO: Propagate detectCopy of operations in cluster?
  -- currently this simplifies nothing!


instance ShrinkArg (BackendClusterArg op) => SLVOperation (Cluster op) where
  slvOperation (Cluster b (Cluster' io ast :: Cluster' op args)) = Just $ ShrinkOperation shrinkOperation
    where
      shrinkOperation :: SubArgs args args' -> Args env args' -> Args env' args -> ShrunkOperation (Cluster op) env
      shrinkOperation subArgs args' args = ShrunkOperation (Cluster (shrinkArgs subArgs b) cluster') args'
        where cluster' = Cluster' (slvIO subArgs args' args io) ast

      slvIO :: SubArgs a a' -> Args env a' -> Args env' a -> ClusterIO a i o -> ClusterIO a' i o
      slvIO SubArgsNil ArgsNil ArgsNil Empty = Empty
      slvIO (SubArgsLive SubArgKeep              sa) (_:>:a') (_:>:a) (Trivial io') = Trivial $ slvIO sa a' a io'
      slvIO (SubArgsLive (SubArgOut SubTupRskip) sa) (_:>:a') (_:>:a) (Trivial io') = Trivial $ slvIO sa a' a io'
      slvIO (SubArgsLive (SubArgOut SubTupRkeep) sa) (_:>:a') (_:>:a) (Trivial io') = Trivial $ slvIO sa a' a io'
      slvIO (SubArgsDead subargs) (ArgVar _ :>: args') (ArgArray Out (ArrayR shr _) _ _ :>: args) (Trivial io') 
        = VarPut $ slvIO subargs args' args io'
      slvIO (SubArgsDead subargs) (ArgVar _ :>: args') (ArgArray Out (ArrayR shr _) _ _ :>: args) (Output t _ te io')
        = Vertical t (ArrayR shr te) $ slvIO subargs args' args io'
      slvIO (SubArgsLive SubArgKeep subargs) (_ :>: (args' :: Args env a')) (_ :>: (args :: Args env' a)) io'
        = let k :: forall i o. ClusterIO a i o -> ClusterIO a' i o
              k = slvIO subargs args' args
          in case io' of
            Input        io'' -> Input  (k io'')
            MutPut       io'' -> MutPut (k io'')
            ExpPut       io'' -> ExpPut (k io'')
            VarPut       io'' -> VarPut (k io'')
            FunPut       io'' -> FunPut (k io'')
            Vertical t r io'' -> Vertical t r (k io'') --case k io'' of SLVIO io''' diff -> wTakeO diff t $ \diff' t' -> SLVIO (Vertical t' r io''') (DeeperI diff')
            Output t s e io'' -> Output t s e (k io'') --case k io'' of SLVIO io''' diff -> wTakeO diff t $ \diff' t' -> SLVIO (Output t' s e io''') (DeeperI diff')
      slvIO
        (SubArgsLive (SubArgOut s) sa)
        ((ArgArray Out _ _ _) :>: a')
        ((ArgArray Out _ _ _) :>: a)
        (Output t s' tr io')
        = Output t (composeSubTupR s s') tr $ slvIO sa a' a io'


class TupRmonoid f where
  pair' :: f a -> f b -> f (a,b)
  injL :: f a -> TupUnitsProof b -> f (a,b)
  injR :: f b -> TupUnitsProof a -> f (a,b)
  unpair' :: f (a,b) -> (f a, f b)

unit :: TupInfo f ()
unit = NoInfo OneUnit

pair :: TupRmonoid f => TupInfo f a -> TupInfo f b -> TupInfo f (a,b)
pair (Info x) (Info y) = Info $ pair' x y
pair (Info x) (NoInfo y) = Info $ injL x y
pair (NoInfo x) (Info y) = Info $ injR y x
pair (NoInfo x) (NoInfo y) = NoInfo (MoreUnits x y)

unpair :: TupRmonoid f => TupInfo f (a,b) -> (TupInfo f a, TupInfo f b)
unpair (Info x) = bimap Info Info $ unpair' x
unpair (NoInfo (MoreUnits x y)) = (NoInfo x, NoInfo y)

instance TupRmonoid Identity where
  pair' (Identity x) (Identity y) = Identity (x, y)
  unpair' (Identity (x,y)) = (Identity x, Identity y)
  injL (Identity x) p = Identity (x, proofToV p)
  injR (Identity x) p = Identity (proofToV p, x)

data TupUnitsProof a where
  OneUnit :: TupUnitsProof ()
  MoreUnits :: TupUnitsProof a -> TupUnitsProof b -> TupUnitsProof (a,b)
-- Hold the info, or a proof that there are no non-unit values in this type
data TupInfo f a where
  Info :: f a -> TupInfo f a
  NoInfo :: TupUnitsProof a -> TupInfo f a

proofToR :: TupUnitsProof a -> TupR f a
proofToR OneUnit = TupRunit
proofToR (MoreUnits l r) = TupRpair (proofToR l) (proofToR r)

proofToR' :: forall g f a. TupUnitsProof a -> TupR f (Distribute g a)
proofToR' OneUnit = TupRunit
proofToR' (MoreUnits l r) = TupRpair (proofToR' @g l) (proofToR' @g r)

proofToV :: TupUnitsProof a -> a
proofToV OneUnit = ()
proofToV (MoreUnits a b) = (proofToV a, proofToV b)

tupInfoTransform :: (forall e. f e -> g e) -> TupInfo f a -> TupInfo g a
tupInfoTransform f (Info x) = Info $ f x
tupInfoTransform _ (NoInfo p) = NoInfo p

tupRfold :: TupRmonoid f => TupR f e -> TupInfo f e
tupRfold TupRunit = unit
tupRfold (TupRsingle s) = Info s
tupRfold (TupRpair l r) = tupRfold l `pair` tupRfold r

takeBuffers :: TupRmonoid (Compose f g) => TakeBuffers g e exs xs -> Env f exs -> (TupInfo (Compose f g) e, Env f xs)
takeBuffers TakeUnit env = (unit, env)
takeBuffers (TakeSingle t) env = first (Info . Compose) $ take' t env
takeBuffers (TakePair l r) env = case takeBuffers r env of
  (r', env') -> case takeBuffers l env' of
    (l', env'') -> (l' `pair` r', env'')

putBuffers :: TupRmonoid (Compose f g) => TakeBuffers g e exs xs -> TupInfo (Compose f g) e -> Env f xs -> Env f exs
putBuffers TakeUnit _ env = env
putBuffers (TakeSingle t) s env = case s of
  Info (Compose s') -> put' t s' env
  NoInfo _ -> error "single tupunitsproof"
putBuffers (TakePair l r) lr env = let (l', r') = unpair lr
                                   in putBuffers r r' $ putBuffers l l' env

unconsBuffers :: TupRmonoid (Compose f g) => ConsBuffers g e exs xs -> Env f exs -> (TupInfo (Compose f g) e, Env f xs)
unconsBuffers ConsUnit env = (unit, env)
unconsBuffers ConsSingle (Env.Push env s) = (Info $ Compose s, env)
unconsBuffers (ConsPair l r) env = case unconsBuffers r env of
  (r', env') -> case unconsBuffers l env' of
    (l', env'') -> (l' `pair` r', env'')
-- unconsBuffers (ConsUnitFusedAway cb) (Env.Push env s) = second (`Env.Push` s) $ unconsBuffers cb env

consBuffers :: TupRmonoid (Compose f g) => ConsBuffers g e exs xs -> f (g e) -> Env f xs -> Env f exs
consBuffers ConsUnit _ env = env
consBuffers ConsSingle s env = Env.Push env s
consBuffers (ConsPair l r) lr env = let
  (Compose l', Compose r') = unpair' $ Compose lr
  in consBuffers r r' $ consBuffers l l' env
-- consBuffers (ConsUnitFusedAway cb) s (Env.Push env t) = Env.Push (consBuffers cb s env) t

tupRindex :: TupRmonoid (Compose f g) => Env f env -> TupR (IdxF g env) a -> TupInfo (Compose f g) a
tupRindex env = tupRfold . mapTupR (\(IdxF idx) -> Compose $ prj' idx env)
