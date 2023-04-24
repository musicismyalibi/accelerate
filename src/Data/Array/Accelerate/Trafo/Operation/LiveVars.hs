{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.LiveVars
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Operation.LiveVars (
  module Data.Array.Accelerate.Trafo.LiveVars,

  stronglyLiveVariables, stronglyLiveVariablesFun,

  SLVOperation(..), ShrinkOperation(..), ShrunkOperation(..), SubArgs(..), SubArg(..),
  reEnvArrayInstr,
  ShrinkArg(..), shrinkArgs,

  defaultSlvGenerate, defaultSlvMap, defaultSlvBackpermute
) where

import Data.Array.Accelerate.AST.Idx
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.LiveVars
import Data.Array.Accelerate.Error

import Data.List ( foldl' )
import Data.Maybe
import Data.Type.Equality

--TODO remove
-- stronglyLiveVariables, stronglyLiveVariablesFun :: a -> a
-- stronglyLiveVariables = id
-- stronglyLiveVariablesFun = id

stronglyLiveVariablesFun :: SLVOperation op => PreOpenAfun op () t -> PreOpenAfun op () t
stronglyLiveVariablesFun acc = acc' ReEnvEnd
  where
    LVAnalysisFun _ acc' = stronglyLiveVariablesFun' emptyLivenessEnv acc

stronglyLiveVariables :: SLVOperation op => PreOpenAcc op () t -> PreOpenAcc op () t
stronglyLiveVariables acc = fromEither' $ acc' ReEnvEnd SubTupRkeep
  where
    LVAnalysis _ _ acc' = stronglyLiveVariables' emptyLivenessEnv (mapTupR (const Shared) $ groundsR acc) acc

stronglyLiveVariablesFun' :: SLVOperation op => LivenessEnv env -> PreOpenAfun op env t -> LVAnalysisFun (PreOpenAfun op) env t
stronglyLiveVariablesFun' liveness (Alam lhs f)
  | liveness1 <- pushLivenessEnv lhs noReturnImplications liveness
  , LVAnalysisFun liveness2 f' <- stronglyLiveVariablesFun' liveness1 f
  , liveness3 <- dropLivenessEnv lhs liveness2
  = LVAnalysisFun
      liveness3
      $ \re -> if
        | BindLiveness lhs' re' <- bind lhs re liveness2 ->
          Alam lhs' $ f' re'
stronglyLiveVariablesFun' liveness (Abody body)
  | LVAnalysis liveness1 returnImplications body' <- stronglyLiveVariables' liveness (mapTupR (const Shared) $ groundsR body) body
  , liveness2 <- foldl' (\e (Exists (ReturnImplication set)) -> setIndicesLive (IdxSet.toList set) e) liveness1 $ flattenTupR returnImplications
  = LVAnalysisFun
      liveness2
      $ \re -> Abody $ fromEither' $ body' re SubTupRkeep

stronglyLiveVariablesFun'' :: SLVOperation op => LivenessEnv env -> Uniquenesses t -> PreOpenAfun op env (s -> t) -> LVAnalysisFun (PreOpenAfun op) env (s -> t)
stronglyLiveVariablesFun'' liveness us (Alam lhs (Abody body))
  | liveness1 <- pushLivenessEnv lhs noReturnImplications liveness
  , LVAnalysis liveness2 returnImplications body' <- stronglyLiveVariables' liveness1 us body
  , liveness3 <- foldl' (\e (Exists (ReturnImplication indices)) -> setIndicesLive (IdxSet.toList indices) e) liveness2 $ flattenTupR returnImplications
  , liveness4 <- dropLivenessEnv lhs liveness3
  = LVAnalysisFun
      liveness4
      $ \re -> if
        | BindLiveness lhs' re' <- bind lhs re liveness3 ->
          Alam lhs' $ Abody $ fromEither' $ body' re' SubTupRkeep
stronglyLiveVariablesFun'' _ _ _ = internalError "Function impossible"

fromEither' :: Either a a -> a
fromEither' (Left  x) = x
fromEither' (Right x) = x

stronglyLiveVariables' :: SLVOperation op => LivenessEnv env -> Uniquenesses t -> PreOpenAcc op env t -> LVAnalysis (PreOpenAcc op) env t
stronglyLiveVariables' liveness us = \case
  Exec op args
    | Just (ShrinkOperation shrinkOp) <- slvOperation op
    -- We can shrink this operation to output to part of its buffers.
    , input <- IdxSet.fromList $ inputs args
    , output <- IdxSet.fromList $ outputs args
    , liveness1 <- setLivenessImplications output input liveness ->
      LVAnalysis
        liveness1
        noReturnImplications
        $ \re s -> if
          | Refl <- subTupUnit s
          , allDead re output ->
            Right $ Return TupRunit

          | Refl <- subTupUnit s
          , ReEnvSubArgs subArgs args' <- reEnvSubArgs re args
          , ShrunkOperation op' args'' <- shrinkOp subArgs args' args ->
            Right $ Exec op' args''

    -- We cannot shrink this operation to only output a part of its buffers.
    -- Hence it's "all or nothing", if we use at least one of the output
    -- buffers, then the entire operation is live.
    | free <- IdxSet.fromList $ map (\(Exists (Var _ idx)) -> Exists idx) $ argsVars args
    , output <- IdxSet.fromList $ outputs args
    , liveness1 <- setLivenessImplications output free liveness ->
      LVAnalysis
        liveness1
        noReturnImplications
        $ \re s -> if
          | Refl <- subTupUnit s
          , allDead re output ->
            Right $ Return TupRunit -- All output vars are dead

          | Refl <- subTupUnit s
          , args' <- reEnvArgs re args ->
            Right $ Exec op args' -- Live

  Return vars ->
    let
      returnImplications = mapTupR (\(Var _ idx) -> ReturnImplication $ IdxSet.singleton idx) vars
    in
      LVAnalysis
        liveness
        returnImplications
        $ \re s -> Right $ Return $ expectJust $ reEnvVars re $ subTupR s vars
  Compute expr ->
    let
      -- If the LHS of the binding is live, then all free variables of this
      -- expression are live as well.
      free = expGroundVars expr
    in
      LVAnalysis
        liveness
        (TupRsingle $ ReturnImplication $ IdxSet.fromVarList free)
        $ \re s ->
          let
            tp = expType expr
            expr' = mapArrayInstr (reEnvArrayInstr re) expr
          in case s of
              SubTupRskip -> Right $ Return TupRunit
              SubTupRkeep -> Right $ Compute $ expr'
              _ | DeclareSubVars lhs _ vars <- declareSubVars tp s
                -> Right $ Compute $ Let lhs expr' $ returnExpVars $ vars weakenId
  Alet lhs us' bnd body
    | LVAnalysis liveness1 retBnd bnd' <- stronglyLiveVariables' liveness  us' bnd
    , liveness2 <- pushLivenessEnv lhs retBnd liveness1
    , LVAnalysis liveness3 ret   body' <- stronglyLiveVariables' liveness2 us body
    , droppedRetBnd <- mapTupR (droppedReturnImplications lhs) ret ->
      LVAnalysis
        (dropLivenessEnv lhs liveness3)
        (mapTupR (strengthenReturnImplications liveness3 $ strengthenWithLHS lhs) ret)
        $ \re s -> case bindSub lhs re $ propagateReturnLiveness s droppedRetBnd liveness3 of
          BindLivenessSub subTup' lhsFull lhsSub re' -> case (bnd' re subTup', body' re' s) of
            (Left bnd'',  Left body'')  -> Left  $ mkAlet lhsFull us' bnd'' body''
            (Left bnd'',  Right body'') -> Right $ mkAlet lhsFull us' bnd'' body''
            (Right bnd'', Left body'')  -> Left  $ mkAlet lhsSub (subTupR subTup' us') bnd'' body''
            (Right bnd'', Right body'') -> Right $ mkAlet lhsSub (subTupR subTup' us') bnd'' body''
  Alloc shr tp sh ->
    let
      free = IdxSet.fromVars sh
    in
      LVAnalysis
        liveness
        (TupRsingle $ ReturnImplication free)
        $ \re s ->
          case s of
            SubTupRskip -> Right $ Return TupRunit
            SubTupRkeep -> Right $ Alloc shr tp $ expectJust $ reEnvVars re sh
  Use tp size buffer ->
    LVAnalysis
      liveness
      noReturnImplications
      $ \_ s ->
        case s of
          SubTupRskip -> Right $ Return TupRunit
          SubTupRkeep -> Right $ Use tp size buffer
  Unit var ->
    let
      free = IdxSet.singleton $ varIdx var
    in
      LVAnalysis
        liveness
        (TupRsingle $ ReturnImplication free)
        $ \re s ->
          case s of
            SubTupRskip -> Right $ Return TupRunit
            SubTupRkeep -> Right $ Unit $ expectJust $ reEnvVar re var
  Acond condition true false
    | liveness1 <- setLive (varIdx condition) liveness
    , LVAnalysis liveness2 retTrue  true'  <- stronglyLiveVariables' liveness1 us true
    , LVAnalysis liveness3 retFalse false' <- stronglyLiveVariables' liveness2 us false ->
      LVAnalysis
        liveness3
        (joinReturnImplications retTrue retFalse)
        $ \re s ->
          let condition' = expectJust $ reEnvVar re condition
          in case (true' re s, false' re s) of
              (Left  true'', Left  false'') -> Left  $ mkAcond condition' true'' false''
              (Right true'', Right false'') -> Right $ mkAcond condition' true'' false''
              (Left  true'', Right false'')
                | SubTupRkeep <- s     -> Left  $ mkAcond condition' true'' false''
                | DeclareSubVars lhs _ vars <- declareSubVars (groundsR true) s
                -> Right $ Acond condition' (Alet lhs us true'' $ Return $ vars weakenId) false''
              (Right true'', Left  false'')
                | SubTupRkeep <- s     -> Left  $ mkAcond condition' true'' false''
                | DeclareSubVars lhs _ vars <- declareSubVars (groundsR true) s
                -> Right $ Acond condition' true'' (Alet lhs us false'' $ Return $ vars weakenId)
  Awhile us' condition step initial
    | liveness1 <- setVarsLive initial liveness
    , LVAnalysisFun liveness2 condition' <- stronglyLiveVariablesFun'' liveness1 (TupRsingle Shared) condition
    , LVAnalysisFun liveness3 step'      <- stronglyLiveVariablesFun'' liveness2 us' step ->
      LVAnalysis
        liveness3
        noReturnImplications
        $ \re _ ->
          Left $ Awhile us' (condition' re) (step' re) $ expectJust $ reEnvVars re initial
  where
    mkAcond :: ExpVar env' PrimBool -> PreOpenAcc op env' t' -> PreOpenAcc op env' t' -> PreOpenAcc op env' t'
    mkAcond _         (Return TupRunit) (Return TupRunit) = Return TupRunit
    mkAcond condition true              false             = Acond condition true false

    mkAlet :: GLeftHandSide bnd subenv subenv' -> Uniquenesses bnd -> PreOpenAcc op subenv bnd -> PreOpenAcc op subenv' t -> PreOpenAcc op subenv t
    mkAlet (LeftHandSideWildcard TupRunit) _ (Return TupRunit) body = body
    mkAlet lhs us' bnd body = Alet lhs us' bnd body

class SLVOperation op where
  slvOperation :: op f -> Maybe (ShrinkOperation op f)

newtype ShrinkOperation op f = ShrinkOperation (forall f' env env'. SubArgs f f' -> Args env f' -> Args env' f -> ShrunkOperation op env)

data ShrunkOperation op env where
  ShrunkOperation :: op f' -> Args env f' -> ShrunkOperation op env

data SubArgs f f' where
  SubArgsNil  :: SubArgs () ()

  -- This Out argument is dead.
  -- Note that implementers of 'slvOperation' may assume that at least one Out
  -- or Mut argument is preserved.
  SubArgsDead :: SubArgs t t'
              -> SubArgs (Out sh e -> t) (Var' sh -> t')

  SubArgsLive :: SubArg  s s'
              -> SubArgs t t'
              -> SubArgs (s -> t) (s' -> t')

infixr 9 `SubArgsLive`

data SubArg t t' where
  SubArgKeep :: SubArg t t

  SubArgOut  :: SubTupR e e'
             -> SubArg (Out sh e) (Out sh e')

class ShrinkArg arg where
  shrinkArg :: SubArg t t' -> arg t -> arg t'
  deadArg :: arg (Out sh e) -> arg (Var' sh)

shrinkArgs :: ShrinkArg arg => SubArgs f f' -> PreArgs arg f -> PreArgs arg f'
shrinkArgs SubArgsNil ArgsNil = ArgsNil
shrinkArgs (SubArgsDead sargs) (a:>:args) = deadArg a :>: shrinkArgs sargs args
shrinkArgs (SubArgsLive sarg sargs) (a:>:args) = shrinkArg sarg a :>: shrinkArgs sargs args

defaultSlvGenerate
  :: (forall sh' t'. op (Fun' (sh' -> t') -> Out sh' t' -> ()))
  -> Maybe (ShrinkOperation op (Fun' (sh -> t) -> Out sh t -> ()))
defaultSlvGenerate mkGenerate = Just $ ShrinkOperation $ \subArgs args@(ArgFun f :>: array :>: ArgsNil) _ -> case subArgs of
  SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgsNil
    -> ShrunkOperation mkGenerate args
  SubArgKeep `SubArgsLive` SubArgOut subTp `SubArgsLive` SubArgsNil
    -> ShrunkOperation mkGenerate (ArgFun (subTupFun subTp f) :>: array :>: ArgsNil)
  _ `SubArgsLive` SubArgsDead _ -> internalError "At least one output should be preserved"

defaultSlvMap
  :: (forall sh' s' t'. op (Fun' (s' -> t') -> In sh' s' -> Out sh' t' -> ()))
  -> Maybe (ShrinkOperation op (Fun' (s -> t)    -> In sh s -> Out sh  t -> ()))
defaultSlvMap mkMap = Just $ ShrinkOperation $ \subArgs args@(ArgFun f :>: input :>: output :>: ArgsNil) _ -> case subArgs of
  SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgsNil
    -> ShrunkOperation mkMap args
  SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgOut subTp `SubArgsLive` SubArgsNil
    -> ShrunkOperation mkMap (ArgFun (subTupFun subTp f) :>: input :>: output :>: ArgsNil)
  _ `SubArgsLive` _ `SubArgsLive` SubArgsDead _ -> internalError "At least one output should be preserved"

defaultSlvBackpermute
  :: (forall sh1' sh2' t'. op (Fun' (sh2' -> sh1') -> In sh1' t' -> Out sh2' t' -> ()))
  -> Maybe (ShrinkOperation op (Fun' (sh2 -> sh1) -> In sh1 t -> Out sh2 t -> ()))
defaultSlvBackpermute mkBackpermute = Just $ ShrinkOperation $ \subArgs args@(f :>: ArgArray In (ArrayR shr r) sh buf :>: output :>: ArgsNil) _ -> case subArgs of
    SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgsNil
      -> ShrunkOperation mkBackpermute args
    SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgOut s `SubArgsLive` SubArgsNil
      -> ShrunkOperation mkBackpermute (f :>: ArgArray In (ArrayR shr (subTupR s r)) sh (subTupDBuf s buf) :>: output :>: ArgsNil)
    _ `SubArgsLive` _ `SubArgsLive` SubArgsDead _ -> internalError "At least one output should be preserved"

reEnvArrayInstr :: ReEnv env subenv -> ArrayInstr env t -> ArrayInstr subenv t
reEnvArrayInstr re (Parameter var) = Parameter $ expectJust $ reEnvVar re var
reEnvArrayInstr re (Index buffer)  = Index $ expectJust $ reEnvVar re buffer

inputs :: Args env t -> [Exists (Idx env)]
inputs = mapMaybe input . argsVars
  where
    input :: Exists (Var AccessGroundR env) -> Maybe (Exists (Idx env))
    input (Exists (Var (AccessGroundRbuffer Out _) _)) = Nothing
    input (Exists (Var _ idx)) = Just $ Exists idx

outputs :: Args env t -> [Exists (Idx env)]
outputs = mapMaybe output . argsVars
  where
    output :: Exists (Var AccessGroundR env) -> Maybe (Exists (Idx env))
    output (Exists (Var (AccessGroundRbuffer Out _) idx)) = Just $ Exists idx
    output (Exists (Var (AccessGroundRbuffer Mut _) idx)) = Just $ Exists idx
    output _ = Nothing

reEnvArgs :: ReEnv env subenv -> Args env t -> Args subenv t
reEnvArgs re (a :>: as) = reEnvArg re a :>: reEnvArgs re as
reEnvArgs _  ArgsNil    = ArgsNil

reEnvArg :: ReEnv env subenv -> Arg env t -> Arg subenv t
reEnvArg re (ArgVar vars) = ArgVar $ expectJust $ reEnvVars re vars
reEnvArg re (ArgExp expr) = ArgExp $ mapArrayInstr (reEnvArrayInstr re) expr
reEnvArg re (ArgFun f)    = ArgFun $ mapArrayInstrFun (reEnvArrayInstr re) f
reEnvArg re (ArgArray m repr sh buffers) = ArgArray m repr (expectJust $ reEnvVars re sh) (expectJust $ reEnvVars re buffers)

-- Captures existential f'
data ReEnvSubArgs subenv f where
  ReEnvSubArgs :: SubArgs f f'
               -> Args subenv f'
               -> ReEnvSubArgs subenv f

reEnvSubArgs :: ReEnv env subenv -> Args env f -> ReEnvSubArgs subenv f
reEnvSubArgs re (a :>: as)
  | ReEnvSubArgs subs as' <- reEnvSubArgs re as =
    case a of
      ArgArray Out (ArrayR shr tp) sh buffers -> case reEnvSubBuffers re tp buffers of
        ReEnvSubBuffers SubTupRskip _        -> ReEnvSubArgs (SubArgsDead subs) (ArgVar (fromGrounds $ expectJust $ reEnvVars re sh) :>: as')
        ReEnvSubBuffers SubTupRkeep buffers' -> ReEnvSubArgs (SubArgsLive SubArgKeep subs) (ArgArray Out (ArrayR shr tp) (expectJust $ reEnvVars re sh) buffers' :>: as')
        ReEnvSubBuffers sub         buffers' -> ReEnvSubArgs (SubArgsLive (SubArgOut sub) subs) (ArgArray Out (ArrayR shr $ subTupR sub tp) (expectJust $ reEnvVars re sh) buffers' :>: as')
      _ -> ReEnvSubArgs (SubArgsLive SubArgKeep subs) (reEnvArg re a :>: as')
reEnvSubArgs _ ArgsNil = ReEnvSubArgs SubArgsNil ArgsNil

reEnvSubBuffers :: ReEnv env subenv -> TypeR t -> GroundVars env (Buffers t) -> ReEnvSubBuffers subenv t
reEnvSubBuffers _  TupRunit TupRunit = ReEnvSubBuffers SubTupRskip TupRunit
reEnvSubBuffers re (TupRsingle _) (TupRsingle var)
  | Just var' <- reEnvVar re var = ReEnvSubBuffers SubTupRkeep (TupRsingle var')
  | otherwise = ReEnvSubBuffers SubTupRskip TupRunit
reEnvSubBuffers re (TupRpair t1 t2) (TupRpair v1 v2)
  | ReEnvSubBuffers s1 v1' <- reEnvSubBuffers re t1 v1
  , ReEnvSubBuffers s2 v2' <- reEnvSubBuffers re t2 v2
  = case (s1, s2) of
      (SubTupRskip, SubTupRskip) -> ReEnvSubBuffers SubTupRskip TupRunit
      (SubTupRkeep, SubTupRkeep) -> ReEnvSubBuffers SubTupRkeep (TupRpair v1' v2')
      _ -> ReEnvSubBuffers (SubTupRpair s1 s2) (TupRpair v1' v2')
reEnvSubBuffers _ _ _ = internalError "Tuple mismatch"

data ReEnvSubBuffers subenv t where
  ReEnvSubBuffers :: SubTupR t t' -> GroundVars subenv (Buffers t') -> ReEnvSubBuffers subenv t
