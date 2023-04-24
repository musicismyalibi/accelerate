{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyCase #-}

-- _Significantly_ speeds up compilation of this file, but at an obvious cost!
-- Even in GHC 9.0.1, which has Lower Your Guards, these checks take some time (though no longer quite as long).
-- Recommended to disable these options when working on this file, and restore them when you're done.
{-# OPTIONS_GHC 
  -Wno-overlapping-patterns 
  -Wno-incomplete-patterns 
#-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering where

import Data.Array.Accelerate.AST.LeftHandSide ( Exists(..), LeftHandSide (..) )
import Data.Array.Accelerate.AST.Partitioned hiding (take', unfused)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph hiding (info)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels hiding (ELabels)

import qualified Data.Map as M
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Graph as G
import qualified Data.Set as S
import Data.Array.Accelerate.AST.Operation
import Data.Maybe (fromJust)
import Data.Type.Equality ( type (:~:)(Refl) )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve (ClusterLs (Execs, NonExec))
import Data.Array.Accelerate.AST.Environment (weakenWithLHS)

import Prelude hiding ( take )
import Lens.Micro (_1)
import Lens.Micro.Extras (view)
import Data.Array.Accelerate.Trafo.LiveVars (SubTupR(SubTupRkeep))
import Data.Array.Accelerate.Representation.Array (ArrayR (ArrayR))
import qualified Data.Functor.Const as C
import Data.Bifunctor (first, second)
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Trafo.Operation.Substitution (weaken)
import Data.Functor.Identity
import Data.Array.Accelerate.Pretty.Exp (IdxF(..))
import qualified Data.Tree as T
import qualified Debug.Trace

-- "open research question"
-- -- Each set of ints corresponds to a set of Constructions, which themselves contain a set of ints (the things they depend on).
-- -- Some of those ints will refer to nodes in previous clusters, others to nodes in this cluster.
-- One pass over these datatypes (back-to-front) should identify the 'output type' of each cluster: which nodes are needed in later clusters?
-- Then, we can construct the clusters front-to-back:
--    identify the nodes that only depend on nodes outside of the cluster, they are the initials
--    the `output type` indicates which nodes we will need to keep: they are all either a final node in the cluster, or get diagonally fused
-- How exactly we can use this information (and a dep. graph) to construct a cluster of ver,hor,diag is not clear.. Will also depend on the exact cluster definition.

{-
Within each cluster (Labels), we do a topological sort using the edges in Graph
((a,b) means a before b in ordering). Then, we can simply cons them on top of each other.
Data.Graph (containers) has a nice topological sort.
-}


-- map M.! key = case map M.!? key of
--   Just x -> x
--   Nothing -> Debug.Trace.trace ("error: map "<> show map <> "does not contain key " <> show key) undefined

-- instance Show (Exists a) where
--   show (Exists x) = "exis"

-- Note that the return type `a` is not existentially qualified: The caller of this function tells
-- us what the result type should be (namely, what it was before fusion). We use unsafe tricks to
-- fulfill this contract: if something goes wrong during fusion or at the caller, bad things happen.
reconstruct :: forall op a. MakesILP op => Graph -> [ClusterLs] -> M.Map Label [ClusterLs] -> M.Map Label (Construction op) -> PreOpenAcc (Cluster op) () a
reconstruct a b c d = case openReconstruct LabelEnvNil a b c d of
          -- see [NOTE unsafeCoerce result type]
          Exists res -> unsafeCoerce @(PartitionedAcc op () _)
                                     @(PartitionedAcc op () a)
                                     res

reconstructF :: forall op a. MakesILP op => Graph -> [ClusterLs] -> M.Map Label [ClusterLs] -> M.Map Label (Construction op) -> PreOpenAfun (Cluster op) () a
reconstructF a b c d = case openReconstructF LabelEnvNil a b (Label 1 Nothing) c d of
          -- see [NOTE unsafeCoerce result type]
          Exists res -> unsafeCoerce @(PartitionedAfun op () _)
                                     @(PartitionedAfun op () a)
                                     res


-- ordered list of labels
data ClusterL = ExecL [Label] | NonExecL Label
  deriving Show

foldC :: (Label -> b -> b) -> b -> ClusterL -> b
foldC f x (ExecL ls) = foldr f x ls
foldC f x (NonExecL l) = f l x

topSort :: Graph -> Labels -> [ClusterL]
topSort _ (S.toList -> [l]) = [ExecL [l]]
topSort (Graph _ fedges fpedges) cluster = map ExecL topsorteds
  where
    buildGraph =
            G.graphFromEdges
          . map (\(a,b) -> (a,a,b))
          . M.toList
          . flip (S.fold (\(x :-> y) -> M.adjust (y:) x)) fedges
          . M.fromList
          . map (,[])
          . S.toList
    -- for some reason, this doesn't work yet!
    -- \xs -> (map f xs, map g xs) gets split, even though I really thought this would work
    -- if @xs@ is concrete, it does seem to work? 
    -- TODO: compare the graphs of @horizontal@ and @horizontal xs@
    -- TODO: I changed stuff since I wrote the above; check whether it works now

    -- Make a graph of all these labels and their incoming edges (for horizontal fusion)...
    fpparents =                    S.unions $ S.map (\l -> (S.\\ cluster) $ S.map (\(a:->_)->a) $ S.filter (\(_:->b)->l==b) fpedges) cluster
    parents   = (S.\\ fpparents) $ S.unions $ S.map (\l -> (S.\\ cluster) $ S.map (\(a:->_)->a) $ S.filter (\(_:->b)->l==b) fedges ) cluster
    parentsPlusEdges :: S.Set (Label, Int, Label) -- (Parent, Order, Source)
    parentsPlusEdges = S.unions $ S.unions $ S.map (\l -> let relevantEdges = S.filter (\(a:->b)->l==a && b `S.member` cluster) (fedges S.\\ fpedges)
                                                              orders :: S.Set Int
                                                              orders = S.map (\(a:->b)-> readOrderOf b) relevantEdges
                                                              ordersWithEdges = S.map (\o -> S.map (\(_:->b) -> (l,o,b)) $ S.filter (\(_:->b)-> readOrderOf b == o) relevantEdges) orders
                                                          in ordersWithEdges) parents
    (graph, getAdj, _) = buildGraph $ S.union cluster parents
    -- TODO: this also 'connects' components through 'horizonal fusion' if they are in different orders.
      -- To fix this: consider each edge from outside the cluster to inside the cluster: look at the sources (parents) and the read-order of those edges.
      -- Whenever one parent has outgoing edges of varying read-orders, we should have multiple nodes for this parent, one per read-order.

    -- .. split it into connected components and remove those parents from last step,
    components = map (S.intersection cluster . S.fromList . map ((\(x,_,_)->x) . getAdj) . T.flatten) $ G.components graph
    -- and make a graph of each of them...
    graphs = map buildGraph components
    -- .. and finally, topologically sort each of those to get the labels per cluster sorted on dependencies
    topsorteds = map (\(graph', getAdj', _) -> map (view _1 . getAdj') $ G.topSort graph') graphs
    readOrderOf = undefined --TODO

openReconstruct   :: MakesILP op
                  => LabelEnv aenv
                  -> Graph
                  -> [ClusterLs]
                  -> M.Map Label [ClusterLs]
                  -> M.Map Label (Construction op)
                  -> Exists (PreOpenAcc (Cluster op) aenv)
openReconstruct  a b c d e = (\(Left x) -> x) $ openReconstruct' a b c Nothing d e
openReconstructF  :: MakesILP op
                  => LabelEnv aenv
                  -> Graph
                  -> [ClusterLs]
                  -> Label
                  -> M.Map Label [ClusterLs]
                  -> M.Map Label (Construction op)
                  -> Exists (PreOpenAfun (Cluster op) aenv)
openReconstructF a b c l d e= (\(Right x) -> x) $ openReconstruct' a b c (Just l) d e

openReconstruct' :: forall op aenv. MakesILP op => LabelEnv aenv -> Graph -> [ClusterLs] -> Maybe Label -> M.Map Label [ClusterLs] -> M.Map Label (Construction op) -> Either (Exists (PreOpenAcc (Cluster op) aenv)) (Exists (PreOpenAfun (Cluster op) aenv))
openReconstruct' labelenv graph clusterslist mlab subclustersmap construct = case mlab of
  Just l  -> Right $ makeASTF labelenv l mempty
  Nothing -> Left $ makeAST labelenv clusters mempty
  where
    -- Make a tree of let bindings

    -- In mkFullGraph, we make sure that the bound body of a let will be in an earlier cluster.
    -- Those are stored in the 'prev' argument.
    -- Note also that we currently assume that the final cluster is the return argument: If all computations are relevant
    -- and our analysis is sound, the return argument should always appear last. If not.. oops
    makeAST :: forall env. LabelEnv env -> [ClusterL] -> M.Map Label (Exists (PreOpenAcc (Cluster op) env)) -> Exists (PreOpenAcc (Cluster op) env)
    makeAST _ [] _ = error "empty AST"
    makeAST env [cluster] prev = case makeCluster env cluster of
      Fold (CCluster args info cio cast) -> Exists $ Exec (Cluster info (Cluster' cio cast)) $ unLabelOp args
      InitFold o args -> unfused o args $
                            \(CCluster args' info cio cast) ->
                                Exists $ Exec (Cluster info (Cluster' cio cast)) (unLabelOp args')
      NotFold con -> case con of
         CExe {}    -> error "should be Fold/InitFold!"
         CExe'{}    -> error "should be Fold/InitFold!"
         CUse se  n be             -> Exists $ Use se n be
         CITE env' c t f   -> case (makeAST env (subcluster t) prev, makeAST env (subcluster f) prev) of
            (Exists tacc, Exists facc) -> Exists $ Acond
              (fromJust $ reindexVar (mkReindexPartial env' env) c)
              -- [See NOTE unsafeCoerce result type]
              (unsafeCoerce @(PreOpenAcc (Cluster op) env _)
                            @(PreOpenAcc (Cluster op) env _)
                            tacc)
              (unsafeCoerce @(PreOpenAcc (Cluster op) env _)
                            @(PreOpenAcc (Cluster op) env _)
                            facc)
         CWhl env' c b i u -> case (subcluster c, subcluster b) of
           (findTopOfF -> c', findTopOfF -> b') -> case (makeASTF env c' prev, makeASTF env b' prev) of
            (Exists cfun, Exists bfun) -> Exists $ Awhile
              u
              -- [See NOTE unsafeCoerce result type]
              (unsafeCoerce @(PreOpenAfun (Cluster op) env _)
                            @(PreOpenAfun (Cluster op) env (_ -> PrimBool))
                            cfun)
              (unsafeCoerce @(PreOpenAfun (Cluster op) env _)
                            @(PreOpenAfun (Cluster op) env (_ -> _))
                            bfun)
              (fromJust $ reindexVars (mkReindexPartial env' env) i)
         CLHS {} -> error "let without scope"
         CFun {} -> error "wrong type: function"
         CBod {} -> error "wrong type: function"
         CRet env' vars     -> Exists $ Return      (fromJust $ reindexVars (mkReindexPartial env' env) vars)
         CCmp env' expr     -> Exists $ Compute     (fromJust $ reindexExp  (mkReindexPartial env' env) expr)
         CAlc env' shr e sh -> Exists $ Alloc shr e (fromJust $ reindexVars (mkReindexPartial env' env) sh)
         CUnt env' evar     -> Exists $ Unit        (fromJust $ reindexVar  (mkReindexPartial env' env) evar)
    makeAST env (cluster:ctail) prev =

      -- TODO: use guards to fuse these two identical cases
      case makeCluster env cluster of
      NotFold con -> case con of
        CLHS (mylhs :: MyGLHS a) b u -> case prev M.! b of
          Exists bnd -> createLHS mylhs env $ \env' lhs ->
            case makeAST env' ctail (M.map (\(Exists acc) -> Exists $ weakenAcc lhs acc) prev) of
              Exists scp
                | bnd' <- unsafeCoerce @(PreOpenAcc (Cluster op) env _) -- [See NOTE unsafeCoerce result type]
                                       @(PreOpenAcc (Cluster op) env a)
                                       bnd
                  -> Exists $ Alet lhs
                      u -- (makeUniqueness lhs bnd') -- TODO @Ivo: `u` is the old uniquenesses of this lhs, do we just take that?
                      bnd'
                      scp
        _ -> let res = makeAST env [cluster] prev in case cluster of
                ExecL _ -> case (res, makeAST env ctail prev) of
                  (Exists exec@Exec{}, Exists scp) -> Exists $ Alet LeftHandSideUnit (shared TupRunit) exec scp
                  _ -> error "nope"
                NonExecL _ -> makeAST env ctail $ foldC (`M.insert` res) prev cluster
      _   -> let res = makeAST env [cluster] prev in case cluster of
                ExecL _ -> case (res, makeAST env ctail prev) of
                  (Exists exec@Exec{}, Exists scp) -> Exists $ Alet LeftHandSideUnit (shared TupRunit) exec scp
                  _ -> error "nope"
                NonExecL _ -> makeAST env ctail $ foldC (`M.insert` res) prev cluster

    makeASTF :: forall env. LabelEnv env -> Label -> M.Map Label (Exists (PreOpenAcc (Cluster op) env)) -> Exists (PreOpenAfun (Cluster op) env)
    makeASTF env l prev = case makeCluster env (NonExecL l) of
      NotFold CBod -> case makeAST env (subcluster l) prev of
        --  fromJust $ l' ^. parent) prev of 
        Exists acc -> Exists $ Abody acc
      NotFold (CFun lhs l') -> createLHS lhs env $ \env' lhs' -> case makeASTF env' l' (M.map (\(Exists acc) -> Exists $ weakenAcc lhs' acc) prev) of
        Exists fun -> Exists $ Alam lhs' fun
      NotFold {} -> error "wrong type: acc"
      _ -> error "not a notfold"

    findTopOfF :: [ClusterL] -> Label
    findTopOfF [] = error "empty list"
    findTopOfF [NonExecL x] = x
    findTopOfF (x@(NonExecL l):xs) = case construct M.! l of
      CBod -> findTopOfF xs
      CFun _ l' -> findTopOfF $ filter (\(NonExecL l'') -> l'' /= l') xs ++ [x]
      _ -> error "should be a function"
      -- findTopOfF $ filter (\(NonExecL l) -> Just l /= p) xs ++ [x]
    findTopOfF _ = error "should be a function"

    -- do the topological sorting for each set
    -- TODO: add 'backend-specific' edges to the graph for sorting, see 3.3.1 in the PLDI paper
    clusters = concatMap (\case
                      Execs ls -> topSort graph ls
                      NonExec l -> [NonExecL l]) clusterslist
    subclusters = M.map (concatMap ( \case
                      Execs ls -> topSort graph ls
                      NonExec l -> [NonExecL l])) subclustersmap
    subcluster l = subclusters M.! l

    makeCluster :: LabelEnv env -> ClusterL -> FoldType op env
    makeCluster env (ExecL ls) =
       foldr1 (flip fuseCluster)
                    $ map ( \l -> case construct M.! l of
                              -- At first thought, this `fromJust` might error if we fuse an array away.
                              -- It does not: The array will still be in the environment, but after we finish
                              -- the `foldr1`, the input argument will dissapear. The output argument does not:
                              -- we clean that up in the SLV pass, if this was vertical fusion. If this is diagonal fusion,
                              -- it stays.
                              CExe env' args op -> InitFold op (fromJust $ reindexLabelledArgsOp (mkReindexPartial env' env) args)
                              _                 -> error "avoid this next refactor" -- c -> NotFold c
                          ) ls
    makeCluster _ (NonExecL l) = NotFold $ construct M.! l

    fuseCluster :: FoldType op env -> FoldType op env -> FoldType op env
    fuseCluster (Fold cluster) (InitFold op largs) =
      consCluster largs cluster op Fold
    fuseCluster (InitFold op largs) x = unfused op largs $ \c -> fuseCluster (Fold c) x
    fuseCluster Fold{} Fold{} = error "fuseCluster got non-leaf as second argument" -- Should never happen
    fuseCluster NotFold{}   _ = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters
    fuseCluster _   NotFold{} = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters

weakenAcc :: LeftHandSide s t env env' -> PreOpenAcc op env a -> PreOpenAcc op env' a
weakenAcc lhs =  runIdentity . reindexAcc (weakenReindex $ weakenWithLHS lhs)


-- | Internal datatype for `makeCluster`.

data FoldType op env
  = forall args. Fold (ConstructingCluster op args env)
  | forall args. InitFold (op args) (LabelledArgsOp op env args)
  | NotFold (Construction op)

-- contains all elements of a Cluster and the LabelledArgsOp
data ConstructingCluster op args env where
  CCluster :: LabelledArgsOp op env args
           -> BackendCluster op args -- you can get this from the labelledargs, why is it here?
           -> ClusterIO args input output
           -> ClusterAST op input output
           -> ConstructingCluster op args env

unfused :: MakesILP op => op args -> LabelledArgsOp op env args -> (forall args'. ConstructingCluster op args' env -> r) -> r
unfused op largs = consCluster largs (CCluster ArgsNil ArgsNil Empty None) op

consCluster :: forall env args extra op r
             . MakesILP op
            => LabelledArgsOp op env extra
            -> ConstructingCluster op args env
            -> op extra
            -> (forall args'. ConstructingCluster op args' env -> r)
            -> r
consCluster lextra (CCluster largs _ cIO cAST) op k = -- we can ignore the BackendCluster that is already present, because the same information is also in the `largs`
  mkReverse lextra $ \rev lartxe->
    consCluster' largs rev lartxe cAST (mkBase cIO) cIO
  where
    -- The new, extra operation has args `extra`.
    -- We have already added the args in `added`,
    -- but still need to add the args in `toAdd`.
    -- In total, we now have a (decomposed) cluster of args `total`:
    -- The CIO divides it into `i` and `o`,
    -- The CAST contains the existing computation from `scope` to `o`,
    -- whereas the `LHSArgs` cons' the `added` args in front using `i`.

    -- We simply recurse down the `toAdd` args until `toAdd ~ ()` and
    -- `added ~ extra`, when we can use the extra operation to construct
    -- the total cluster. All results are passed in these accumulating parameters.

    -- In each step, we check whether the argument array is already mentioned
    -- in the operations that follow it: If so, we fuse them (making both arguments
    -- point to the same place in the environment), otherwise we simply add a new one. 

    -- note that this function has a lot of type safety (recursing wrongly is very difficult),
    -- except for two details: Whether or not to fuse is a choice, and the call to `k`
    -- works with any cluster/args. The first requires diligence, the second occurs
    -- only in the very first line (which is, visually, correct).
    consCluster' :: LabelledArgsOp op env total
                 -> Reverse' extra added toAdd
                 -> LabelledArgsOp op env toAdd
                 -> ClusterAST op scope o
                 -> LeftHandSideArgs added i scope
                 -> ClusterIO total i o
                 -> r
    consCluster' ltot Ordered ArgsNil ast lhs io = k $ CCluster ltot (mapArgs getClusterArg ltot) io (Bind lhs op ast)
    consCluster' ltot (Revert r) (a :>: toAdd) ast lhs io = case a of
      LOp (ArgArray In  _ _ _) _ _ -> consInArg  a ltot lhs ast io $ \ltot' -> consCluster' ltot' r toAdd
      LOp (ArgArray Out _ _ _) _ _ -> consOutArg a ltot lhs ast io $ \ltot' -> consCluster' ltot' r toAdd
      -- non-array arguments
      LOp (ArgExp _)           _ _ -> let (io', ast') = addExp io ast ExpPut in consCluster' (a :>: ltot) r toAdd ast' (EArg lhs) io'
      LOp (ArgVar _)           _ _ -> let (io', ast') = addExp io ast VarPut in consCluster' (a :>: ltot) r toAdd ast' (VArg lhs) io'
      LOp (ArgFun _)           _ _ -> let (io', ast') = addExp io ast FunPut in consCluster' (a :>: ltot) r toAdd ast' (FArg lhs) io'
      LOp (ArgArray Mut _ _ _) _ _ -> let (io', ast') = addExp io ast MutPut in consCluster' (a :>: ltot) r toAdd ast' (Adju lhs) io'

-- remove an argument
foo :: Take' (x sh e) total total' -> LabelledArgsOp op env total -> PreArgs (LabelledArgOp op env) total'
foo Here' (_ :>: as) = as
foo (There' t) (a :>: as) = a :>: foo t as


-- Incrementally applying arguments reverses their order, which makes the types messy.
-- As a solution, we first reverse the arguments to be added, so that we end up
-- with the original order! This datatype keeps track of the proof that peeling off args
-- one-by-one from the reversed type yields the original type, which matches the operation.
-- 
-- Building a `Reverse` (and the initial reversing) is awkward, which is why we have `mkReverse`.
-- Using them (peeling off Revert until we're done) is much easier, and happens in the recursion
-- of `consCluster'`.
type Reverse xs sx = Reverse' xs () sx
data Reverse' tot acc rev where
  Ordered :: Reverse' tot     tot       ()
  Revert  :: Reverse' tot (a -> x)      y
          -> Reverse' tot       x (a -> y)

mkReverse :: forall env xs op r
           . LabelledArgsOp op env xs
          -> (forall sx. Reverse xs sx -> LabelledArgsOp op env sx -> r)
          -> r
mkReverse xs k = rev Ordered ArgsNil xs
  where
    rev :: Reverse' xs ys zs
        -> LabelledArgsOp op env zs
        -> LabelledArgsOp op env ys
        -> r
    rev a zs ArgsNil = k a zs
    rev a zs (arg :>: args) = rev (Revert a) (arg :>: zs) args

-- for each buffer in the arg, this will either fuse it with an existing input buffer or add a new one
consInArg :: MakesILP op
         => LabelledArgOp op env (In sh e)
         -> LabelledArgsOp op  env total
         -> LeftHandSideArgs added i scope
         -> ClusterAST op scope o
         -> ClusterIO total i o
         -> (forall total' i' o' scope'
            . LabelledArgsOp op env total'
           -> ClusterAST op scope' o'
           -> LeftHandSideArgs (In sh e -> added) i' scope'
           -> ClusterIO total' i' o'
           -> r)
         -> r
consInArg a@(LOp (ArgArray In (ArrayR _ TupRunit) _ _) _ _) ltot lhs ast io k =
  k (a:>:ltot) (weakenAST ast) (Triv lhs) (Trivial io)
consInArg (LOp (ArgArray In (ArrayR sh (TupRpair l r)) sh' (TupRpair bufL bufR)) (Arr (TupRpair el er), _) b) ltot lhs ast io k =
  consInArg (LOp (ArgArray In (ArrayR sh l) sh' bufL) (Arr el, mempty) b) ltot lhs ast io $
    \ltot' ast' lhs' io' ->
      consInArg (LOp (ArgArray In (ArrayR sh r) sh' bufR) (Arr er, mempty) b) ltot' lhs' ast' io' $
        \ltot'' ast'' lhs'' io'' ->
            k ltot'' ast'' (squish lhs'') io''
consInArg a@(LOp (ArgArray In (ArrayR _ (TupRsingle _)) _ _) (Arr (TupRsingle (C.Const _)), _) _) ltot lhs ast io k =
  maybe
    (let (ast', io') = addInput ast io
    in k (a :>: ltot) ast' (Reqr (TupRsingle $ IdxF ZeroIdx) (TupRsingle $ IdxF ZeroIdx) $ Ignr lhs) io')
    (\lhs' -> k ltot ast lhs' io)
    (fuseInput a ltot lhs io)
consInArg _ _ _ _ _ _ = error "impossible combination of TypeR, ALabels and TupR Buffer"


-- Only works if the top of the lhsargs only contains Reqr and Ignr! This is the case in @consInArg@
squish :: LeftHandSideArgs (In sh b -> In sh a -> args) i o -> LeftHandSideArgs (In sh (a,b) -> args) i o
squish = \case
  (Ignr lhs) -> Ignr (squish lhs)
  (Reqr t1 t2 lhs) -> case go lhs of
    Left (Reqr t3 t4 lhs') -> Reqr (TupRpair t3 t1) (TupRpair t4 t2) lhs'
    Right (Refl, lhs') -> Reqr (TupRpair TupRunit t1) (TupRpair TupRunit t2) lhs'
    _ -> error "go should always give a Reqr/triv"
  (Triv lhs) -> case go lhs of
    Left (Reqr t1 t2 lhs') -> Ignr $ Reqr (TupRpair t1 TupRunit) (TupRpair t2 TupRunit) lhs'
    Right (Refl, _) -> error "change type of Triv to support this"
  _ -> error "squish encountered non-reqr, non-ignr, non-triv"
  where
    -- search for the second reqr and weaken it up above the ignrs, or IGNoRe the Triv
    go :: LeftHandSideArgs (In sh a -> args) i o -> Either (LeftHandSideArgs (In sh a -> args) i o) (a:~:(), LeftHandSideArgs args i o)
    go (Reqr a b c) = Left $ Reqr a b c
    go (Triv lhs') = Right (Refl, Ignr lhs')
    go (Ignr lhs') = case go lhs' of
      Left (Reqr a b lhs'') -> Left $ Reqr (mapTupR succIdxF a) (mapTupR succIdxF b) $ Ignr lhs''
      Right (Refl, lhs'') -> Right (Refl, Ignr lhs'')
      _ -> error "go should always give a reqr/triv"


consOutArg :: MakesILP op
           => LabelledArgOp op env (Out sh e)
           -> LabelledArgsOp op  env total
           -> LeftHandSideArgs added i scope
           -> ClusterAST op scope o
           -> ClusterIO total i o
           -> (forall total' i' o' scope'
               . LabelledArgsOp op env total'
              -> ClusterAST op scope' o'
              -> LeftHandSideArgs (Out sh e -> added) i' scope'
              -> ClusterIO total' i' o'
              -> r)
           -> r
consOutArg a@(LOp (ArgArray Out (ArrayR _ TupRunit) _ _) _ _) ltot lhs ast io k =
  addOutput a ltot ast io lhs $ \ast' io' ltot' lhs' ->
    k ltot' ast' lhs' io'
consOutArg (LOp (ArgArray Out (ArrayR sh (TupRpair l r)) sh' (TupRpair bufL bufR)) (Arr (TupRpair el er), _) b) ltot lhs ast io k =
  case (l,r) of
    (TupRunit, TupRunit) -> error "change Triv's type to support this"
    (TupRunit, _) -> consOutArg (LOp (ArgArray Out (ArrayR sh r) sh' bufR) (Arr er, mempty) b) ltot lhs ast io $
      \ltot'' ast'' (Make t1 t2 lhs'') io'' -> k ltot'' ast'' (Make (TakePair TakeUnit t1) (ConsPair ConsUnit t2) lhs'') io'' 
    (_, TupRunit) -> consOutArg (LOp (ArgArray Out (ArrayR sh l) sh' bufL) (Arr el, mempty) b) ltot lhs ast io $
      \ltot'' ast'' (Make t1 t2 lhs'') io'' -> k ltot'' ast'' (Make (TakePair t1 TakeUnit) (ConsPair t2 ConsUnit) lhs'') io''
    _ -> consOutArg (LOp (ArgArray Out (ArrayR sh l) sh' bufL) (Arr el, mempty) b) ltot lhs ast io $
      \ltot' ast' lhs' io' -> 
        consOutArg (LOp (ArgArray Out (ArrayR sh r) sh' bufR) (Arr er, mempty) b) ltot' lhs' ast' io' $
          \ltot'' ast'' (Make t1 t2 (Make t3 t4 lhs'')) io'' -> 
            k ltot'' ast'' (Make (TakePair t3 t1) (ConsPair t4 t2) lhs'') io''
consOutArg a@(LOp (ArgArray Out (ArrayR _ (TupRsingle _)) _ _) (Arr (TupRsingle (C.Const _)), _) _) ltot lhs ast io k =
  addOutput a ltot ast io lhs $ \ast' io' ltot' lhs' ->
    k ltot' ast' lhs' io'
consOutArg _ _ _ _ _ _ = error "impossible combination of TypeR, ALabels and TupR Buffer"


addOutput :: MakesILP op
          => LabelledArgOp op env (Out sh e)
          -> LabelledArgsOp op env total
          -> ClusterAST op scope o
          -> ClusterIO total i o
          -> LeftHandSideArgs added i scope
          -> (forall o' total' i' scope'
              . ClusterAST op scope' o'
             -> ClusterIO (Out sh e -> total') i' o'
             -> LabelledArgsOp op env (Out sh e -> total')
             -> LeftHandSideArgs (Out sh e -> added) i' scope'
             -> r)
          -> r
addOutput a@(LOp (ArgArray Out (ArrayR _ TupRunit) _ _) _ _) ltot ast io lhs k
  = k (weakenAST ast) (Trivial io) (a :>: ltot) (Triv lhs)
addOutput a@(LOp (ArgArray Out (ArrayR _ ty) _ _) _ _) ltot ast io lhs k
  | Just r <- checkDiagonalFusion a ltot $ \t -> applyDiagonalFusion t io lhs ty $ \io' lhs' _ -> k ast io' (a :>: foo t ltot) lhs'
  = r -- diagonal fusion
  | otherwise -- no fusion
  = k (weakenAST ast) (Output Here SubTupRkeep ty io) (a :>: ltot) (Make (TakeSingle Here) ConsSingle lhs)

-- Takes the corresponding input argument out, for diagonal fusing.
checkDiagonalFusion :: MakesILP op
                    => LabelledArgOp op env (Out sh e)
                    -> LabelledArgsOp op env total
                    -> (forall total'. Take' (In sh e) total total' -> r)
                    -> Maybe r
checkDiagonalFusion _ ArgsNil _ = Nothing
checkDiagonalFusion (LOp _ (a1, _) o1) (LOp (ArgArray In _ _ _) (a2, _) o2 :>: _) k
  | Just Refl <- matchALabel a1 a2
  , o1 == o2 = Just $ k Here'
checkDiagonalFusion arg (_ :>: args) k = checkDiagonalFusion arg args $ k . There'

-- the IO now gets an output and no input
-- the LHS gets a Sh instead of a Value for input
-- We half-shuffle: The input of this lhs changes from Value to Sh and it gets moved to the front
-- but the output of this lhs stays intact
applyDiagonalFusion :: ()
                    => Take' (In sh e) total total'
                    -> ClusterIO total i o
                    -> LeftHandSideArgs added i scope
                    -> TypeR e
                    -> (forall i'
                        . ClusterIO (Out sh e -> total') (i', Sh sh e) o
                       -> LeftHandSideArgs (Out sh e -> added) (i', Sh sh e) scope
                       -> Take (Value sh e) i i'
                       -> r)
                    -> r
-- base cases
applyDiagonalFusion _ _ _ TupRpair{} _ = error "pair"
applyDiagonalFusion _ _ _ TupRunit   _ = error "trivial: we don't bother fusing unit arrays, the duplication of shape info gets simplified away later (I think)"
applyDiagonalFusion Here' (Input io) (Ignr lhs) (TupRsingle ty) k = k (Output Here SubTupRkeep (TupRsingle ty) io) (Make (TakeSingle Here) ConsSingle lhs) Here
-- recursive cases
applyDiagonalFusion t io (Make tb1 tb2 lhs) ty k =
  pastOutputs tb1 tb2 t io $ \t' io' iok ->
    applyDiagonalFusion t' io' lhs ty $ \(Output a b c io'') (Make (TakeSingle ts) ConsSingle lhs') t1 ->
      -- _ tb1 $ \ tb1' ->
        iok t1 a io'' ts $ \a' io''' t1' ts' tb1' tb2' ->
          k (Output a' b c io''') (Make (TakeSingle ts') ConsSingle $ Make tb1' tb2' lhs') t1'
-- Reqr:
applyDiagonalFusion t io (Reqr ti to lhs) ty k =
  applyDiagonalFusion t io lhs ty $ \io' (Make (TakeSingle ts) ConsSingle lhs') t1 ->
    -- these takeStrengthenF's can only fail when this operation was already using its own output
    k io' (Make (TakeSingle ts) ConsSingle $ Reqr (mapTupR (`takeStrengthenF` t1) ti) (mapTupR (`takeStrengthenF` ts) to) lhs') t1
-- Ignr:
applyDiagonalFusion (There' t) (Input        io) (Ignr lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 ->                       k (Output (There a) b c $ Input   io') (Make (tbThere ts) ConsSingle $ Ignr lhs') (There t1)
applyDiagonalFusion (There' t) (ExpPut       io) (Ignr lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 ->                       k (Output (There a) b c $ ExpPut  io') (Make (tbThere ts) ConsSingle $ Ignr lhs') (There t1)
applyDiagonalFusion (There' t) (VarPut       io) (Ignr lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 ->                       k (Output (There a) b c $ VarPut  io') (Make (tbThere ts) ConsSingle $ Ignr lhs') (There t1)
applyDiagonalFusion (There' t) (Trivial      io) (Ignr lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 ->                       k (Output (There a) b c $ Trivial io') (Make (tbThere ts) ConsSingle $ Ignr lhs') (There t1)
applyDiagonalFusion (There' t) (FunPut       io) (Ignr lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 ->                       k (Output (There a) b c $ FunPut  io') (Make (tbThere ts) ConsSingle $ Ignr lhs') (There t1)
applyDiagonalFusion (There' t) (MutPut       io) (Ignr lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 ->                       k (Output (There a) b c $ MutPut  io') (Make (tbThere ts) ConsSingle $ Ignr lhs') (There t1)
applyDiagonalFusion (There' t) (Output x y z io) (Ignr lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 -> ttake a x $ \a' x' -> k (Output a' b c $ Output x' y z  io') (Make (tbThere ts) ConsSingle $ Ignr lhs') (There t1)
applyDiagonalFusion (There' t) (Vertical x y io) (Ignr lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 -> ttake a x $ \a' x' -> k (Output a' b c $ Vertical x' y  io') (Make (tbThere ts) ConsSingle $ Ignr lhs') (There t1)
-- Adju, EArg, VArg, FArg are timilar to Ignr:
applyDiagonalFusion (There' t) (MutPut       io) (Adju lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 ->                       k (Output (There a) b c $ MutPut  io') (Make (tbThere ts) ConsSingle $ Adju lhs') (There t1)
applyDiagonalFusion (There' t) (ExpPut       io) (EArg lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 ->                       k (Output (There a) b c $ ExpPut  io') (Make (tbThere ts) ConsSingle $ EArg lhs') (There t1)
applyDiagonalFusion (There' t) (VarPut       io) (VArg lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 ->                       k (Output (There a) b c $ VarPut  io') (Make (tbThere ts) ConsSingle $ VArg lhs') (There t1)
applyDiagonalFusion (There' t) (Trivial      io) (VArg lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 ->                       k (Output (There a) b c $ Trivial io') (Make (tbThere ts) ConsSingle $ VArg lhs') (There t1)
applyDiagonalFusion (There' t) (FunPut       io) (FArg lhs) ty k = applyDiagonalFusion t io lhs ty $ \(Output a b c io') (Make ts ConsSingle lhs') t1 ->                       k (Output (There a) b c $ FunPut  io') (Make (tbThere ts) ConsSingle $ FArg lhs') (There t1)

applyDiagonalFusion Here' _ _ _ _ = error "This operation wasn't igoring its own output"



ttb :: Take x a b -> ConsBuffers f y c a -> (forall d. Take x c d -> ConsBuffers f y d b -> r) -> r
ttb t ConsUnit k = k t ConsUnit
ttb t ConsSingle k = k (There t) ConsSingle
ttb t (ConsPair l r) k =
  ttb t l $ \t' l' ->
    ttb t' r $ \t'' r' ->
      k t'' (ConsPair l' r')

weakenAST :: ClusterAST op scope o -> ClusterAST op (scope, x) (o, x)
weakenAST None = None
weakenAST (Bind lhs op ast) = Bind (Ignr lhs) op $ weakenAST ast

--Only call this with a single buffer!
fuseInput :: MakesILP op
          => LabelledArgOp op env (In sh e)
          -> LabelledArgsOp op  env total
          -> LeftHandSideArgs added i scope
          -> ClusterIO total i result
          -> Maybe (LeftHandSideArgs (In sh e -> added) i scope)
-- Base case, no fusion
fuseInput _ ArgsNil _ Empty = Nothing
-- The happy path: Fusion!
fuseInput
  (LOp _ (a1, _) o1)
  (LOp (ArgArray In _ _ _) (a2, _) o2 :>: _)
  (Ignr lhs)
  (Input _)
  | Just Refl <- matchALabel a1 a2
  , o1 == o2 =
    Just $ Reqr (TupRsingle $ IdxF ZeroIdx) (TupRsingle $ IdxF ZeroIdx) $ Ignr lhs
-- The rest are recursive cases
fuseInput x as (Make t1 t2 lhs) io =
  peelOutputs as t1 t2 io $ \io' as' ->
    (\(Reqr a b c) -> Reqr (mapTupR (weaken $ cbWeaken t2) a) (mapTupR (weaken $ tbWeaken t1) b) (Make t1 t2 c))
    <$> fuseInput x as' lhs io'
fuseInput x as (Reqr t t2 lhs) io = (\(Reqr a b c) -> Reqr a b (Reqr t t2 c)) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Adju lhs) (MutPut       io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ Adju c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (EArg lhs) (ExpPut'      io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ EArg c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (VArg lhs) (ExpPut'      io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ VArg c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (FArg lhs) (ExpPut'      io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ FArg c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (VArg lhs) (Trivial      io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ VArg c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Triv lhs) (Trivial      io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ Triv c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (Output _ _ _ io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ Ignr c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (Input        io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ Ignr c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (MutPut       io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ Ignr c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (ExpPut'      io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ Ignr c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (Vertical _ _ io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ Ignr c) <$> fuseInput x as lhs io
fuseInput x (_ :>: as) (Ignr lhs) (Trivial      io) = (\(Reqr a b c) -> Reqr (there' a) (there' b) $ Ignr c) <$> fuseInput x as lhs io

-- also peels verticals and trivials
peelOutputs :: LabelledArgsOp op env total
            -> TakeBuffers (Value sh) e eo o
            -> ConsBuffers (Sh sh) e shi i
            -> ClusterIO total shi result
            -> (forall t' result'
               . ClusterIO t' i result'
              -> LabelledArgsOp op env t'
              -> r)
            -> r
peelOutputs ltot TakeUnit ConsUnit io k = k io ltot
peelOutputs ltot (TakePair l1 r1) (ConsPair l2 r2) io k =
  peelOutputs ltot r1 r2 io $ \io' ltot' ->
    peelOutputs ltot' l1 l2 io' $ \io'' ltot'' ->
      k io'' ltot''
peelOutputs (_ :>: ltot) (TakeSingle _) ConsSingle (Output _ _ _ io) k = k io ltot
peelOutputs (_ :>: ltot) (TakeSingle _) ConsSingle (Vertical _ _ io) k = k io ltot
peelOutputs _ TakeUnit     ConsSingle _ _ = error "unit in single"
peelOutputs _ TakeSingle{} ConsUnit   _ _ = error "unit in single"
peelOutputs _ TakeSingle{} ConsPair{} _ _ = error "pair in single"
peelOutputs _ TakePair{}   ConsSingle _ _ = error "pair in single"
-- peelOutputs _ _ ConsUnitFusedAway{} _ _ = error "impossible here"

-- go past outputs and verticals and trivials, and give a continuation which slaps them back on
pastOutputs :: TakeBuffers (Value sh) e eo o
            -> ConsBuffers (Sh sh) e shi i
            -> Take' (In sh2 e2) total total'
            -> ClusterIO total shi result
            -> (forall t' t'' result'
               . Take' (In sh2 e2) t' t''
              -> ClusterIO t' i result'
              -> (forall sh1 e1 i' b r2 o'
                 . Take (Value sh1 e1) i i'
                -> Take (Value sh1 e1) result' b
                -> ClusterIO t'' i' b
                -> Take (Value sh1 e1) o o'
                -> (forall a' b' o2
                   . Take (Value sh1 e1) result b'
                  -> ClusterIO total' a' b'
                  -> Take (Value sh1 e1) shi a'
                  -> Take (Value sh1 e1) eo o2
                  -> TakeBuffers (Value sh) e o2 o'
                  -> ConsBuffers (Sh sh) e a' i'
                  -> r2)
                -> r2)
              -> r)
            -> r
-- trivial recursive case, as a warmup to the nested existentials
-- pastOutputs tb1 tb2 (There' t) (Trivial io) k =
--   pastOutputs tb1 tb2 t io $ \t' io' iok ->
--     k t' io' $ \t1 t2 io'' t3 k' ->
--       iok t1 t2 io'' t3 $ \t4 io''' t5 t6 tb3 cb ->
--         k' t4 (Trivial io''') t5 t6 tb3 cb
-- takeUnits case, mirror of the trivial case
pastOutputs TakeUnit ConsUnit t io k =
  k t io $ \t1 t2 io' t3 k' ->
    k' t2 io' t1 t3 TakeUnit ConsUnit
-- takeSingles case, the "real" base-case
pastOutputs (TakeSingle ts) ConsSingle (There' take') (Output t st ty io) k =
  k take' io $ \t1 t2 io' t3 k' ->
    ttake t2 t $ \t2' t' ->
      ttake t3 ts $ \t3' ts' ->
        k' t2' (Output t' st ty io') (There t1) t3' (TakeSingle ts') ConsSingle
-- the same for vertical
pastOutputs (TakeSingle ts) ConsSingle (There' take') (Vertical t a io) k =
  k take' io $ \t1 t2 io' t3 k' ->
    ttake t2 t $ \t2' t' ->
      ttake t3 ts $ \t3' ts' ->
        k' t2' (Vertical t' a io') (There t1) t3' (TakeSingle ts') ConsSingle
-- takePair case: the double recursion
pastOutputs (TakePair l1 r1) (ConsPair l2 r2) t io k =
  pastOutputs r1 r2 t io $ \t' io' iok ->
    pastOutputs l1 l2 t' io' $ \t'' io'' iok' ->
      k t'' io'' $ \t1 t2 io''' t3 k' ->
        iok' t1 t2 io''' t3 $ \t4 io'''' t5 t6 tb1 cb1 ->
          iok t5 t4 io'''' t6 $ \t7 io5 t8 t9 tb2 cb2 ->
            k' t7 io5 t8 t9 (TakePair tb1 tb2) (ConsPair cb1 cb2)
pastOutputs _ _ _ _ _ = error "A unit or pair was hiding in a TakeSingle, I think"

-- Only call for a single buffer!
addInput  :: ClusterAST op scope o
          -> ClusterIO total i o
          -> (ClusterAST op (scope, Value sh e) (o, Value sh e)
            , ClusterIO (In sh e -> total) (i, Value sh e) (o, Value sh e))
addInput None io = (None, Input io)
addInput (Bind lhs op ast) io = first (Bind (Ignr lhs) op) $ addInput ast io

-- use one of the IO constructors {ExpPut, VarPut, FunPut} as third argument
addExp  :: ClusterIO total i o
        -> ClusterAST op scope o
        -> (forall total' i' o'. ClusterIO total' i' o' -> ClusterIO (e -> total') (i', e) (o', e))
        -> ( ClusterIO (e -> total) (i, e) (o, e)
           , ClusterAST op (scope, e) (o, e)
           )
addExp io None constructor = (constructor io, None)
addExp io (Bind lhs op ast) constructor = second (Bind (Ignr lhs) op) $ addExp io ast constructor



{- [NOTE unsafeCoerce result type]

  Because we lose some type information by rebuilding the AST from scratch, we use
  unsafeCoerce to tell GHC what the result type of the computation is.
  TypeApplications allows us to specify the exact types unsafeCoerce works on,
  which in turn helps retain as much typesafety as possible. Whereever this note
  is found, unsafeCoerce's type is restricted to only work on the result type.
  In particular, we take care to not allow unsafeCoerce to mess with environment types,
  as they are tricky to get right and we really want GHC to check our work.

-}

tryUpdateList :: (a -> Bool) -> (a -> a) -> [a] -> Maybe [a]
tryUpdateList _ _ [] = Nothing
tryUpdateList p f (x : xs)
  | p x = Just $ f x : xs
  | otherwise = tryUpdateList p f xs







--------------------------------------------------------------------------------------

-- data Combine' first second rest total where
--   Horizontal :: Combine (In  a) (In a) xs (In  a, xs)
--   Diagonal   :: Combine (Out a) (In a) xs (Out a, xs)
--   Vertical   :: Combine (Out a) (In a) xs         xs

-- data Combine first second fused where
--   BaseCase  :: Combine () () ()
--   Fusion    :: Combine' a b rest fused 
--             -> Combine     as      bs      rest 
--             -> Combine (a, as) (b, bs)     fused
--   Intro1    :: Combine     as      bs      fused 
--             -> Combine (a, as)     bs  (a, fused)
--   Intro2    :: Combine     as      bs      fused 
--             -> Combine     as  (b, bs) (a, fused)

-- data AlternativeCluster op args where
--   Singleton :: op args -> SortArgs args sorted -> AlternativeCluster op sorted
--   Multiple :: Combine first second args 
--            -> AlternativeCluster op first 
--            -> AlternativeCluster op second 
--            -> AlternativeCluster op args

-- type SortArgs args sorted = () -- TODO: some datatype which describes the permutation of those arguments
