{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve where


import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
    (Label, parent, Labels )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver

import Data.List (groupBy, sortOn)
import Prelude hiding ( pi )

import qualified Data.Map as M

-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S
import Data.Function ( on )
import Lens.Micro ((^.),  _1 )
import Lens.Micro.Extras ( view )
import Data.Maybe (fromJust,  mapMaybe )
import Control.Monad.State
import Data.Array.Accelerate.Trafo.Partitioning.ILP.NameGeneration (freshName)
import Data.Foldable

-- Any edge of this form will either be trivial (if fusible) or impossible (if infusible). 
-- They originate from the smart constructor -?>, which is not quite smart enough: It should really perform this check,
-- but then it returns a Maybe Edge, which requires refactoring.. So we simply filter all of those out in this step instead.
trimIds :: S.Set Edge -> S.Set Edge
trimIds = S.filter (\(x:->y) -> x /= y)

-- Makes the ILP. Note that this function 'appears' to ignore the Label levels completely!
-- We could add some assertions, but if all the input is well-formed (no labels, constraints, etc
-- that reward putting non-siblings in the same cluster) this is fine: We will interpret 'cluster 3'
-- with parents `Nothing` as a different cluster than 'cluster 3' with parents `Just 5`.
makeILP :: forall op. MakesILP op => Information op -> ILP op
makeILP (Info
          (Graph nodes (trimIds -> fuseEdges') (trimIds -> nofuseEdges))
          backendconstraints
          backendbounds
        ) = combine graphILP
  where
    -- Remove any redundant 'fusible' edges
    fuseEdges = fuseEdges' S.\\ nofuseEdges

    combine :: ILP op -> ILP op
    combine (ILP dir fun cons bnds _) =
             ILP dir fun (cons <> backendconstraints)
                         (bnds <> backendbounds)
                         n
    -- n is used in some of the constraints, as an upperbound on the number of clusters.
    -- We add a small constant to be safe, as some variables have ranges from -3 to number of nodes.
    n :: Int
    n = 5 + S.size nodes

    graphILP = ILP Minimise objFun myConstraints myBounds n

    -- Since we want all clusters to have one 'iteration size', the final objFun should
    -- take care to never reward 'fusing' disjoint clusters, and then slightly penalise it.
    -- The alternative is O(n^2) edges, so this is worth the trouble!
    --
    -- In the future, maybe we want this to be backend-dependent (add to MakesILP).
    -- Also future: add @IVO's IPU reward here.
    objFun :: Expression op
    objFun = minimiseArrayReadsWrites

    -- objective function that maximises the number of edges we fuse, and minimises the number of array reads if you ignore horizontal fusion
    maximiseNumberOfFusedEdges = foldl' (\f (i :-> j) -> f .+. fused i j)
                    (int 0)
                    (S.toList fuseEdges)

    -- A cost function that doesn't ignore horizontal fusion.
    -- Idea: Each node $x$ with $n$ outgoing edges gets $n$ extra variables.
    -- Each edge (fused or not) $(x,y)$ will require that one of these variables is equal to $pi y$.
    -- The number of extra variables that are equal to 0 (the thing you maximise) is exactly equal to n - the number of clusters that read from $x$.
    -- Then, we also need n^2 intermediate variables just to make these disjunction of conjunctions 
    -- note, it's only quadratic in the number of consumers of a specific array.
    -- TODO: Because of backpermute, we actually need twice as many extra variables, where the second version is for the order it is accessed.
    -- problem: backpermutes live in the backend specific variables currently
    minimiseNumberOfReads = nReads
    (nReads, readConstraints, readBounds) = 
        foldl (\(a,b,c) (d,e,f)->(a.+.d,b<>e,c<>f)) (int 0, mempty, mempty)
      . flip evalState ""
      . forM (S.toList nodes) $ \l -> do
      let consumers  = map (\(_ :-> j) -> j) . S.toList $ S.filter (\(i :-> _) -> i == l) fuseEdges
          nConsumers = length consumers
      readPis <- replicateM nConsumers readPiVar
      (subConstraint, subBounds) <- flip foldMapM readPis $ \readPi -> do
        useVars <- replicateM nConsumers useVar -- these are the n^2 variables
        let constraint = foldMap (isEqual (c readPi) (pi l) . c) useVars
        -- note that we set it to be equal to 1 here, >= 1 would also work but that is never optimal
        -- I don't know which version is easier/faster to solve!
        return (constraint <> foldl (.+.) (int 0) (map c useVars) .==. int 1, foldMap binary useVars)
      readPi0s <- replicateM nConsumers readPi0Var
      return ( foldl (.+.) (int 0) (map c readPi0s)
             , subConstraint <> fold (zipWith (\p p0 -> c p .<=. timesN (c p0)) readPis readPi0s)
             , subBounds <> foldMap (\v -> lowerUpper 0 v n) readPis <> foldMap binary readPi0s)

    readPiVar  = Other <$> freshName "ReadPi"
    readPi0Var = Other <$> freshName "Read0Pi"
    useVar = Other <$> freshName "ReadUse"

    -- objective function that maximises the number of fused away arrays, and thus minimises the number of array writes
    maximiseArrayContraction = foldl' (\f l -> f .+. manifest l) (int 0) (S.toList nodes)

    -- objective function that minimises the total number of array reads + writes
    minimiseArrayReadsWrites = minimiseNumberOfReads .+. maximiseArrayContraction

    -- objective function that minimises the number of clusters -- only works if the constraint below it is used!
    minimiseNumberOfClusters  = c (Other "maximumClusterNumber")
    -- removing this from myConstraints makes the ILP slightly smaller, but disables the use of this cost function
    minimiseNumberOfClusters' = foldMap (\l -> pi l .<=. minimiseNumberOfClusters) nodes

    myConstraints = acyclic <> infusible <> manifestC <> finalize (S.toList nodes) <> minimiseNumberOfClusters' <> readConstraints

    -- x_ij <= pi_j - pi_i <= n*x_ij for all edges
    acyclic = foldMap
                (\(i :-> j) -> between
                              ( fused i j )
                              ( pi j .-. pi i )
                              ( timesN $ fused i j ))
                (fuseEdges <> nofuseEdges)
    infusible = foldMap
                  (\(i :-> j) -> fused i j .==. int 1)
                  nofuseEdges

    -- if (i :-> j) is not fused, i has to be manifest
    -- TODO: final output is also manifest
    manifestC = foldMap
                (\(i :-> j) -> notB (fused i j) `impliesB` manifest i)
                (fuseEdges <> nofuseEdges)

    myBounds :: Bounds op
    --            0 <= pi_i <= n
    myBounds = foldMap (\i -> lowerUpper 0 (Pi i) n)
                  (S.toList nodes)
               <>  -- x_ij \in {0, 1}
               foldMap (\(i :-> j) -> binary $ Fused i j)
                  (S.toList $ fuseEdges <> nofuseEdges)
               <>
               foldMap (\(i :-> j) -> binary (ManifestOutput i) <> binary (ManifestOutput j))
                  (S.toList $ fuseEdges <> nofuseEdges)
               <>
               readBounds


-- Extract the fusion information (ordered list of clusters of Labels) (head is the first cluster).
-- Output has the top-level clusters in fst, and the rest in snd.
interpretSolution :: MakesILP op => Solution op -> ([Labels], M.Map Label [Labels])
interpretSolution =
    (\(x:xs) ->
      ( x
      , M.fromList $
            map
            (\l ->
              ( fromJust -- All labels in the Map will have a parent, only the top clusters can have Nothing as parent (depending on whether we have an Acc or an Afun)
              . view parent
              . S.findMin -- `head` and `findMin` just to get _any_ element:
              . head      -- there is at least one and the parents are all identical
              $ l
              , l))
            xs))
  . map
    ( map
      ( S.fromList
      . map fst)
    . partition snd)
  . partition (^. _1.parent)
  . mapMaybe (_1 fromPi)
  . M.toList
  where
    fromPi (Pi l) = Just l
    fromPi _      = Nothing

    -- groupBy only really does what you want on a sorted list
    partition f = groupBy ((==) `on` f) . sortOn f

data ClusterLs = Execs Labels | NonExec Label
  deriving (Eq, Show)

-- I think that only `let`s can still be in the same cluster as `exec`s, 
-- and their bodies should all be in earlier clusters already.
-- Simply make one cluster per let, before the cluster with execs.
-- TODO: split the cluster of Execs into connected components
splitExecs :: ([Labels], M.Map Label [Labels]) -> M.Map Label (Construction op) -> ([ClusterLs], M.Map Label [ClusterLs])
splitExecs (xs, xM) constrM = (f xs, M.map f xM)
  where
    f :: [Labels] -> [ClusterLs]
    f = concatMap (\ls -> filter (/= Execs mempty) $ map NonExec (S.toList $ S.filter isNonExec ls) ++ [Execs (S.filter isExec ls)])

    isExec l = case constrM M.!? l of
      Just CExe{}  -> True
      Just CExe'{} -> True
      _ -> False
    isNonExec l = not $ isExec l



-- Only needs Applicative
newtype MonadMonoid f m = MonadMonoid { getMonadMonoid :: f m }
instance (Monad f, Semigroup m) => Semigroup (MonadMonoid f m) where
  (MonadMonoid x) <> (MonadMonoid y) = MonadMonoid $ (<>) <$> x <*> y
instance (Monad f, Monoid m) => Monoid (MonadMonoid f m) where
  mempty = MonadMonoid (pure mempty)

foldMapM :: (Foldable t, Monad f, Monoid m) => (a -> f m) -> t a -> f m
foldMapM f = getMonadMonoid . foldMap (MonadMonoid . f)
