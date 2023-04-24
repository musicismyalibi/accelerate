{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo (

  -- * HOAS -> de Bruijn conversion
  -- ** Array computations
  convertAcc, convertAccWith,

  -- ** Array functions
  Afunction, ArraysFunctionR,
  convertAfun, convertAfunWith,

  -- ** Sequence computations
  -- convertSeq, convertSeqWith,

  -- ** Scalar expressions
  Function, EltFunctionR,
  convertExp, convertFun,

  test,
) where

import Data.Array.Accelerate.Sugar.Array                  ( ArraysR )
import Data.Array.Accelerate.Sugar.Elt                    ( EltR )
import Data.Array.Accelerate.Smart
import Data.Array.Accelerate.Trafo.Config
-- import Data.Array.Accelerate.Trafo.Delayed
import Data.Array.Accelerate.Trafo.Sharing                ( Afunction, ArraysFunctionR, Function, EltFunctionR )
import qualified Data.Array.Accelerate.AST                as AST
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule
-- import qualified Data.Array.Accelerate.Trafo.Fusion       as Fusion
import qualified Data.Array.Accelerate.Trafo.LetSplit     as LetSplit
import qualified Data.Array.Accelerate.Trafo.Exp.Simplify as Rewrite
import qualified Data.Array.Accelerate.Trafo.Sharing      as Sharing
import qualified Data.Array.Accelerate.Trafo.Operation.LiveVars as Operation
import qualified Data.Array.Accelerate.Trafo.Operation.Simplify as Operation
-- import qualified Data.Array.Accelerate.Trafo.Vectorise    as Vectorise

import Control.DeepSeq
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Partitioning
import Data.Array.Accelerate.Representation.Ground (DesugaredArrays, DesugaredAfun)
import Data.Array.Accelerate.Trafo.Desugar (DesugarAcc, desugar, desugarAfun)
import qualified Data.Array.Accelerate.Trafo.NewNewFusion as NewNewFusion
import qualified Data.Array.Accelerate.Pretty             as Pretty
import qualified Data.Array.Accelerate.Pretty.Operation   as Pretty
import qualified Data.Array.Accelerate.Pretty.Schedule    as Pretty
import Data.Array.Accelerate.Pretty (prettyOpenAcc)
import Data.Array.Accelerate.Pretty.Partitioned ()
import Data.Text.Lazy.Builder
import qualified Data.Array.Accelerate.AST.Operation as Operation
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph
import Data.Array.Accelerate.Pretty.Print (configPlain, Val (Empty))
import qualified Debug.Trace
import Data.Text.Lazy (unpack)

#ifdef ACCELERATE_DEBUG
import Formatting
import System.IO.Unsafe
import Data.Array.Accelerate.Debug.Internal.Flags                   hiding ( when )
import Data.Array.Accelerate.Debug.Internal.Timed
#endif

test
  :: forall sched kernel f. (Afunction f, DesugarAcc (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), Pretty.PrettyKernel kernel, IsSchedule sched, IsKernel kernel, Pretty.PrettySchedule sched, Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => f
  -> String
test f
  = "OriginalAcc:\n"
  ++ Pretty.renderForTerminal (Pretty.prettyPreOpenAfun configPlain prettyOpenAcc Empty original)
  ++ "\n\nDesugared OperationAcc:\n"
  ++ Pretty.renderForTerminal (Pretty.prettyAfun desugared)
  ++ "\n\nSimplified OperationAcc:\n"
  ++ Pretty.renderForTerminal (Pretty.prettyAfun operation)
  ++ "\n\nPartitionedAcc:\n"
  ++ Pretty.renderForTerminal (Pretty.prettyAfun partitioned)
  ++ "\nSLV'd PartitionedAcc:\n"
  ++ Pretty.renderForTerminal (Pretty.prettyAfun slvpartitioned)
  ++ "\n\nSchedule:\n"
  ++ Pretty.renderForTerminal (Pretty.prettySchedule schedule)
  where
    operation
      = Operation.simplifyFun
      $ Operation.stronglyLiveVariablesFun
      $ Operation.simplifyFun
      $ desugared
    desugared =
        desugarAfun @(KernelOperation kernel)
      $ original
    original =
        LetSplit.convertAfun 
      $ Sharing.convertAfunWith defaultOptions f

    partitioned = Operation.simplifyFun $ NewNewFusion.convertAfun operation

    slvpartitioned = Operation.simplifyFun $ Operation.stronglyLiveVariablesFun partitioned

    schedule = convertScheduleFun @sched @kernel slvpartitioned

-- HOAS -> de Bruijn conversion
-- ----------------------------

-- | Convert a closed array expression to de Bruijn form while also
--   incorporating sharing observation and array fusion.
--
convertAcc
  :: forall sched kernel arrs.
     (DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => Acc arrs
  -> sched kernel () (ScheduleOutput sched (DesugaredArrays (ArraysR arrs)) -> ())
convertAcc = convertAccWith defaultOptions

convertAccWith
  :: forall sched kernel arrs.
     (DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => Config
  -> Acc arrs
  -> sched kernel () (ScheduleOutput sched (DesugaredArrays (ArraysR arrs)) -> ())
convertAccWith config
  = phase' "codegen"     rnfSchedule convertSchedule
  . phase  "partition-live-vars"    (Operation.simplify . Operation.stronglyLiveVariables)
  . phase  "array-fusion"           (Operation.simplify . NewNewFusion.convertAccWith config)
  . phase  "operation-live-vars"    (Operation.simplify . Operation.stronglyLiveVariables)
  . phase  "desugar"                (Operation.simplify . desugar)
  . phase  "array-split-lets"       LetSplit.convertAcc
  -- phase "vectorise-sequences"    Vectorise.vectoriseSeqAcc `when` vectoriseSequences
  . phase  "sharing-recovery"       (Sharing.convertAccWith config)


-- | Convert a unary function over array computations, incorporating sharing
--   observation and array fusion
--
convertAfun
  :: forall sched kernel f.
     (Afunction f, DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => f
  -> sched kernel () (Scheduled sched (DesugaredAfun (ArraysFunctionR f)))
convertAfun = convertAfunWith defaultOptions

convertAfunWith
  :: forall sched kernel f.
     (Afunction f, DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => Config
  -> f
  -> sched kernel () (Scheduled sched (DesugaredAfun (ArraysFunctionR f)))
convertAfunWith config
  = phase' "codegen"     rnfSchedule convertScheduleFun
  . phase  "partition-live-vars"    (Operation.simplifyFun . Operation.stronglyLiveVariablesFun)
  . phase  "array-fusion"           (Operation.simplifyFun . NewNewFusion.convertAfunWith config)
  . phase  "operation-live-vars"    (Operation.simplifyFun . Operation.stronglyLiveVariablesFun)
  . phase  "desugar"                (Operation.simplifyFun . desugarAfun)
  . phase  "array-split-lets"       LetSplit.convertAfun
  -- phase "vectorise-sequences"    Vectorise.vectoriseSeqAfun  `when` vectoriseSequences
  . phase  "sharing-recovery"       (Sharing.convertAfunWith config)


-- | Convert a closed scalar expression, incorporating sharing observation and
--   optimisation.
--
convertExp :: Exp e -> AST.Exp () (EltR e)
convertExp
  = phase "exp-simplify"     Rewrite.simplifyExp
  . phase "sharing-recovery" Sharing.convertExp


-- | Convert closed scalar functions, incorporating sharing observation and
--   optimisation.
--
convertFun :: Function f => f -> AST.Fun () (EltFunctionR f)
convertFun
  = phase "exp-simplify"     Rewrite.simplifyFun
  . phase "sharing-recovery" Sharing.convertFun

{--
-- | Convert a closed sequence computation, incorporating sharing observation and
--   optimisation.
--
convertSeq :: Typeable s => Seq s -> DelayedSeq s
convertSeq = convertSeqWith phases

convertSeqWith :: Typeable s => Phase -> Seq s -> DelayedSeq s
convertSeqWith Phase{..} s
  = phase "array-fusion"           (Fusion.convertSeq enableAccFusion)
  -- $ phase "vectorise-sequences"    Vectorise.vectoriseSeq     `when` vectoriseSequences
  -- $ phase "rewrite-segment-offset" Rewrite.convertSegmentsSeq `when` convertOffsetOfSegment
  $ phase "sharing-recovery"       (Sharing.convertSeq recoverAccSharing recoverExpSharing recoverSeqSharing floatOutAccFromExp)
  $ s
--}


-- when :: (a -> a) -> Bool -> a -> a
-- when f True  = f
-- when _ False = id

-- Debugging
-- ---------

-- Execute a phase of the compiler and (possibly) print some timing/gc
-- statistics.
--
phase :: NFData b => Builder -> (a -> b) -> a -> b
phase n = phase' n rnf

-- Execute a phase of the compiler and (possibly) print some timing/gc
-- statistics.
--
phase' :: Builder -> (b -> ()) -> (a -> b) -> a -> b
#ifdef ACCELERATE_DEBUG
phase' n rnf'' f x = unsafePerformIO $ do
  enabled <- getFlag dump_phases
  if enabled
    then timed dump_phases (now ("phase " <> n <> ": ") % elapsed) (let y = f x in rnf'' y `seq` return y)
    else return (f x)
#else
phase' _ _ f = f
#endif
