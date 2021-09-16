{-# LANGUAGE GADTs        #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      : Data.Array.Accelerate.AST.Kernel
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module defines the interface for kernels, to be implemented
-- in other modules.
--

module Data.Array.Accelerate.AST.Kernel (
  IsKernel(..),
  OpenKernelFun(..), KernelFun
) where

import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Representation.Ground
import Data.Kind

class NFData' kernel => IsKernel kernel where
  type KernelOperation kernel :: Type -> Type

  compileKernel :: Cluster (KernelOperation kernel) args -> Args env args -> kernel env

type KernelFun kernel = OpenKernelFun kernel ()

data OpenKernelFun kernel env t where
  KernelFunLam
    :: GroundR s
    -> OpenKernelFun kernel (env, s) t
    -> OpenKernelFun kernel env (s -> t)
  
  KernelFunBody
    :: kernel env
    -> OpenKernelFun kernel env ()

instance NFData' kernel => NFData' (OpenKernelFun kernel env) where
  rnf' (KernelFunLam g fun) = rnfGroundR g `seq` rnf' fun
  rnf' (KernelFunBody kernel) = rnf' kernel
