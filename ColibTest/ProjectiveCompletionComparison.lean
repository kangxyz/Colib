/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Colib.Topology.ClassifyingSpace.ProjectiveCompletionUnitHomotopy
import Colib.Topology.ClassifyingSpace.ProjectiveCompletionComponents
import Colib.Topology.ClassifyingSpace.StableProjectiveSource

open CategoryTheory MonoidalCategory
open ModuleCat.FiniteProjective ModuleCat.FiniteProjective.StableFreeRight

universe u

attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  projectiveTelescopeAction

variable (R : Type u) [Ring R]

-- The total retraction keeps the original functor as its actual forward map.
example : (completedRetractionHomotopyEquiv R).toFun =
    classifyingSpaceMapUniversal (completedRetraction R) :=
  completedRetractionHomotopyEquiv_toFun R

-- The original completion map has exactly the original zero-component preimage.
example : (classifyingSpaceMapUniversal (completionFunctor R)) ⁻¹'
    pathComponent (StableCompletion.zeroPoint R) =
    pathComponent (classifyingSpacePoint (projectiveTelescopeBase R)) :=
  completionMap_preimage_zeroComponent R

-- The source equivalence retains the specified original stable-to-telescope inverse.
example (x : ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))) :
    (stableProjectiveZeroHomotopyEquiv R x).val =
      classifyingSpaceMapUniversal (telescopeFunctor R)
        (StableCompletion.originalStableToTelescope R x) :=
  stableProjectiveZeroHomotopyEquiv_val R x

#print axioms ModuleCat.FiniteProjective.StableFreeRight.telescopeUnitCompletionHomotopy
#print axioms ModuleCat.FiniteProjective.StableFreeRight.completedRetractionHomotopyEquiv
#print axioms ModuleCat.FiniteProjective.StableFreeRight.completionMap_preimage_zeroComponent
#print axioms ModuleCat.FiniteProjective.StableFreeRight.stableProjectiveZeroHomotopyEquiv
#print axioms ModuleCat.FiniteProjective.StableFreeRight.stableZeroMap_completionMap_val
