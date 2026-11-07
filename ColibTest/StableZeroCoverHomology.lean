/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Colib.KTheory.Quillen.StableZeroFiberHomology

open CategoryTheory FundamentalGroupoid.LocalCoefficients
open ModuleCat.FiniteProjective ModuleCat.FiniteProjective.StableCompletion

universe u

variable (R : Type u) [Ring R]
  {T : Type (u + 1)} [TopologicalSpace T] (q : T → ZeroComponent R)
  (hq : IsCoveringMap q)

-- The native source universe, actual monodromy and arbitrary degree are retained.
example (A : System.{u + 1, u + 1} (ZeroComponent R)) (n : ℕ) :
    IsIso (UniverseLift.homologyMap.{u, u + 1, u + 1} (stableZeroMap R) A n) :=
  StableFreeRight.stableZeroMap_localHomology_isIso R A n

-- This is precisely the actual covering-fiber system, not constant coefficients.
example : IsIso (UniverseLift.homologyMap.{u, u + 1, u + 1} (stableZeroMap R)
    (PullbackCovering.fiberSystem hq) 2) :=
  stableZeroMap_coveringFiber_homologyTwo_isIso R q hq

-- The singular H₂ arrow is that of the literal original pullback lift.
example : IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u + 1} ℤ) 2).obj
    (ModuleCat.of ℤ (ULift.{u + 1} ℤ))).map
      (TopCat.ofHom (Topology.Covering.Pullback.lift (stableZeroMap R) q))) :=
  stableZeroCoverLift_homologyTwo_isIso R q hq

#print axioms ModuleCat.FiniteProjective.StableFreeRight.stableZeroMap_localCoefficients_quasiIso
#print axioms ModuleCat.FiniteProjective.StableFreeRight.stableZeroMap_localHomology_isIso
#print axioms ModuleCat.FiniteProjective.StableCompletion.stableZeroMap_coveringFiber_homologyTwo_isIso
#print axioms ModuleCat.FiniteProjective.StableCompletion.stableZeroCoverLift_homologyTwo_isIso
#print axioms ModuleCat.FiniteProjective.StableCompletion.stableZeroCoverLift_quasiIso
