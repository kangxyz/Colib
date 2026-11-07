/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.ClassifyingSpace.StableProjectiveLocalHomology
public import Colib.Topology.LocalCoefficients.PullbackCoveringHomologyUniverseLift

/-!
# Integral homology of the original stable-zero covering pullback

The proved all-target-system theorem is applied to the actual free integral
module on the covering fibers, with the original monodromy. The unconditional
native arrow comparison then gives integral homology of the literal pullback
lift. No homology equivalence is a premise of these statements.

Adapted from the homology conclusion of `Quillen/KTheory/Plus/StableZeroFiberHomology.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Existing native cover geometry is unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory FundamentalGroupoid.LocalCoefficients

universe u

namespace ModuleCat.FiniteProjective.StableCompletion

variable (R : Type u) [Ring R]
  {T : Type (u + 1)} [TopologicalSpace T] (q : T → ZeroComponent R)
  (hq : IsCoveringMap q)

include hq

/-- The original mixed-universe map preserves degree-two homology with the actual
free covering-fiber system, rather than with an untwisted replacement. -/
theorem stableZeroMap_coveringFiber_homologyTwo_isIso :
    IsIso (UniverseLift.homologyMap.{u, u + 1, u + 1} (stableZeroMap R)
      (PullbackCovering.fiberSystem hq) 2) :=
  StableFreeRight.stableZeroMap_localHomology_isIso R (PullbackCovering.fiberSystem hq) 2

/-- The literal covering pullback lift induces an integral singular H₂ isomorphism,
with the actual successor-universe coefficient object. -/
theorem stableZeroCoverLift_homologyTwo_isIso :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u + 1} ℤ) 2).obj
      (ModuleCat.of ℤ (ULift.{u + 1} ℤ))).map
        (TopCat.ofHom (Topology.Covering.Pullback.lift (stableZeroMap R) q))) :=
  (Arrow.isIso_iff_isIso_of_isIso
    (PullbackCoveringUniverseLift.successorHomologyTwoArrowIso
      (stableZeroMap R) hq).hom).mp
        (stableZeroMap_coveringFiber_homologyTwo_isIso R q hq)

/-- In fact the original integral singular-chain map of that literal pullback
lift is a quasi-isomorphism, by the proved all-target-system theorem. -/
theorem stableZeroCoverLift_quasiIso :
    QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u + 1} ℤ)).obj
      (ModuleCat.of ℤ (ULift.{u + 1} ℤ))).map
        (TopCat.ofHom (Topology.Covering.Pullback.lift (stableZeroMap R) q))) :=
  PullbackCoveringUniverseLift.successor_singular_quasiIso_of_all_localCoefficients
    (stableZeroMap R) hq (StableFreeRight.stableZeroMap_localCoefficients_quasiIso R)

end ModuleCat.FiniteProjective.StableCompletion
