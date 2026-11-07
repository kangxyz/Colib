/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeFiberComparison

/-!
# The original stable cone sequence from genuine cone-to-fiber excision

A proved stable equivalence of the unchanged cone-to-fiber comparison transports the existing
original fiber sequence to the original arrow and cone inclusion. The connecting homomorphism
uses the genuine signed fiber boundary and the inverse of precisely that comparison. All three
recurring exactness positions retain the actual signed stable groups and original maps.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/ConeStableExactness.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual cone, full independent cylinder and loop parameters, signed degrees and
original hypotheses are retained under their native mathematical owners. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
  (hf : IsStableEquivalence (mappingConeFiberComparison f))

/-- The signed original cone boundary, transported by the actual cone-to-fiber isomorphism. -/
def stableMappingConeConnecting (d : ℤ) :
    stableHomotopyGroup (mappingCone f) (d + 1) ⟶ stableHomotopyGroup E d :=
  let := hf d
  stableFiberConnecting (mappingConeInclusion f) d ≫
    inv ((stableHomotopyFunctor d).map (mappingConeFiberComparison f))

/-- The original cone boundary followed by the exact comparison is the original fiber boundary. -/
theorem stableMappingConeConnecting_comparison (d : ℤ) :
    stableMappingConeConnecting f hf d ≫
      (stableHomotopyFunctor d).map (mappingConeFiberComparison f) =
        stableFiberConnecting (mappingConeInclusion f) d := by
  let := hf d
  simp [stableMappingConeConnecting]

/-- The original comparison identifies projection with the unchanged original stable arrow. -/
theorem stableMappingConeComparison_projection (d : ℤ) :
    (stableHomotopyFunctor d).map (mappingConeFiberComparison f) ≫
      (stableHomotopyFunctor d).map (homotopyFiberProjection (mappingConeInclusion f)) =
        (stableHomotopyFunctor d).map f := by
  rw [← Functor.map_comp, mappingConeFiberComparison_projection]

include hf in
/-- Exactness at the original target, using actual comparison surjectivity. -/
theorem stableMappingCone_exact_target (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor d).map f)
      ((stableHomotopyFunctor d).map (mappingConeInclusion f)) := by
  let := hf d
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := (stableHomotopyFiber_exact_source (mappingConeInclusion f) d y).mp hy
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      ((stableHomotopyFunctor d).map (mappingConeFiberComparison f))).surjective z
    refine ⟨x, ?_⟩
    exact (ConcreteCategory.congr_hom (stableMappingConeComparison_projection f d) x).symm.trans hz
  · rintro ⟨x, rfl⟩
    apply (stableHomotopyFiber_exact_source (mappingConeInclusion f) d _).mpr
    exact ⟨(stableHomotopyFunctor d).map (mappingConeFiberComparison f) x,
      ConcreteCategory.congr_hom (stableMappingConeComparison_projection f d) x⟩

/-- Exactness at the original source, with the unchanged original arrow after the boundary. -/
theorem stableMappingConeConnecting_exact_source (d : ℤ) :
    Function.Exact (stableMappingConeConnecting f hf d) ((stableHomotopyFunctor d).map f) := by
  let := hf d
  let j := (stableHomotopyFunctor d).map (mappingConeFiberComparison f)
  have hj := ConcreteCategory.bijective_of_isIso j
  intro x
  constructor
  · intro hx
    have hz : (stableHomotopyFunctor d).map
        (homotopyFiberProjection (mappingConeInclusion f)) (j x) = 0 := by
      exact (ConcreteCategory.congr_hom (stableMappingConeComparison_projection f d) x).trans hx
    obtain ⟨y, hy⟩ :=
      (stableFiberConnecting_exact_fiber (mappingConeInclusion f) d (j x)).mp hz
    refine ⟨y, hj.injective ?_⟩
    exact (ConcreteCategory.congr_hom (stableMappingConeConnecting_comparison f hf d) y).trans hy
  · rintro ⟨y, rfl⟩
    refine (ConcreteCategory.congr_hom (stableMappingConeComparison_projection f d)
      (stableMappingConeConnecting f hf d y)).symm.trans ?_
    exact (congrArg ((stableHomotopyFunctor d).map
      (homotopyFiberProjection (mappingConeInclusion f)))
        (ConcreteCategory.congr_hom (stableMappingConeConnecting_comparison f hf d) y)).trans
          ((stableFiberConnecting_exact_fiber (mappingConeInclusion f) d _).mpr ⟨y, rfl⟩)

/-- Exactness at the original cone in the actual shifted signed degree. -/
theorem stableMappingConeConnecting_exact_cone (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion f))
      (stableMappingConeConnecting f hf d) := by
  let := hf d
  let j := (stableHomotopyFunctor d).map (mappingConeFiberComparison f)
  have hj := ConcreteCategory.bijective_of_isIso j
  intro y
  constructor
  · intro hy
    apply (stableFiberConnecting_exact_target (mappingConeInclusion f) d y).mp
    have he := ConcreteCategory.congr_hom (stableMappingConeConnecting_comparison f hf d) y
    rw [ConcreteCategory.comp_apply, hy, map_zero] at he
    exact he.symm
  · intro hy
    apply hj.injective
    rw [map_zero]
    exact (ConcreteCategory.congr_hom (stableMappingConeConnecting_comparison f hf d) y).trans
      ((stableFiberConnecting_exact_target (mappingConeInclusion f) d y).mpr hy)

/-- All recurring positions of the original signed stable cone sequence are exact. -/
theorem stableMappingConeLongExactSequence (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion f))
      (stableMappingConeConnecting f hf d) ∧
    Function.Exact (stableMappingConeConnecting f hf d) ((stableHomotopyFunctor d).map f) ∧
    Function.Exact ((stableHomotopyFunctor d).map f)
      ((stableHomotopyFunctor d).map (mappingConeInclusion f)) :=
  ⟨stableMappingConeConnecting_exact_cone f hf d,
    stableMappingConeConnecting_exact_source f hf d, stableMappingCone_exact_target f hf d⟩

end Topology.LoopPrespectrum
