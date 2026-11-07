/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Residue.CanonicalRamifiedMap
public import Colib.RingTheory.KTheory.MilnorK.Residue.UnramifiedMapAcross
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Native Milnor residues and actual DVR completion

This adapts `MilnorK.DVR.residue_completion_restrict` and
`MilnorK.DVR.residue_completion_identification` from
`Aglib/KTheory/MilnorK/Residue/AdicCompletion.lean`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, lines 28–58.

The completion is Mathlib's actual adic completion. The domain and DVR proposition witnesses
come from pinned Stacks Tag 0AP1. The fraction map is Mathlib's literal `IsFractionRing.lift`,
used directly without a new map definition or fraction-field algebra instance. It has the same
base map as the lift underlying `EppCompletionInput.algebraAdicCompletionFractionField`;
the localization uniqueness theorem below identifies every map with this triangle.
The residue identification
is the inverse of Mathlib's bijective actual residue map. No completion ring, valuation, Milnor
group or tame residue is reconstructed. Both universes remain independent. The final criterion
concerns the kernel of the tame residue; it asserts neither injectivity nor surjectivity of the
map on the entire Milnor group, and makes no norm or tensor-decomposition claim.

The completion-ring input is Stacks Tag 0AP1. The tame-symbol background is Tag 0EAY;
compatibility with completion is the consequence proved here, not a quotation of either tag.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

open IsLocalRing IsDiscreteValuationRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Local proposition witnesses from the existing completion theorem, not a new ring model. -/
private theorem completion_dvr :
    ∃ _ : IsDomain (AdicCompletion (maximalIdeal R) R),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal R) R) :=
  isDiscreteValuationRing_iff_adicCompletion_maximalIdeal.mp ⟨inferInstance, inferInstance⟩

/-- Domain witness for the actual completion, from Stacks Tag 0AP1. -/
theorem dvrCompletion_isDomain : IsDomain (AdicCompletion (maximalIdeal R) R) :=
  Exists.elim (completion_dvr R) fun h _ => h

attribute [local instance] dvrCompletion_isDomain

/-- DVR witness for the same actual completion, from Stacks Tag 0AP1. -/
theorem dvrCompletion_isDiscreteValuationRing :
    IsDiscreteValuationRing (AdicCompletion (maximalIdeal R) R) :=
  Exists.elim (completion_dvr R) fun _ h => h

attribute [local instance] dvrCompletion_isDiscreteValuationRing

/-- The completion map has the same maximal-ideal generator. This is the elementary proof in
pinned `IsDiscreteValuationRing.irreducible_algebraMap_adicCompletion`, used here without the
higher Epp application import. No new uniformizer is chosen by this fact. -/
private theorem completion_irreducible {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R (AdicCompletion (maximalIdeal R) R) π) := by
  refine (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr ?_
  rw [AdicCompletion.maximalIdeal_eq_map,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span]
  simp

local notation "C" => AdicCompletion (maximalIdeal R) R
local notation "Q" => FractionRing C

/-- The original ring embeds in the fraction field of its actual completion. -/
theorem dvrCompletionFraction_algebraMap_injective : Function.Injective (algebraMap R Q) := by
  rw [IsScalarTower.algebraMap_eq R C Q]
  exact (IsFractionRing.injective C Q).comp (AdicCompletion.of_injective (maximalIdeal R) R)

variable (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]

local notation "φ" => IsFractionRing.lift (A := R) (K := F)
  (g := algebraMap R Q) (dvrCompletionFraction_algebraMap_injective R)

/-- Every fraction-field map with the actual completion triangle is the same native lift. -/
theorem dvrCompletionFractionLift_unique (f : F →+* Q)
    (hf : ∀ r : R, f (algebraMap R F r) =
      algebraMap C Q (algebraMap R C r)) : φ = f := by
  apply IsFractionRing.lift_unique
  intro r
  exact (hf r).trans (IsScalarTower.algebraMap_apply R C Q r).symm

/-- The actual completion fraction-field map commutes with the native canonical tame residue. -/
theorem dvrMilnorTameSymbol'_completion (n : ℕ) :
    (milnorKTheoryMap
        (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) n).toAddMonoidHom.comp
        (dvrMilnorTameSymbol' R F n) =
      (dvrMilnorTameSymbol' (AdicCompletion (maximalIdeal R) R)
        Q n).comp
          (milnorKTheoryMap φ
            (n + 1)).toAddMonoidHom := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [dvrMilnorTameSymbol'_eq_of_ramified_identity hπ,
    dvrMilnorTameSymbol'_eq_of_ramified_identity (completion_irreducible R hπ)]
  refine dvrMilnorTameSymbol_map_across
    (algebraMap R (AdicCompletion (maximalIdeal R) R))
    φ (fun r => ?_) hπ
    (completion_irreducible R hπ) n
  exact (IsFractionRing.lift_algebraMap (dvrCompletionFraction_algebraMap_injective R) r).trans
    (IsScalarTower.algebraMap_apply R C Q r)

/-- Inverting the actual residue map recovers the original residue of every Milnor class. -/
theorem dvrMilnorTameSymbol'_completion_identification (n : ℕ)
    (x : MilnorKTheory F (n + 1)) :
    let e := RingEquiv.ofBijective
      (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
      (AdicCompletion.residueField_map_bijective R)
    milnorKTheoryMap e.symm.toRingHom n
      (dvrMilnorTameSymbol' (AdicCompletion (maximalIdeal R) R)
        Q n
          (milnorKTheoryMap φ (n + 1) x)) =
      dvrMilnorTameSymbol' R F n x := by
  intro e
  have hc := DFunLike.congr_fun (dvrMilnorTameSymbol'_completion R F n) x
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe] at hc
  rw [← hc]
  change ((milnorKTheoryMap e.symm.toRingHom n).comp
    (milnorKTheoryMap e.toRingHom n)) (dvrMilnorTameSymbol' R F n x) = _
  rw [← milnorKTheoryMap_comp]
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id (ResidueField R) := by
    ext z
    exact e.symm_apply_apply z
  rw [he, milnorKTheoryMap_id, LinearMap.id_apply]

/-- Completion preserves and reflects vanishing of the canonical tame residue. -/
theorem dvrMilnorTameSymbol'_completion_eq_zero_iff (n : ℕ)
    (x : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' (AdicCompletion (maximalIdeal R) R)
        Q n
        (milnorKTheoryMap φ (n + 1) x) = 0 ↔
      dvrMilnorTameSymbol' R F n x = 0 := by
  constructor
  · intro hx
    have h := dvrMilnorTameSymbol'_completion_identification R F n x
    dsimp only at h
    rw [hx, map_zero] at h
    exact h.symm
  · intro hx
    have h := DFunLike.congr_fun (dvrMilnorTameSymbol'_completion R F n) x
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe] at h
    rw [hx, map_zero] at h
    exact h.symm

end Stacks.Chow

attribute [stacks 0AP1 "Domain and DVR witnesses for the actual maximal-ideal adic completion"]
  Stacks.Chow.dvrCompletion_isDomain Stacks.Chow.dvrCompletion_isDiscreteValuationRing
attribute [colib_tag "COL-0168"]
  Stacks.Chow.dvrMilnorTameSymbol'_completion
  Stacks.Chow.dvrMilnorTameSymbol'_completion_identification
  Stacks.Chow.dvrMilnorTameSymbol'_completion_eq_zero_iff
attribute [stacks 0EAY "DVR tame-symbol background; the completion comparison is proved here"]
  Stacks.Chow.dvrMilnorTameSymbol'_completion
  Stacks.Chow.dvrMilnorTameSymbol'_completion_identification
  Stacks.Chow.dvrMilnorTameSymbol'_completion_eq_zero_iff
