/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Actual DVR completions and their fraction maps

The domain and DVR witnesses are projections of native Stacks Tag 0AP1. The fraction map is
Mathlib's actual `IsFractionRing.lift`, not a new fraction-field model. The algebra structure
below only exposes that native map for an arbitrary specified fraction field.

This is the lower RingTheory interface needed by the branch application of
`Aglib/RingTheory/AdicCompletion/FractionBaseChange.lean`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The same proposition witnesses and fraction lift
already occur in Colib's Milnor completion comparison. This file deliberately has no dependency
on Milnor K-theory. The elementary uniformizer proof is the one in pinned
`IsDiscreteValuationRing.irreducible_algebraMap_adicCompletion`, without its higher Epp imports.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing IsDiscreteValuationRing

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

private theorem completion_dvr :
    ∃ _ : IsDomain (AdicCompletion (maximalIdeal R) R),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal R) R) :=
  isDiscreteValuationRing_iff_adicCompletion_maximalIdeal.mp ⟨inferInstance, inferInstance⟩

/-- The actual maximal-ideal completion of a DVR is a domain, by native Stacks 0AP1. -/
instance instIsDomainMaximalIdeal : IsDomain (AdicCompletion (maximalIdeal R) R) :=
  Exists.elim (completion_dvr R) fun h _ => h

/-- The same actual completion is a DVR, by native Stacks 0AP1. -/
instance instIsDiscreteValuationRingMaximalIdeal :
    IsDiscreteValuationRing (AdicCompletion (maximalIdeal R) R) :=
  Exists.elim (completion_dvr R) fun _ h => h

/-- The original uniformizer generates the maximal ideal after completion. -/
theorem irreducible_algebraMap {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R (AdicCompletion (maximalIdeal R) R) π) := by
  refine (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr ?_
  rw [maximalIdeal_eq_map, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
    Ideal.map_span]
  simp

/-- The original DVR embeds in the fraction field of its actual completion. -/
theorem fraction_algebraMap_injective :
    Function.Injective (algebraMap R (FractionRing (AdicCompletion (maximalIdeal R) R))) := by
  rw [IsScalarTower.algebraMap_eq R (AdicCompletion (maximalIdeal R) R)]
  exact (IsFractionRing.injective (AdicCompletion (maximalIdeal R) R) _).comp
    (of_injective (maximalIdeal R) R)

variable (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]

/-- The specified original fraction field acts by the native universal fraction lift. -/
@[instance_reducible,
  colib_tag "COL-0191",
  colib_ref "aglib_principal_euler_pin" "RingTheory/AdicCompletion/FractionBaseChange.lean"
    "adaptation" "Native DVR completion and specified fraction-field lift"]
def fractionCompletionAlgebra :
    Algebra F (FractionRing (AdicCompletion (maximalIdeal R) R)) :=
  (IsFractionRing.lift (K := F) (fraction_algebraMap_injective R)).toAlgebra

/-- The fraction action has the literal original completion triangle. -/
theorem fractionCompletionIsScalarTower :
    letI := fractionCompletionAlgebra R F
    IsScalarTower R F (FractionRing (AdicCompletion (maximalIdeal R) R)) := by
  let := fractionCompletionAlgebra R F
  exact IsScalarTower.of_algebraMap_eq fun r =>
    (IsFractionRing.lift_algebraMap (fraction_algebraMap_injective R) r).symm

/-- The algebra map is exactly the native fraction lift. -/
theorem fractionCompletionAlgebra_algebraMap :
    letI := fractionCompletionAlgebra R F
    algebraMap F (FractionRing (AdicCompletion (maximalIdeal R) R)) =
      IsFractionRing.lift (K := F) (fraction_algebraMap_injective R) := rfl

/-- The fraction map agrees with the original completion map on every original element. -/
theorem fractionCompletionAlgebra_algebraMap_apply (r : R) :
    letI := fractionCompletionAlgebra R F
    algebraMap F (FractionRing (AdicCompletion (maximalIdeal R) R)) (algebraMap R F r) =
      algebraMap (AdicCompletion (maximalIdeal R) R)
        (FractionRing (AdicCompletion (maximalIdeal R) R))
        (algebraMap R (AdicCompletion (maximalIdeal R) R) r) := by
  let := fractionCompletionAlgebra R F
  exact (IsFractionRing.lift_algebraMap (fraction_algebraMap_injective R) r).trans
    (IsScalarTower.algebraMap_apply R (AdicCompletion (maximalIdeal R) R) _ r)

end AdicCompletion
