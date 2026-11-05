/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.BranchLocal
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Native fraction actions on actual completed branches

The fraction action is exactly `FractionRing.liftAlgebra` for the already constructed canonical
completed-base map. Finite-dimensionality is the native fraction-field theorem for finite
torsion-free domain algebras. No localization-away or new field model is introduced.

Adapted from `Aglib/RingTheory/AdicCompletion/BranchFractionAlgebra.lean` and
`Aglib/RingTheory/AdicCompletion/BranchFractionFinite.lean`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. Their explicit universal lift and localization proof
are replaced by these existing Mathlib interfaces. The action itself needs no module finiteness.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S]
  [DecidableEq (Ideal S)]

/-- The completed fraction field acts by Mathlib's existing universal fraction lift. -/
@[instance_reducible,
  colib_tag "COL-0191"]
def localCompletionFractionAlgebra
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    Algebra (FractionRing (AdicCompletion (maximalIdeal R) R))
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  let := localCompletionBaseFaithfulSMul R S q
  exact FractionRing.liftAlgebra (AdicCompletion (maximalIdeal R) R)
    (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q))

/-- The native fraction action extends the original canonical completed-base action. -/
theorem localCompletionFractionIsScalarTower
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    letI := localCompletionFractionAlgebra R S q
    IsScalarTower (AdicCompletion (maximalIdeal R) R)
      (FractionRing (AdicCompletion (maximalIdeal R) R))
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  let := localCompletionBaseFaithfulSMul R S q
  let := localCompletionFractionAlgebra R S q
  exact FractionRing.isScalarTower_liftAlgebra (AdicCompletion (maximalIdeal R) R)
    (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q))

/-- The fraction action has the literal canonical completed-base triangle. -/
theorem localCompletionFractionAlgebra_algebraMap
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S)))
    (x : AdicCompletion (maximalIdeal R) R) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    letI := localCompletionFractionAlgebra R S q
    algebraMap (FractionRing (AdicCompletion (maximalIdeal R) R))
        (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q))
        (algebraMap (AdicCompletion (maximalIdeal R) R)
          (FractionRing (AdicCompletion (maximalIdeal R) R)) x) =
      algebraMap (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)
        (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q))
        (localCompletionBaseMap (maximalIdeal R) q x) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  let := localCompletionFractionAlgebra R S q
  let := localCompletionFractionIsScalarTower R S q
  rw [← IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal R) R)
    (FractionRing (AdicCompletion (maximalIdeal R) R))]
  rw [IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal R) R)
    (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)]
  rfl

/-- Each actual completed branch fraction field is finite over the completed base fraction field.
The nonzero extended ideal is derived, rather than an additional input. -/
@[colib_tag "COL-0191"]
theorem localCompletionFractionFinite [Module.Finite R S]
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    letI := localCompletionFractionAlgebra R S q
    Module.Finite (FractionRing (AdicCompletion (maximalIdeal R) R))
      (FractionRing (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  let := localCompletionBaseFaithfulSMul R S q
  let := localCompletionBaseFinite (maximalIdeal R) (map_maximalIdeal_ne_zero R S) q
  let := localCompletionFractionAlgebra R S q
  infer_instance

end AdicCompletion
