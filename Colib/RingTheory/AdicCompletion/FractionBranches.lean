/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.BranchFraction
public import Colib.RingTheory.AdicCompletion.OriginalBranch
public import Colib.RingTheory.Localization.FiniteProductBaseChange

/-!
# The actual completed fraction tensor product over all original branches

For a finite torsion-free Dedekind algebra over a DVR, the completed base fraction field
tensor the specified original fraction field is the product of all actual completed original
branch fraction fields. This uses the proved integral completion decomposition and the native
algebraic fraction-field pushout. The equivalence is over the completed fraction field from
the outset. No uniformizer, extra generic-fiber equivalence, or nonzero extended-ideal premise
is supplied to its definition.

The coordinate formulas identify actual ring maps, not just abstract field factors. In
particular, restricting a coordinate to the specified original fraction field gives the
native completion fraction lift for its original localization.

Adapted from `Aglib/RingTheory/AdicCompletion/FractionBranches.lean` and
`Aglib/RingTheory/AdicCompletion/FractionTensorBranches.lean`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The coordinate uniqueness argument is extracted
from lines 80–97 of `Aglib/KTheory/MilnorK/Norm/FiniteExtension/DVR.lean` at the same revision;
it uses no norm or Milnor object. All four original ring and field universes are independent.

The extracted coordinate proof retains its original notice:
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing
open scoped TensorProduct

universe u v w z

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E]

local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "Khat" => FractionRing Rhat
local notation "D" => fun q : IdealBranch J => BranchCompletion J q
local notation "C" => fun q : IdealBranch J => FractionRing (D q)

/-- The actual full original-branch decomposition, with no chosen uniformizer in its definition. -/
@[colib_tag "COL-0192",
  colib_ref "aglib_principal_euler_pin" "RingTheory/AdicCompletion/FractionBranches.lean"
    "adaptation" "All actual original completed branches over the completed fraction field"]
def fractionTensorEquivLocalFractionFields :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    Khat ⊗[F] E ≃ₐ[Khat] ∀ q : IdealBranch J, C q := by
  let := fractionCompletionAlgebra R F
  let := fractionCompletionIsScalarTower R F
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionBaseIsScalarTower (S := S) (maximalIdeal R) q
  let := fun q => localCompletionBaseFaithfulSMul R S q
  let := fun q => localCompletionBaseFinite (S := S) (maximalIdeal R)
    (map_maximalIdeal_ne_zero R S) q
  let := fun q => localCompletionFractionAlgebra R S q
  let := fun q => localCompletionFractionIsScalarTower R S q
  exact Algebra.TensorProduct.fractionPiEquiv R S Rhat F E Khat D C
    (tensorEquivLocalCompletionsBase (maximalIdeal R) (map_maximalIdeal_ne_zero R S))

/-- Original integral elements have exactly their native localization-completion coordinates. -/
@[simp,
  colib_tag "COL-0192"]
theorem fractionTensorEquivLocalFractionFields_one_tmul
    (s : S) (q : IdealBranch J) :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    fractionTensorEquivLocalFractionFields R S F E (1 ⊗ₜ[F] algebraMap S E s) q =
      algebraMap (D q) (C q)
        (algebraMap (Localization.AtPrime q.val) (D q)
          (algebraMap S (Localization.AtPrime q.val) s)) := by
  let := fractionCompletionAlgebra R F
  let := fractionCompletionIsScalarTower R F
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionBaseIsScalarTower (S := S) (maximalIdeal R) q
  let := fun q => localCompletionBaseFaithfulSMul R S q
  let := fun q => localCompletionBaseFinite (S := S) (maximalIdeal R)
    (map_maximalIdeal_ne_zero R S) q
  let := fun q => localCompletionFractionAlgebra R S q
  let := fun q => localCompletionFractionIsScalarTower R S q
  rw [fractionTensorEquivLocalFractionFields,
    Algebra.TensorProduct.fractionPiEquiv_one_tmul_algebraMap]
  change algebraMap (D q) (C q)
    (tensorEquivLocalCompletions (maximalIdeal R) (map_maximalIdeal_ne_zero R S)
      (1 ⊗ₜ[R] s) q) = _
  rw [tensorEquivLocalCompletions_one_tmul]

/-- Left coefficients act by the native completed fraction-field action on every branch. -/
theorem fractionTensorEquivLocalFractionFields_tmul
    (b : Khat) (x : E) (q : IdealBranch J) :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    fractionTensorEquivLocalFractionFields R S F E (b ⊗ₜ[F] x) q =
      algebraMap Khat (C q) b *
        fractionTensorEquivLocalFractionFields R S F E (1 ⊗ₜ[F] x) q := by
  let := fractionCompletionAlgebra R F
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionFractionAlgebra R S q
  have h : b ⊗ₜ[F] x = algebraMap Khat (Khat ⊗[F] E) b * (1 ⊗ₜ[F] x) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [h, map_mul, (fractionTensorEquivLocalFractionFields R S F E).commutes]
  rfl

/-- Fractions have the quotient of their actual integral branch coordinates, also at zero
denominators with the field's totalized division. -/
@[colib_tag "COL-0192"]
theorem fractionTensorEquivLocalFractionFields_one_tmul_div
    (s t : S) (q : IdealBranch J) :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    fractionTensorEquivLocalFractionFields R S F E
        (1 ⊗ₜ[F] (algebraMap S E s / algebraMap S E t)) q =
      algebraMap (D q) (C q) (algebraMap S (D q) s) /
        algebraMap (D q) (C q) (algebraMap S (D q) t) := by
  let := fractionCompletionAlgebra R F
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionFractionAlgebra R S q
  let f : E →+* C q := (Pi.evalRingHom C q).comp
    ((fractionTensorEquivLocalFractionFields R S F E).toRingHom.comp
      (Algebra.TensorProduct.includeRight : E →ₐ[F] Khat ⊗[F] E).toRingHom)
  have hf (a : S) : f (algebraMap S E a) =
      algebraMap (D q) (C q) (algebraMap S (D q) a) := by
    change fractionTensorEquivLocalFractionFields R S F E
      (1 ⊗ₜ[F] algebraMap S E a) q = _
    rw [fractionTensorEquivLocalFractionFields_one_tmul]
    rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime q.val) (D q)]
  change f (algebraMap S E s / algebraMap S E t) = _
  rw [map_div₀, hf, hf]

/-- Each coordinate on the specified original field is its native branch-completion fraction
lift. No replacement of the original field by a chosen isomorphic field is involved. -/
@[colib_tag "COL-0192"]
theorem fractionTensorEquivLocalFractionFields_coordinate (q : IdealBranch J) :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    letI := originalBranchFractionAlgebra S E q
    letI := originalBranchIsFractionRing S E q
    (Pi.evalRingHom C q).comp
        ((fractionTensorEquivLocalFractionFields R S F E).toRingHom.comp
          (Algebra.TensorProduct.includeRight : E →ₐ[F] Khat ⊗[F] E).toRingHom) =
      IsFractionRing.lift (K := E)
        (fraction_algebraMap_injective (Localization.AtPrime q.val)) := by
  let := fractionCompletionAlgebra R F
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionFractionAlgebra R S q
  let := originalBranchFractionAlgebra S E q
  let := originalBranchFractionTower S E q
  let := originalBranchIsFractionRing S E q
  apply IsFractionRing.ringHom_ext (A := S)
  intro s
  change fractionTensorEquivLocalFractionFields R S F E
    (1 ⊗ₜ[F] algebraMap S E s) q = _
  rw [fractionTensorEquivLocalFractionFields_one_tmul,
    IsScalarTower.algebraMap_apply S (Localization.AtPrime q.val) E,
    IsFractionRing.lift_algebraMap]
  rw [IsScalarTower.algebraMap_apply (Localization.AtPrime q.val) (D q) (C q)]

/-- The original integral coordinates characterize the entire completed fraction tensor map. -/
@[colib_tag "COL-0192"]
theorem fractionTensorEquivLocalFractionFields_unique :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    ∀ (f : Khat ⊗[F] E →ₐ[Khat] ∀ q : IdealBranch J, C q),
      (∀ (s : S) (q : IdealBranch J), f (1 ⊗ₜ[F] algebraMap S E s) q =
        algebraMap (D q) (C q) (algebraMap (Localization.AtPrime q.val) (D q)
          (algebraMap S (Localization.AtPrime q.val) s))) →
      f = (fractionTensorEquivLocalFractionFields R S F E).toAlgHom := by
  let := fractionCompletionAlgebra R F
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionFractionAlgebra R S q
  intro f hf
  apply Algebra.TensorProduct.algHom_ext_of_isFractionRing S
  intro s
  funext q
  exact (hf s q).trans (fractionTensorEquivLocalFractionFields_one_tmul R S F E s q).symm

end AdicCompletion
