/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import StacksFrontier.Algebra.Module.FiniteLength.DeterminantProduct

/-!
# Comparing finite-length and ordinary determinants over a field

The native finite-length determinant takes values in the residue field of the base
local ring. For a field base, it is the residue of the ordinary determinant. The
comparison uses the canonical residue map and tensor transport, without installing
a different scalar action on the original vector space.

This is supporting glue for the finite-algebra norm calculation adapted from
`Aglib/RingTheory/FiniteAlgebraNormLength.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. It uses the existing finite-length
determinant, not the source's custom prime-filtration construction.

-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FiniteLengthEndomorphism

universe u v

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
  [Module.Finite k M]

/-- Over a field, the native finite-length determinant is the residue of the ordinary
determinant. The residue-field comparison is through the canonical scalar extension. -/
@[colib_tag "COL-0182",
  colib_ref "axiom_stacks" "Algebra/Module/FiniteLength/DeterminantProduct.lean"
    "comparison" "Field-base comparison with the native finite-length determinant"]
theorem det_eq_residue_det (hM : IsFiniteLength k M) (f : Module.End k M) :
    det k hM f = IsLocalRing.residue k f.det := by
  let K := IsLocalRing.ResidueField k
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K)
    ⟨(algebraMap k K).injective, IsLocalRing.residue_surjective⟩
  let E : M ≃ₗ[k] K ⊗[k] M :=
    (TensorProduct.lid k M).symm.trans (e.toLinearEquiv.rTensor M)
  have hE (m : M) : E m = (1 : K) ⊗ₜ[k] m := by
    change e 1 ⊗ₜ[k] m = (1 : K) ⊗ₜ[k] m
    rw [map_one]
  have hT : IsFiniteLength k (K ⊗[k] M) := E.isFiniteLength hM
  have hcomm : E.toLinearMap.comp f =
      ((f.baseChange K).restrictScalars k).comp E.toLinearMap := by
    ext m
    change E (f m) = (f.baseChange K) (E m)
    simp only [hE, LinearMap.baseChange_tmul]
  calc
    det k hM f = det k hT ((f.baseChange K).restrictScalars k) :=
      det_eq_of_linearEquiv hM hT f _ E hcomm
    _ = (f.baseChange K).det := det_residue k (K ⊗[k] M) hT (f.baseChange K)
    _ = IsLocalRing.residue k f.det := LinearMap.det_baseChange f

end FiniteLengthEndomorphism
