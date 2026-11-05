/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The sign of the mapping-cone connecting morphism

Mathlib's standard triangle uses the negative of the first cone projection.
Consequently a lift with first cocycle component `α` composes with the third
triangle morphism to the shifted morphism represented by `-α`.

This is a low-level sign interface needed when comparing projective-resolution
`Ext` cocycles with short-exact-sequence classes. It does not itself assert a
comparison for any particular resolution or augmentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace CochainComplex.mappingCone

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {K F G : CochainComplex C ℤ} (φ : F ⟶ G)
  (α : Cocycle K F 1) (β : Cochain K G 0)
  (h : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)

/-- A cone lift meets the standard triangle projection with the negative of its first cocycle. -/
theorem lift_comp_triangle_mor₃ :
    lift φ α β h ≫ (triangle φ).mor₃ = Cocycle.equivHomShift.symm (-α) := by
  change lift φ α β h ≫ Cocycle.equivHomShift.symm (-fst φ) = _
  rw [← Cocycle.equivHomShift_symm_precomp]
  congr 1
  ext p q hpq
  simp [Cocycle.precomp]

end CochainComplex.mappingCone
