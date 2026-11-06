/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The explicit change of sign in an original mapping cone

The cone of −f is identified with the cone of f by negation on the shifted source and identity
on the target. This keeps the sign in a split-factorization quotient visible.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.MappingCone.Sign`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

/-- The original cone sign change, negating only the shifted source coordinate. -/
def mappingConeNegIso : mappingCone (-f) ≅ mappingCone f where
  hom := mappingCone.map (-f) f (-𝟙 K) (𝟙 L) (by simp)
  inv := mappingCone.map f (-f) (-𝟙 K) (𝟙 L) (by simp)
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.id_comp]
    exact mappingCone.map_id _
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.id_comp]
    exact mappingCone.map_id _

/-- The unchanged target inclusion is preserved literally. -/
theorem mappingConeNegIso_inr :
    mappingCone.inr (-f) ≫ (mappingConeNegIso f).hom = mappingCone.inr f := by
  simp [mappingConeNegIso, mappingCone.map]

/-- The inverse also preserves the original target inclusion. -/
theorem mappingConeNegIso_inv_inr :
    mappingCone.inr f ≫ (mappingConeNegIso f).inv = mappingCone.inr (-f) := by
  simp [mappingConeNegIso, mappingCone.map]

/-- The shifted source coordinate is negated, with its original degree retained. -/
theorem mappingConeNegIso_inl_f (p q : ℤ) (hpq : p + (-1) = q) :
    (mappingCone.inl (-f)).v p q hpq ≫ ((mappingConeNegIso f).hom).f q =
      -(mappingCone.inl f).v p q hpq := by
  simp [mappingConeNegIso, mappingCone.map]

end CochainComplex
