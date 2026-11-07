/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Tactic.Abel

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The relative pushout map for split short exact sequences

For a morphism of split short complexes, if the quotient map is split
mono, the map from the pushout of the two left terms into the target
middle term is split mono. The retraction is explicit. Degreewise
application supplies the relative cofibration calculation for cylinders.
-/
/-! Adapted from `Quillen.Aglib.CategoryTheory.ExactCategory.RelativeSplitMono`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- An explicit relative retraction for a map of split short exact sequences. -/
theorem isSplitMono_relative_of_splittings
    {S T : ShortComplex C} (σ : S.Splitting) (τ : T.Splitting) (φ : S ⟶ T)
    [IsSplitMono φ.τ₃] {P : C} {g : S.X₂ ⟶ P} {j : T.X₁ ⟶ P}
    (h : IsPushout S.f φ.τ₁ g j) (k : P ⟶ T.X₂)
    (hg : g ≫ k = φ.τ₂) (hj : j ≫ k = T.f) : IsSplitMono k := by
  let v : S.X₃ ⟶ P := σ.s ≫ g - σ.s ≫ φ.τ₂ ≫ τ.r ≫ j
  let r : T.X₂ ⟶ P := τ.r ≫ j + T.g ≫ retraction φ.τ₃ ≫ v
  refine IsSplitMono.mk' ⟨r, ?_⟩
  apply h.hom_ext
  · simp only [← Category.assoc, hg, Category.comp_id]
    dsimp [r, v]
    simp only [Preadditive.comp_add, Category.assoc, φ.comm₂₃_assoc,
      IsSplitMono.id_assoc, Preadditive.comp_sub, σ.g_s_assoc,
      Preadditive.sub_comp, Category.id_comp, Category.assoc]
    rw [h.w, ← φ.comm₁₂_assoc]
    simp only [τ.f_r_assoc]
    abel
  · simp only [← Category.assoc, hj, Category.comp_id]
    simp [r]

end CategoryTheory.ExactCategory
