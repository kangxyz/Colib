/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.SmallModel.Exact
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Ext
public import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# Abelian exact structures on the native small model

Mathlib's actual `SmallModel C` inherits its abelian structure through
`equivSmallModel C`. The transported exact structure is the standard abelian
one, because the inverse equivalence preserves and reflects short exact
sequences. The comparison is the identity functor on that same small category.

The exact-structure comparison supplies the lower input used by
`Quillen/Localization/SmallModel.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

namespace CategoryTheory

attribute [local instance] Abelian.hasFiniteBiproducts

variable (C : Type u₁) [Category.{v₁} C] [Abelian C] [EssentiallySmall.{w} C]

/-- The abelian structure transported to Mathlib's chosen small model. -/
instance smallModelAbelian : Abelian (SmallModel.{w} C) :=
  abelianOfEquivalence (equivSmallModel C).inverse

/-- Transporting the standard abelian exact structure gives precisely all
short exact sequences in the chosen small model. -/
theorem ExactCategory.abelianExactStructure_smallModel :
    (abelianExactStructure C).smallModel = abelianExactStructure (SmallModel.{w} C) := by
  apply ExactStructure.ext_conflation
  funext S
  apply propext
  change (S.map (equivSmallModel C).inverse).ShortExact ↔ S.ShortExact
  constructor
  · intro h
    exact
      { exact := (S.exact_map_iff_of_faithful (equivSmallModel C).inverse).1 h.exact
        mono_f := (equivSmallModel C).inverse.mono_of_mono_map h.mono_f
        epi_g := (equivSmallModel C).inverse.epi_of_epi_map h.epi_g }
  · intro h
    exact h.map_of_exact (equivSmallModel C).inverse

namespace SmallModel

/-- The identity comparison from the transported exact structure to the
equal standard abelian exact structure. -/
def abelianExactComparison : ExactCategory.ExactFunctor (abelianExactStructure C).smallModel
    (abelianExactStructure (SmallModel.{w} C)) where
  toFunctor := 𝟭 _
  map_conflation _ h := by
    rw [abelianExactStructure_smallModel] at h
    exact h

instance abelianExactComparison_isEquivalence :
    (abelianExactComparison C).toFunctor.IsEquivalence :=
  inferInstanceAs (𝟭 (SmallModel.{w} C)).IsEquivalence

variable {C} {D : Type u₂} [Category.{v₂} D] [Abelian D] [EssentiallySmall.{w} D]

/-- The very same descended functor, with the standard abelian exact
structures on its source and target. -/
def mapAbelianExactFunctor
    (F : ExactCategory.ExactFunctor (abelianExactStructure C) (abelianExactStructure D)) :
    ExactCategory.ExactFunctor (abelianExactStructure (SmallModel.{w} C))
      (abelianExactStructure (SmallModel.{w} D)) where
  toFunctor := F.smallModel.toFunctor
  map_conflation S h := by
    rw [← abelianExactStructure_smallModel] at h ⊢
    exact F.smallModel.map_conflation S h

end SmallModel
end CategoryTheory
