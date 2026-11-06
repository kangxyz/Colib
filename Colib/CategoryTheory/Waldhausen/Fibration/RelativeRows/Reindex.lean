/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Structure

/-! # Genuine exact reindexing of relative quotient rows

Only the actual added-initial-vertex map is used. All original acyclic tail
objects and inherited fine morphism classes are retained under restriction.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/Reindex.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- Relative rows reindex by the actual ordinal map fixing the added initial vertex. -/
def reindex {m n : SimplexCategory} (α : m ⟶ n) : Obj N n ⥤ Obj N m where
  obj F := ⟨(QuotientRows.reindex V (addInitial.map α)).obj F.obj,
    fun p ↦ F.property ((QuotientRows.indexMap α).obj p)⟩
  map η := (objects N m).homMk ((QuotientRows.reindex V (addInitial.map α)).map η.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem reindex_forget {m n : SimplexCategory} (α : m ⟶ n) :
    reindex N α ⋙ forget N m = forget N n ⋙ QuotientRows.reindex V (addInitial.map α) := rfl

@[simp] theorem reindex_zero {m n : SimplexCategory} (α : m ⟶ n) :
    (reindex N α).obj (zero N n) = zero N m := by
  apply ObjectProperty.FullSubcategory.ext
  exact QuotientRows.reindex_zero V (addInitial.map α)

/-- Every relative ordinal restriction is genuinely exact for the inherited fine structure. -/
theorem reindex_exact {m n : SimplexCategory} (α : m ⟶ n) :
    IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
      (waldhausenStructure N m).cof (waldhausenStructure N m).weq (reindex N α) where
  zero h := IsZero.of_full_of_faithful_of_isZero (forget N m) _
    ((QuotientRows.reindex_exact V (addInitial.map α)).zero ((forget_exact N n).zero h))
  cofibration _ h := (QuotientRows.reindex_exact V (addInitial.map α)).cofibration _ h
  weak _ h := (QuotientRows.reindex_exact V (addInitial.map α)).weak _ h
  pushout hf h := IsPushout.of_map_of_faithful (forget N m)
    ((QuotientRows.reindex_exact V (addInitial.map α)).pushout hf (forget_map_pushout N hf h))

/-- Equality of original ambient-row functors detects equality into the full relative category. -/
theorem functor_eq_of_comp_forget {D : Type u'} [Category.{v'} D] {n : SimplexCategory}
    {F G : D ⥤ Obj N n} (h : F ⋙ forget N n = G ⋙ forget N n) : F = G := by
  refine CategoryTheory.Functor.ext
    (fun X ↦ ObjectProperty.FullSubcategory.ext (CategoryTheory.Functor.congr_obj h X)) ?_
  intro X Y f
  apply (forget N n).map_injective
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.eqToHom_map]
  exact CategoryTheory.Functor.congr_hom h f

@[simp] theorem reindex_id (n : SimplexCategory) : reindex N (𝟙 n) = 𝟭 (Obj N n) := by
  apply functor_eq_of_comp_forget N
  simp only [reindex_forget, CategoryTheory.Functor.map_id, QuotientRows.reindex_id,
    CategoryTheory.Functor.comp_id, CategoryTheory.Functor.id_comp]

@[simp] theorem reindex_comp {l m n : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n) :
    reindex N (α ≫ β) = reindex N β ⋙ reindex N α := by
  apply functor_eq_of_comp_forget N
  calc
    reindex N (α ≫ β) ⋙ forget N l =
        forget N n ⋙ QuotientRows.reindex V (addInitial.map (α ≫ β)) := reindex_forget N _
    _ = forget N n ⋙ (QuotientRows.reindex V (addInitial.map β) ⋙
        QuotientRows.reindex V (addInitial.map α)) := by
      rw [CategoryTheory.Functor.map_comp, QuotientRows.reindex_comp]
    _ = (forget N n ⋙ QuotientRows.reindex V (addInitial.map β)) ⋙
        QuotientRows.reindex V (addInitial.map α) := rfl
    _ = (reindex N β ⋙ forget N m) ⋙ QuotientRows.reindex V (addInitial.map α) := by
      rw [reindex_forget]
    _ = reindex N β ⋙ (forget N m ⋙ QuotientRows.reindex V (addInitial.map α)) := rfl
    _ = reindex N β ⋙ (reindex N α ⋙ forget N l) := by rw [reindex_forget]
    _ = (reindex N β ⋙ reindex N α) ⋙ forget N l := rfl

/-- The actual tail projection, unlike first-object evaluation, is strictly outer-natural. -/
@[simp] theorem reindex_tailUnderlying {m n : SimplexCategory} (α : m ⟶ n) :
    reindex N α ⋙ tailUnderlying N m = tailUnderlying N n ⋙ QuotientRows.reindex V α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
