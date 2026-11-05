/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Basic

/-! # Weak-map-preserving reindexing of actual quotient rows along every ordinal map

The zero, horizontal cofibration, and quotient conditions are retained by
interval restriction. Pointwise weak-map preservation needs no row Waldhausen structure.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/Rows/Reindex.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd.
   Isolated strict compilation is recorded in the accompanying release report. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The interval functor underlying the original S-direction ordinal restriction. -/
def indexMap {m n : SimplexCategory} (α : m ⟶ n) : Interval m ⥤ Interval n :=
  (show Monotone (fun p : Interval m ↦
      interval (α.toOrderHom p.val.1) (α.toOrderHom p.val.2) (α.toOrderHom.monotone p.property))
        from
    fun _ _ h ↦ ⟨α.toOrderHom.monotone h.1, α.toOrderHom.monotone h.2⟩).functor

/-- Ordinary S-row restriction retains all original quotient-grid axioms. -/
theorem IsRow.precomp {m n : SimplexCategory} {F : Interval n ⥤ C}
    (hF : IsRow W F) (α : m ⟶ n) : IsRow W (indexMap α ⋙ F) where
  zero i := hF.zero (α.toOrderHom i)
  cofibration _ _ _ hij hjk := hF.cofibration _ _ _ (α.toOrderHom.monotone hij)
    (α.toOrderHom.monotone hjk)
  quotient _ _ _ hij hjk := hF.quotient _ _ _ (α.toOrderHom.monotone hij) (α.toOrderHom.monotone
    hjk)

/-- The actual reindexing functor on full quotient-row categories. -/
def reindex {m n : SimplexCategory} (α : m ⟶ n) : Obj W n ⥤ Obj W m where
  obj F := ⟨indexMap α ⋙ F.obj, F.property.precomp W α⟩
  map η := (objects W m).homMk (Functor.whiskerLeft (indexMap α) η.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem reindex_obj_diagram {m n : SimplexCategory} (α : m ⟶ n) (F : Obj W n) :
    ((reindex W α).obj F).obj = indexMap α ⋙ F.obj := rfl

@[simp] theorem reindex_map_app {m n : SimplexCategory} (α : m ⟶ n)
    {F G : Obj W n} (η : F ⟶ G) (p : Interval m) :
    ((reindex W α).map η).hom.app p = η.hom.app ((indexMap α).obj p) := rfl

@[simp] theorem reindex_zero {m n : SimplexCategory} (α : m ⟶ n) :
    (reindex W α).obj (zero W n) = zero W m := by
  apply ObjectProperty.FullSubcategory.ext
  rfl

/-- Every ordinal restriction preserves the original pointwise weak maps. -/
theorem reindex_weq {m n : SimplexCategory} (α : m ⟶ n)
    {F G : Obj W n} {η : F ⟶ G} (hη : weq W n η) : weq W m ((reindex W α).map η) := by
  intro p
  exact hη ((indexMap α).obj p)

@[simp] theorem reindex_id (n : SimplexCategory) : reindex W (𝟙 n) = 𝟭 (Obj W n) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem reindex_comp {l m n : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n) :
    reindex W (α ≫ β) = reindex W β ⋙ reindex W α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.QuotientRows
