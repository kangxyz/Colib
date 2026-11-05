/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Colib.CategoryTheory.Waldhausen.SConstruction

/-! # Actual quotient-row categories and pointwise weak maps

Objects are precisely genuine S-construction quotient grids without the
nerve coordinate. All natural transformations are retained as morphisms.
The weak maps are pointwise weak natural transformations. Row-level Reedy
cofibrations and the row Waldhausen structure are intentionally not dependencies.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/Rows/Basic.lean
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

/-- The original S-construction row conditions on the original interval poset. -/
structure IsRow {n : SimplexCategory} (F : Interval n ⥤ C) : Prop where
  zero (i) : IsZero (F.obj (interval i i le_rfl))
  cofibration (i j k) (hij : i ≤ j) (hjk : j ≤ k) :
    W.cof (F.map (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl,
      hjk⟩)))
  quotient (i j k) (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout
      (F.map (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl, hjk⟩)))
      (F.map (homOfLE (show interval i j hij ≤ interval j j le_rfl from ⟨hij, le_rfl⟩)))
      (F.map (homOfLE (show interval i k (hij.trans hjk) ≤ interval j k hjk from ⟨hij, le_rfl⟩)))
      (F.map (homOfLE (show interval j j le_rfl ≤ interval j k hjk from ⟨le_rfl, hjk⟩)))

/-- The predicate selecting interval diagrams with zero diagonal objects, horizontal
cofibrations, and the quotient pushout squares specified by `IsRow W`. -/
def objects (n : SimplexCategory) : ObjectProperty (Interval n ⥤ C) := IsRow W
/-- The full category of quotient-row diagrams satisfying the S-construction row conditions,
retaining all natural transformations as morphisms. -/
abbrev Obj (n : SimplexCategory) := (objects W n).FullSubcategory

/-- The full-subcategory inclusion of quotient rows into all diagrams on `Interval n`. -/
def forget (n : SimplexCategory) : Obj W n ⥤ (Interval n ⥤ C) := (objects W n).ι
instance forget_full (n) : (forget W n).Full := by unfold forget; infer_instance
instance forget_faithful (n) : (forget W n).Faithful := by unfold forget; infer_instance

/-- The functor taking a quotient row to its component at the interval `p` and a natural
transformation to its component map there. -/
def evaluation {n : SimplexCategory} (p : Interval n) : Obj W n ⥤ C :=
  forget W n ⋙ (CategoryTheory.evaluation (Interval n) C).obj p

/-- Weak equivalences remain pointwise weak natural transformations. -/
def weq (n : SimplexCategory) : MorphismProperty (Obj W n) := fun _ _ η ↦
  ∀ p, W.weq (η.hom.app p)

instance weq_multiplicative (n : SimplexCategory) : (weq W n).IsMultiplicative where
  id_mem _ _ := W.weq.id_mem _
  comp_mem _ _ hη hθ p := W.weq.comp_mem _ _ (hη p) (hθ p)

theorem weq_iso (n : SimplexCategory) : MorphismProperty.isomorphisms (Obj W n) ≤ weq W n := by
  intro F G η hη p
  let : IsIso η := hη
  exact W.weq_iso _ (inferInstance : IsIso ((evaluation W p).map η))

/-- The literal constant chosen-zero row is a genuine quotient grid. -/
def zero (n : SimplexCategory) : Obj W n :=
  ⟨(Functor.const (Interval n)).obj W.zero, {
    zero _ := W.isZero
    cofibration _ _ _ _ _ := W.cof.id_mem _
    quotient _ _ _ _ _ := IsPushout.id_horiz (𝟙 W.zero) }⟩

theorem isZero (n : SimplexCategory) : IsZero (zero W n) where
  unique_to F := by
    refine ⟨{ default := (objects W n).homMk {
      app p := W.isZero.to_ (F.obj.obj p)
      naturality _ _ _ := W.isZero.eq_of_src _ _ }, uniq := ?_ }⟩
    intro η
    apply ObjectProperty.hom_ext
    ext p
    exact W.isZero.eq_of_src _ _
  unique_from F := by
    refine ⟨{ default := (objects W n).homMk {
      app p := W.isZero.from_ (F.obj.obj p)
      naturality _ _ _ := W.isZero.eq_of_tgt _ _ }, uniq := ?_ }⟩
    intro η
    apply ObjectProperty.hom_ext
    ext p
    exact W.isZero.eq_of_tgt _ _

end CategoryTheory.Waldhausen.QuotientRows
