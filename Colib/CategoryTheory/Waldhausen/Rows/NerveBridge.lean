/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.GridBridge
public import Mathlib.CategoryTheory.Widesubcategory

/-! # Original independent grids and the nerve of actual weak quotient rows

Every map below keeps the original grid components. The two directions are
an actual simplex equivalence, not just an equivalence of object predicates.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/Rows/NerveBridge.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd.
   Isolated strict compilation is recorded in the accompanying release report. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The category of original quotient rows and original pointwise weak arrows. -/
abbrev WeakRows (n : SimplexCategory) := WideSubcategory (weq W n)

/-- Equality transport is evaluated on the unchanged original component object. -/
@[simp] theorem weakRows_eqToHom_app {n : SimplexCategory} {X Y : WeakRows W n}
    (h : X = Y) (p : Interval n) :
    (eqToHom h).hom.hom.app p = eqToHom (congrArg (fun Z ↦ Z.obj.obj.obj p) h) := by
  subst Y
  rfl

/-- Read each original grid row and original nerve-direction map without changing it. -/
def gridToWeakChain {n k : SimplexCategory} (F : Grid₂ n k ⥤ C)
    (hF : IsSimplex₂ W.cof W.weq F) : ComposableArrows (WeakRows W n) k.len where
  obj t := ⟨⟨gridRestriction t ⋙ F, isRow_of_isSimplex₂ W hF t⟩⟩
  map {s t} f := ⟨(objects W n).homMk {
    app p := F.map (homOfLE (show (s,p) ≤ (t,p) from ⟨leOfHom f,le_rfl⟩))
    naturality p q a := by
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← F.map_comp, ← F.map_comp]
      congr 1 }, fun p ↦ hF.weak s t p.val.1 p.val.2 (leOfHom f) p.property⟩
  map_id t := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext p
    exact F.map_id (t,p)
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext p
    exact F.map_comp _ _

/-- Recover the original entire grid from the actual weak chain of rows. -/
def weakChainToGrid {n k : SimplexCategory} (F : ComposableArrows (WeakRows W n) k.len) :
    Grid₂ n k ⥤ C where
  obj p := (F.obj p.1).obj.obj.obj p.2
  map {p q} f := (F.obj p.1).obj.obj.map (homOfLE (leOfHom f).2) ≫
    (F.map (homOfLE (leOfHom f).1)).hom.hom.app q.2
  map_id p := by
    simp
  map_comp {p q r} f g := by
    rw [Category.assoc, ← Category.assoc ((F.map _).hom.hom.app q.2),
      ← (F.map (homOfLE (leOfHom f).1)).hom.hom.naturality (homOfLE (leOfHom g).2)]
    simp only [← Category.assoc]
    have ht := F.map_comp (homOfLE (leOfHom f).1) (homOfLE (leOfHom g).1)
    have hv := (F.obj p.1).obj.obj.map_comp (homOfLE (leOfHom f).2) (homOfLE (leOfHom g).2)
    rw [← hv]
    change _ ≫ (F.map _).hom.hom.app _ = _
    have ht' := congrArg (fun z ↦ z.hom.hom.app r.2) ht
    change (F.map (homOfLE ((leOfHom f).1.trans (leOfHom g).1))).hom.hom.app r.2 =
      (F.map (homOfLE (leOfHom f).1)).hom.hom.app r.2 ≫
        (F.map (homOfLE (leOfHom g).1)).hom.hom.app r.2 at ht'
    simpa only [Category.assoc, homOfLE_comp] using congrArg
      (fun z ↦ (F.obj p.1).obj.obj.map (homOfLE ((leOfHom f).2.trans (leOfHom g).2)) ≫ z) ht'

/-- Every object of the reconstructed grid is its original row object. -/
@[simp] theorem weakChainToGrid_obj {n k : SimplexCategory}
    (F : ComposableArrows (WeakRows W n) k.len) (t : Fin (k.len + 1)) (p : Interval n) :
    (weakChainToGrid W F).obj (t, p) = (F.obj t).obj.obj.obj p := rfl

/-- Every grid morphism uses its original row map followed by its original nerve map. -/
@[simp] theorem weakChainToGrid_map {n k : SimplexCategory}
    (F : ComposableArrows (WeakRows W n) k.len) {p q : Grid₂ n k} (f : p ⟶ q) :
    (weakChainToGrid W F).map f =
      (F.obj p.1).obj.obj.map (homOfLE (leOfHom f).2) ≫
        (F.map (homOfLE (leOfHom f).1)).hom.hom.app q.2 := rfl


/-- The reconstructed grid has the unchanged zero, cofibration, quotient and weak predicates. -/
theorem weakChainToGrid_isSimplex₂ {n k : SimplexCategory}
    (F : ComposableArrows (WeakRows W n) k.len) :
    IsSimplex₂ W.cof W.weq (weakChainToGrid W F) where
  zero t i := (F.obj t).obj.property.zero i
  cofibration t i j k hij hjk := by
    simpa [weakChainToGrid, grid₂] using (F.obj t).obj.property.cofibration i j k hij hjk
  quotient t i j k hij hjk := by
    simpa [weakChainToGrid, grid₂] using (F.obj t).obj.property.quotient i j k hij hjk
  weak s t i j hst hij := by
    simpa [weakChainToGrid, grid₂] using
      (F.map (homOfLE hst)).property (interval i j hij)

/-- Restriction of the reconstructed grid gives back the original entire row functor. -/
theorem weakChainToGrid_row {n k : SimplexCategory}
    (F : ComposableArrows (WeakRows W n) k.len) (t : Fin (k.len + 1)) :
    gridRestriction t ⋙ weakChainToGrid W F = (F.obj t).obj.obj := by
  refine CategoryTheory.Functor.ext (F := gridRestriction t ⋙ weakChainToGrid W F)
    (G := (F.obj t).obj.obj) (fun _ ↦ rfl) ?_
  intro p q a
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (weakChainToGrid W F).map
    (homOfLE (show ((t, p) : Grid₂ n k) ≤ (t, q) from ⟨le_rfl, leOfHom a⟩)) = _
  rw [weakChainToGrid_map]
  simp only [homOfLE_refl, homOfLE_leOfHom, CategoryTheory.Functor.map_id,
    WideSubcategory.id_def, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    Category.comp_id]
  exact (F.obj t).obj.obj.congr_map (Subsingleton.elim _ _)

/-- Reconstructing an original grid recovers every original arrow, including mixed ones. -/
theorem weakChainToGrid_gridToWeakChain {n k : SimplexCategory} (F : Grid₂ n k ⥤ C)
    (hF : IsSimplex₂ W.cof W.weq F) :
    weakChainToGrid W (gridToWeakChain W F hF) = F := by
  refine CategoryTheory.Functor.ext (F := weakChainToGrid W (gridToWeakChain W F hF))
    (G := F) (fun _ ↦ rfl) ?_
  intro p q a
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change F.map _ ≫ F.map _ = _
  rw [← F.map_comp]
  rfl

/-- Reading the reconstructed grid recovers the unchanged original weak chain. -/
theorem gridToWeakChain_weakChainToGrid {n k : SimplexCategory}
    (F : ComposableArrows (WeakRows W n) k.len) :
    gridToWeakChain W (weakChainToGrid W F) (weakChainToGrid_isSimplex₂ W F) = F := by
  refine CategoryTheory.Functor.ext (fun t ↦ ?_) ?_
  · apply WideSubcategory.ext
    exact ObjectProperty.FullSubcategory.ext (weakChainToGrid_row W F t)
  · intro s t a
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    ext p
    simp [gridToWeakChain, weakChainToGrid, weakRows_eqToHom_app]
    rfl

/-- The actual original-grid simplex and the actual weak-row nerve simplex are equivalent. -/
def gridWeakChainEquiv (n k : SimplexCategory) :
    {F : Grid₂ n k ⥤ C // IsSimplex₂ W.cof W.weq F} ≃
      ComposableArrows (WeakRows W n) k.len where
  toFun F := gridToWeakChain W F.val F.property
  invFun F := ⟨weakChainToGrid W F, weakChainToGrid_isSimplex₂ W F⟩
  left_inv F := Subtype.ext (weakChainToGrid_gridToWeakChain W F.val F.property)
  right_inv := gridToWeakChain_weakChainToGrid W

end CategoryTheory.Waldhausen.QuotientRows
