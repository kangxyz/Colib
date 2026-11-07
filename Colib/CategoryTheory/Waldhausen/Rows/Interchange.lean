/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.ReedyArrows

/-! # Interchanging the two genuine quotient-row directions

The transposition keeps every original component and map. Its horizontal
cofibrations are genuine row cofibrations, obtained from the proved exact
Reedy-arrow interchange, not merely componentwise cofibrations.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/Interchange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Evaluation in the inner direction, with the unchanged outer row. -/
def transposeDiagram {m n : SimplexCategory} (X : Obj (waldhausenStructure W n) m) :
    Interval n ⥤ Obj W m where
  obj p := (postcompose (waldhausenStructure W n) W (evaluation_exact W p) m).obj X
  map f := (objects W m).homMk {
    app q := (X.obj.obj q).obj.map f
    naturality q q' a := ((X.obj.map a).hom.naturality f).symm }
  map_id p := by
    apply ObjectProperty.hom_ext
    ext q
    exact (X.obj.obj q).obj.map_id p
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext q
    exact (X.obj.obj q).obj.map_comp f g

/-- The exact row/arrow interchange proves the full original Reedy condition. -/
theorem transposeDiagram_isRow {m n : SimplexCategory}
    (X : Obj (waldhausenStructure W n) m) :
    IsRow (waldhausenStructure W m) (transposeDiagram W X) where
  zero i := isZero_of_components W _ (fun q ↦ (X.obj.obj q).property.zero i)
  cofibration i j k hij hjk := by
    exact rowsReedyTransformation_cof W m
      ((postcompose (waldhausenStructure W n) (ExtensionCategory.waldhausenStructure W)
        (horizontalArrow_exact W i j k hij hjk) m).obj X)
  quotient i j k hij hjk := isPushout_of_pointwise W _ _ _ _
    (fun q ↦ (X.obj.obj q).property.quotient i j k hij hjk)

/-- Literal transposition of the two genuine quotient-row coordinates. -/
def transposeRows (m n : SimplexCategory) :
    Obj (waldhausenStructure W n) m ⥤ Obj (waldhausenStructure W m) n where
  obj X := ⟨transposeDiagram W X, transposeDiagram_isRow W X⟩
  map f := (objects (waldhausenStructure W m) n).homMk {
    app p := (objects W m).homMk {
      app q := (f.hom.app q).hom.app p
      naturality q q' a := congrArg (fun k ↦ k.hom.app p) (f.hom.naturality a) }
    naturality p p' a := by
      apply ObjectProperty.hom_ext
      ext q
      exact (f.hom.app q).hom.naturality a }
  map_id X := by
    apply ObjectProperty.hom_ext
    ext p q
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext p q
    rfl

@[simp] theorem transposeRows_obj_component {m n : SimplexCategory}
    (X : Obj (waldhausenStructure W n) m) (p : Interval n) (q : Interval m) :
    (((transposeRows W m n).obj X).obj.obj p).obj.obj q = (X.obj.obj q).obj.obj p := rfl

@[simp] theorem transposeRows_map_component {m n : SimplexCategory}
    {X Y : Obj (waldhausenStructure W n) m} (f : X ⟶ Y)
    (p : Interval n) (q : Interval m) :
    (((transposeRows W m n).map f).hom.app p).hom.app q = (f.hom.app q).hom.app p := rfl

@[simp] theorem transposeRows_twice (m n : SimplexCategory) :
    transposeRows W m n ⋙ transposeRows W n m = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Both inverses retain the actual component diagrams and maps. -/
def rowInterchange (m n : SimplexCategory) :
    Obj (waldhausenStructure W n) m ≌ Obj (waldhausenStructure W m) n :=
  CategoryTheory.Equivalence.mk (transposeRows W m n) (transposeRows W n m)
    (eqToIso (transposeRows_twice W m n).symm)
    (eqToIso (transposeRows_twice W n m))

/-- Every original horizontal arrow is the proved genuine row/arrow transpose. -/
theorem transposeRows_horizontalArrow {m n : SimplexCategory}
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    transposeRows W m n ⋙ horizontalArrow (waldhausenStructure W m) i j k hij hjk =
      postcompose (waldhausenStructure W n) (ExtensionCategory.waldhausenStructure W)
        (horizontalArrow_exact W i j k hij hjk) m ⋙ rowsToReedy W m := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The full Reedy cube condition is preserved, using exact arrow transposition. -/
theorem transposeRows_cof {m n : SimplexCategory}
    {X Y : Obj (waldhausenStructure W n) m} {f : X ⟶ Y}
    (hf : cof (waldhausenStructure W n) m f) :
    cof (waldhausenStructure W m) n ((transposeRows W m n).map f) := by
  intro i j k hij hjk
  exact rowsToReedy_cof W (postcompose_cof _ _ (horizontalArrow_exact W i j k hij hjk) hf)

/-- Transposition is genuinely exact, including the original Reedy cofibration class. -/
theorem transposeRows_exact (m n : SimplexCategory) :
    IsExact (waldhausenStructure (waldhausenStructure W n) m).cof
      (waldhausenStructure (waldhausenStructure W n) m).weq
      (waldhausenStructure (waldhausenStructure W m) n).cof
      (waldhausenStructure (waldhausenStructure W m) n).weq (transposeRows W m n) where
  zero h := isZero_of_components (waldhausenStructure W m) _ (fun p ↦
    isZero_of_components W _ (fun q ↦ evaluation_isZero W
      (evaluation_isZero (waldhausenStructure W n) h q) p))
  cofibration _ h := transposeRows_cof W h
  weak _ h p q := h q p
  pushout _ h := by
    let : (transposeRows W m n).IsEquivalence := (rowInterchange W m n).isEquivalence_functor
    exact h.map (transposeRows W m n)

/-- Ordinal restriction in the old outer direction becomes restriction in the new inner
direction. -/
theorem transposeRows_reindex_outer {m m' n : SimplexCategory} (α : m' ⟶ m) :
    reindex (waldhausenStructure W n) α ⋙ transposeRows W m' n =
      transposeRows W m n ⋙ postcompose (waldhausenStructure W m)
        (waldhausenStructure W m') (reindex_exact W α) n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Ordinal restriction in the old inner direction becomes restriction in the new outer
direction. -/
theorem transposeRows_reindex_inner {m n n' : SimplexCategory} (α : n' ⟶ n) :
    postcompose (waldhausenStructure W n) (waldhausenStructure W n') (reindex_exact W α) m ⋙
        transposeRows W m n' = transposeRows W m n ⋙ reindex (waldhausenStructure W m) α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.QuotientRows
