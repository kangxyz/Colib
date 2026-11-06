/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.PointwiseArrows
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.TransposeExact

/-! # Actual interchange of quotient rows and genuine Reedy cofibration arrows

The original component diagrams determine inverse categorical functors.
Preservation of cofibration cubes uses the proved exact Reedy transposition
and actual mapped relative pushouts, rather than categorical equivalence alone.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/ReedyArrows.lean`
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

/-- All actual horizontal-arrow tests, including the degenerate intervals. -/
structure HorizontalTriple (n : SimplexCategory) where
  /-- The common left endpoint of the intervals in a horizontal-arrow test. -/
  i : Fin (n.len + 1)
  /-- The right endpoint of the source interval in the test, with `i ≤ j`. -/
  j : Fin (n.len + 1)
  /-- The right endpoint of the target interval in the test, with `j ≤ k`. -/
  k : Fin (n.len + 1)
  hij : i ≤ j
  hjk : j ≤ k

/-- The literal component-cofibration diagram of a genuine cofibration between rows. -/
def reedyDiagram {n : SimplexCategory} (X : ExtensionCategory.Obj (waldhausenStructure W n)) :
    Interval n ⥤ ExtensionCategory.Obj W where
  obj p := ⟨Arrow.mk (X.obj.hom.hom.app p), cof_app W X.property p⟩
  map f := (ExtensionCategory.objects W).homMk
    (Arrow.homMk (X.obj.left.obj.map f) (X.obj.right.obj.map f) (X.obj.hom.hom.naturality f))
  map_id p := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> exact CategoryTheory.Functor.map_id _ p
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> exact CategoryTheory.Functor.map_comp _ f g

/-- The original all-triples condition gives genuine horizontal Reedy arrows
by the actual transposed relative pushout. -/
theorem reedyDiagram_isRow {n : SimplexCategory}
    (X : ExtensionCategory.Obj (waldhausenStructure W n)) :
    IsRow (ExtensionCategory.waldhausenStructure W) (reedyDiagram W X) where
  zero p := ExtensionCategory.isZero_of_components W _
    (X.obj.left.property.zero p) (X.obj.right.property.zero p)
  cofibration i j k hij hjk :=
    (ExtensionCategory.transposeSquare W ((horizontalArrow W i j k hij hjk).map X.obj.hom)
      (X.property i j k hij hjk)).property
  quotient i j k hij hjk := IsPushout.of_map_of_faithful (ExtensionCategory.forget W)
    (ExtensionCategory.arrow_isPushout _ _ _ _
      (X.obj.left.property.quotient i j k hij hjk) (X.obj.right.property.quotient i j k hij hjk))

/-- A genuine cofibration between rows is sent to its original component-cofibration row. -/
def reedyToRows (n : SimplexCategory) :
    ExtensionCategory.Obj (waldhausenStructure W n) ⥤ Obj (ExtensionCategory.waldhausenStructure
      W) n where
  obj X := ⟨reedyDiagram W X, reedyDiagram_isRow W X⟩
  map f := (objects _ n).homMk {
    app p := (ExtensionCategory.objects W).homMk (((arrowDiagram W n).map f.hom).app p)
    naturality _ _ a := by
      apply ObjectProperty.hom_ext
      exact ((arrowDiagram W n).map f.hom).naturality a }
  map_id _ := by
    apply ObjectProperty.hom_ext
    ext p <;> rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    ext p <;> rfl

/-- The literal structural arrows give a transformation of the two endpoint-row functors. -/
def rowsReedyTransformation (n : SimplexCategory) :
    postcompose (ExtensionCategory.waldhausenStructure W) W (ExtensionCategory.source_exact W) n ⟶
      postcompose (ExtensionCategory.waldhausenStructure W) W (ExtensionCategory.middle_exact W)
        n where
  app X := (objects W n).homMk (Functor.whiskerLeft X.obj (ExtensionCategory.inclusion W))
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    ext p
    exact (f.hom.app p).hom.w

/-- Every structural transformation is an actual row cofibration, by the original
horizontal Reedy tests and their transposed relative pushouts. -/
theorem rowsReedyTransformation_cof (n : SimplexCategory)
    (X : Obj (ExtensionCategory.waldhausenStructure W) n) :
    cof W n ((rowsReedyTransformation W n).app X) := by
  intro i j k hij hjk
  exact (ExtensionCategory.transposeSquare W
    (X.obj.map (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl, hjk⟩)))
    (X.property.cofibration i j k hij hjk)).property

/-- Collect the original component cofibrations into their genuine row-cofibration arrow. -/
def rowsToReedy (n : SimplexCategory) :
    Obj (ExtensionCategory.waldhausenStructure W) n ⥤ ExtensionCategory.Obj (waldhausenStructure
      W n) where
  obj X := ⟨Arrow.mk ((rowsReedyTransformation W n).app X), rowsReedyTransformation_cof W n X⟩
  map f := (ExtensionCategory.objects _).homMk
    ((ArrowDiagrams.toDiagramObj (Arrow.mk (rowsReedyTransformation W n))).map f)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (ArrowDiagrams.toDiagramObj (Arrow.mk (rowsReedyTransformation W n))).map_id X
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (ArrowDiagrams.toDiagramObj (Arrow.mk (rowsReedyTransformation W n))).map_comp f g

@[simp] theorem reedyToRows_obj_hom {n : SimplexCategory}
    (X : ExtensionCategory.Obj (waldhausenStructure W n)) (p : Interval n) :
    (((reedyToRows W n).obj X).obj.obj p).obj.hom = X.obj.hom.hom.app p := rfl
@[simp] theorem rowsToReedy_obj_hom_app {n : SimplexCategory}
    (X : Obj (ExtensionCategory.waldhausenStructure W) n) (p : Interval n) :
    ((rowsToReedy W n).obj X).obj.hom.hom.app p = (X.obj.obj p).obj.hom := rfl

@[simp] theorem reedyToRows_rowsToReedy (n : SimplexCategory) :
    reedyToRows W n ⋙ rowsToReedy W n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
@[simp] theorem rowsToReedy_reedyToRows (n : SimplexCategory) :
    rowsToReedy W n ⋙ reedyToRows W n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The genuine Reedy-arrow interchange retains the literal original component diagrams. -/
def reedyArrowEquivalence (n : SimplexCategory) :
    ExtensionCategory.Obj (waldhausenStructure W n) ≌ Obj (ExtensionCategory.waldhausenStructure
      W) n :=
  CategoryTheory.Equivalence.mk (reedyToRows W n) (rowsToReedy W n)
    (eqToIso (reedyToRows_rowsToReedy W n).symm) (eqToIso (rowsToReedy_reedyToRows W n))

/-- Restricting the collected row cofibration gives precisely the transposed original square. -/
theorem rowsToReedy_horizontalArrow {n : SimplexCategory}
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    rowsToReedy W n ⋙ ExtensionCategory.postcompose _ _ (horizontalArrow_exact W i j k hij hjk) =
      horizontalArrow (ExtensionCategory.waldhausenStructure W) i j k hij hjk ⋙
        ExtensionCategory.transpose W := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- All original Reedy cube tests are preserved using actual three-direction pushout symmetry. -/
theorem reedyToRows_cof {n : SimplexCategory}
    {X Y : ExtensionCategory.Obj (waldhausenStructure W n)} {f : X ⟶ Y}
    (hf : ExtensionCategory.cof (waldhausenStructure W n) f) :
    cof (ExtensionCategory.waldhausenStructure W) n ((reedyToRows W n).map f) := by
  intro i j k hij hjk
  exact ExtensionCategory.transpose_cof W
    (ExtensionCategory.postcompose_cof _ _ (horizontalArrow_exact W i j k hij hjk) hf)

/-- The converse uses joint detection of the original all-triples cofibration
class and the actual mapped relative pushouts. -/
theorem rowsToReedy_cof {n : SimplexCategory}
    {X Y : Obj (ExtensionCategory.waldhausenStructure W) n} {f : X ⟶ Y}
    (hf : cof (ExtensionCategory.waldhausenStructure W) n f) :
    ExtensionCategory.cof (waldhausenStructure W n) ((rowsToReedy W n).map f) := by
  apply ExtensionCategory.cof_of_postcompose_family (waldhausenStructure W n)
    (ExtensionCategory.waldhausenStructure W)
    (fun t : HorizontalTriple n ↦ horizontalArrow W t.i t.j t.k t.hij t.hjk)
    (fun t ↦ horizontalArrow_exact W t.i t.j t.k t.hij t.hjk)
  · intro A B η h i j k hij hjk
    exact h ⟨i, j, k, hij, hjk⟩
  · intro t
    exact ExtensionCategory.transpose_cof W (hf t.i t.j t.k t.hij t.hjk)

/-- Component-cofibration rows are obtained by an actual exact functor. -/
theorem reedyToRows_exact (n : SimplexCategory) :
    IsExact (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).cof
      (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).weq
      (waldhausenStructure (ExtensionCategory.waldhausenStructure W) n).cof
      (waldhausenStructure (ExtensionCategory.waldhausenStructure W) n).weq (reedyToRows W n) where
  zero h := (isZero (ExtensionCategory.waldhausenStructure W) n).of_iso
    ((reedyToRows W n).mapIso (h.iso (ExtensionCategory.isZero (waldhausenStructure W n))))
  cofibration _ h := reedyToRows_cof W h
  weak _ h p := ⟨h.1 p, h.2 p⟩
  pushout _ h := by
    let : (reedyToRows W n).IsEquivalence := (reedyArrowEquivalence W n).isEquivalence_functor
    exact h.map (reedyToRows W n)

/-- Collecting the original component cofibrations is an actual exact functor. -/
theorem rowsToReedy_exact (n : SimplexCategory) :
    IsExact (waldhausenStructure (ExtensionCategory.waldhausenStructure W) n).cof
      (waldhausenStructure (ExtensionCategory.waldhausenStructure W) n).weq
      (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).cof
      (ExtensionCategory.waldhausenStructure (waldhausenStructure W n)).weq (rowsToReedy W n) where
  zero h := (ExtensionCategory.isZero (waldhausenStructure W n)).of_iso
    ((rowsToReedy W n).mapIso (h.iso (isZero (ExtensionCategory.waldhausenStructure W) n)))
  cofibration _ h := rowsToReedy_cof W h
  weak _ h := ⟨fun p ↦ (h p).1, fun p ↦ (h p).2⟩
  pushout _ h := by
    let : (rowsToReedy W n).IsEquivalence := (reedyArrowEquivalence W n).isEquivalence_inverse
    exact h.map (rowsToReedy W n)

end CategoryTheory.Waldhausen.QuotientRows
