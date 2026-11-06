/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Reindex
public import Colib.CategoryTheory.Waldhausen.Rows.PostcomposeDetection
public import Colib.CategoryTheory.Waldhausen.Product.Structure

/-! # The actual acyclic tail functor and original relative projection

The tail quotients are lifted into the actual coarse-acyclic full category.
Their fine row cofibrations are proved by reflection through the original
exact inclusion and actual mapped relative pushouts.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/Tail.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The original tail quotient diagram, with its proved acyclic objects. -/
def acyclicTailDiagram {n : SimplexCategory} (X : Obj N n) : Interval n ⥤ AcyclicCategory N :=
  (acyclicObjects N).lift ((tailUnderlying N n).obj X).obj X.property

/-- The original quotient squares are genuine quotient squares in the actual acyclic category. -/
theorem acyclicTailDiagram_isRow {n : SimplexCategory} (X : Obj N n) :
    QuotientRows.IsRow (acyclicStructure N) (acyclicTailDiagram N X) where
  zero i := IsZero.of_full_of_faithful_of_isZero (acyclicObjects N).ι _
    (((tailUnderlying N n).obj X).property.zero i)
  cofibration i j k hij hjk := ((tailUnderlying N n).obj X).property.cofibration i j k hij hjk
  quotient i j k hij hjk := IsPushout.of_map_of_faithful (acyclicObjects N).ι
    (((tailUnderlying N n).obj X).property.quotient i j k hij hjk)

/-- The actual acyclic-tail row functor, retaining every original fine natural transformation. -/
def tailFunctor (n : SimplexCategory) : Obj N n ⥤ QuotientRows.Obj (acyclicStructure N) n where
  obj X := ⟨acyclicTailDiagram N X, acyclicTailDiagram_isRow N X⟩
  map f := (QuotientRows.objects _ n).homMk {
    app p := (acyclicObjects N).homMk (((tailUnderlying N n).map f).hom.app p)
    naturality _ _ a := by
      apply ObjectProperty.hom_ext
      exact ((tailUnderlying N n).map f).hom.naturality a }
  map_id _ := by apply ObjectProperty.hom_ext; ext p; rfl
  map_comp _ _ := by apply ObjectProperty.hom_ext; ext p; rfl

/-- Forgetting acyclicity gives precisely the original ambient tail row. -/
@[simp] theorem tailFunctor_postcompose (n : SimplexCategory) :
    tailFunctor N n ⋙ QuotientRows.postcompose (acyclicStructure N) V (acyclicInclusion_exact N) n =
      tailUnderlying N n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual tail functor is genuinely exact for the inherited fine weak class. -/
theorem tailFunctor_exact (n : SimplexCategory) :
    IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
      (QuotientRows.waldhausenStructure (acyclicStructure N) n).cof
      (QuotientRows.waldhausenStructure (acyclicStructure N) n).weq (tailFunctor N n) where
  zero h := QuotientRows.isZero_of_components _ _ (fun p ↦
    IsZero.of_full_of_faithful_of_isZero (acyclicObjects N).ι _
      (QuotientRows.evaluation_isZero V ((tailUnderlying_exact N n).zero h) p))
  cofibration f h := by
    apply QuotientRows.cof_of_postcompose (acyclicStructure N) V (acyclicInclusion_exact N)
      (fun {_ _} _ h ↦ h)
    exact (tailUnderlying_exact N n).cofibration f h
  weak f h p := (tailUnderlying_exact N n).weak f h p
  pushout hf h := by
    apply QuotientRows.isPushout_of_pointwise _ _ _ _ _
    intro p
    apply IsPushout.of_map_of_faithful (acyclicObjects N).ι
    exact QuotientRows.pointwise_of_isPushout V ((tailUnderlying_exact N n).cofibration _ hf)
      ((tailUnderlying_exact N n).pushout hf h) p

/-- The acyclic tail retains the actual chosen constant zero row. -/
@[simp] theorem tailFunctor_zero (n : SimplexCategory) :
    (tailFunctor N n).obj (zero N n) = QuotientRows.zero (acyclicStructure N) n := by
  apply ObjectProperty.FullSubcategory.ext
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The original acyclic-tail projection is strictly natural in the outer ordinal. -/
@[simp] theorem tailFunctor_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    reindex N α ⋙ tailFunctor N m =
      tailFunctor N n ⋙ QuotientRows.reindex (acyclicStructure N) α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual degreewise first-object/tail functor, with its literal product components. -/
def firstTail (n : SimplexCategory) : Obj N n ⥤ C × QuotientRows.Obj (acyclicStructure N) n :=
  (first N n).prod' (tailFunctor N n)

/-- The original first-object/tail functor is genuinely exact. -/
theorem firstTail_exact (n : SimplexCategory) :
    IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
      (Product.productStructure V (QuotientRows.waldhausenStructure (acyclicStructure
        N) n)).cof
      (Product.productStructure V (QuotientRows.waldhausenStructure (acyclicStructure
        N) n)).weq
      (firstTail N n) :=
  Product.pair_exact _ _ _ (first_exact N n) (tailFunctor_exact N n)

/-- The actual second projection is exactly the original tail functor. -/
@[simp] theorem firstTail_snd (n : SimplexCategory) :
    firstTail N n ⋙ CategoryTheory.Prod.snd _ _ = tailFunctor N n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
/-- The first projection is exactly the degreewise original first-object evaluation. -/
@[simp] theorem firstTail_fst (n : SimplexCategory) :
    firstTail N n ⋙ CategoryTheory.Prod.fst _ _ = first N n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
