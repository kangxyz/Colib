/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.TailQuotient
public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.SplitFiberZero
public import Colib.CategoryTheory.Waldhausen.Additivity.SplitSequence

/-! # The actual coproduct section of the first-object/tail functor

The section sends a pair to the coproduct of its zero-first tail section and
its constant zero-tail fiber. Its first/tail composite is naturally isomorphic
to the original pair through the images of the original coproduct inclusions.
The isomorphisms are derived from genuine mapped pushouts and zero objects.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/ProductSection.lean`
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
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (n : SimplexCategory)
variable [HasBinaryCoproducts (Obj N n)]

/-- The original tail-section/fiber coproduct on actual pairs. -/
def splitFunctor : C × QuotientRows.Obj (acyclicStructure N) n ⥤ Obj N n :=
  CategoryTheory.sumFunctor
    (CategoryTheory.Prod.snd _ _ ⋙ tailSection N n)
    (CategoryTheory.Prod.fst _ _ ⋙ fiber N n)

@[simp] theorem splitFunctor_obj (X : C × QuotientRows.Obj (acyclicStructure N) n) :
    (splitFunctor N n).obj X = ((tailSection N n).obj X.2 ⨿ (fiber N n).obj X.1) := rfl

@[simp] theorem splitFunctor_map {X Y : C × QuotientRows.Obj (acyclicStructure N) n}
    (f : X ⟶ Y) :
    (splitFunctor N n).map f = coprod.map ((tailSection N n).map f.2) ((fiber N n).map f.1) := rfl

/-- Exactness of the actual section follows from exact projections and coproducts. -/
theorem splitFunctor_exact :
    IsExact (Product.productStructure V
        (QuotientRows.waldhausenStructure (acyclicStructure N) n)).cof
      (Product.productStructure V
        (QuotientRows.waldhausenStructure (acyclicStructure N) n)).weq
      (waldhausenStructure N n).cof (waldhausenStructure N n).weq (splitFunctor N n) :=
  Additivity.sumFunctor_isExact _ _
    ((Product.snd_exact _ _).comp (tailSection_exact N n))
    ((Product.fst_exact _ _).comp (fiber_exact N n))

/-- The original first object enters through the original fiber summand. -/
theorem first_map_split_inr_isIso (X : C × QuotientRows.Obj (acyclicStructure N) n) :
    IsIso ((first N n).map (coprod.inr : (fiber N n).obj X.1 ⟶ (splitFunctor N n).obj X)) := by
  let splitFirstZero : IsIso ((first N n).map
      ((isZero N n).to_ ((tailSection N n).obj X.2))) :=
    ((first_exact N n).zero (isZero N n)).isIso (tailSection_first_isZero N n X.2) _
  exact ((first_exact N n).pushout ((waldhausenStructure N n).cof_zero _)
    (Additivity.coprod_isPushout (waldhausenStructure N n)
      ((tailSection N n).obj X.2) ((fiber N n).obj X.1))).isIso_inr_of_isIso

/-- The original tail enters through the original tail-section summand. -/
theorem tail_map_split_inl_isIso (X : C × QuotientRows.Obj (acyclicStructure N) n) :
    IsIso ((tailFunctor N n).map
      (coprod.inl : (tailSection N n).obj X.2 ⟶ (splitFunctor N n).obj X)) := by
  have hz : IsZero ((tailFunctor N n).obj ((fiber N n).obj X.1)) :=
    QuotientRows.isZero (acyclicStructure N) n
  let splitTailZero : IsIso ((tailFunctor N n).map
      ((isZero N n).to_ ((fiber N n).obj X.1))) :=
    ((tailFunctor_exact N n).zero (isZero N n)).isIso hz _
  exact ((tailFunctor_exact N n).pushout ((waldhausenStructure N n).cof_zero _)
    (Additivity.coprod_isPushout (waldhausenStructure N n)
      ((tailSection N n).obj X.2) ((fiber N n).obj X.1))).isIso_inl_of_isIso

/-- The actual pair of original summand inclusions, after first/tail evaluation. -/
def splitFunctorUnit : 𝟭 (C × QuotientRows.Obj (acyclicStructure N) n) ⟶
    splitFunctor N n ⋙ firstTail N n where
  app X := ((first N n).map (coprod.inr : (fiber N n).obj X.1 ⟶ (splitFunctor N n).obj X),
      (tailFunctor N n).map (coprod.inl : (tailSection N n).obj X.2 ⟶ (splitFunctor N n).obj X))
  naturality X Y f := by
    apply _root_.Prod.ext
    · change (first N n).map ((fiber N n).map f.1) ≫ (first N n).map coprod.inr =
        (first N n).map coprod.inr ≫ (first N n).map
          (coprod.map ((tailSection N n).map f.2) ((fiber N n).map f.1))
      rw [← Functor.map_comp, ← Functor.map_comp, coprod.inr_map]
    · change (tailFunctor N n).map ((tailSection N n).map f.2) ≫ (tailFunctor N n).map coprod.inl =
        (tailFunctor N n).map coprod.inl ≫ (tailFunctor N n).map
          (coprod.map ((tailSection N n).map f.2) ((fiber N n).map f.1))
      rw [← Functor.map_comp, ← Functor.map_comp, coprod.inl_map]

/-- Both original summand inclusions become genuine isomorphisms. -/
theorem splitFunctorUnit_app_isIso (X : C × QuotientRows.Obj (acyclicStructure N) n) :
    IsIso ((splitFunctorUnit N n).app X) :=
  (CategoryTheory.isIso_prod_iff _ _).2
    ⟨first_map_split_inr_isIso N n X, tail_map_split_inl_isIso N n X⟩

/-- The section followed by the original first/tail functor is genuinely the identity up to iso. -/
def splitFirstTailIso : splitFunctor N n ⋙ firstTail N n ≅
    𝟭 (C × QuotientRows.Obj (acyclicStructure N) n) := by
  letI splitUnitComponentIso (X : C × QuotientRows.Obj (acyclicStructure N) n) :
      IsIso ((splitFunctorUnit N n).app X) := splitFunctorUnit_app_isIso N n X
  letI splitUnitIso : IsIso (splitFunctorUnit N n) := NatIso.isIso_of_isIso_app _
  exact (asIso (splitFunctorUnit N n)).symm

/-- The inverse retains exactly the original first/tail images of the coproduct inclusions. -/
@[simp] theorem splitFirstTailIso_inv_app (X : C × QuotientRows.Obj (acyclicStructure N) n) :
    (splitFirstTailIso N n).inv.app X =
      ((first N n).map (coprod.inr : (fiber N n).obj X.1 ⟶ (splitFunctor N n).obj X),
      (tailFunctor N n).map (coprod.inl : (tailSection N n).obj X.2 ⟶ (splitFunctor N n).obj X))
        := rfl

/-- In the other order, the actual section is exactly tail quotient plus the original first
fiber. -/
theorem firstTail_splitFunctor : firstTail N n ⋙ splitFunctor N n =
    CategoryTheory.sumFunctor (tailQuotientFunctor N n) (first N n ⋙ fiber N n) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
