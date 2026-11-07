/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.Opposite
public import Colib.CategoryTheory.TheoremA.IteratedRealization

/-! Source: Quillen/CategoryTheory/TheoremA/OuterOppositeRealization.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universal properties retained. -/

/-! Reversing either simplicial direction preserves actual diagonal realization. -/
@[expose] public section

noncomputable section
open SSet CategoryTheory Limits Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremA

/-- Geometric realization of simplicial spaces, with its actual coend maps. -/
def iteratedRealizationFunctor : (SimplexCategoryᵒᵖ ⥤ TopCat.{u}) ⥤ TopCat.{u} where
  obj := iteratedRealization
  map := iteratedRealizationMap
  map_id X := by
    apply coend.hom_ext
    intro n
    simp [iteratedRealizationMap, iteratedRealizationBifunctorMap]
    rfl
  map_comp f g := by
    apply coend.hom_ext
    intro n
    simp [iteratedRealizationMap, iteratedRealizationBifunctorMap]

/-- Reversing the diagonal after outer reversal agrees with inner reversal. -/
def diagonalOuterOppositeIso (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (diagonalSSet (SimplexCategory.rev.op ⋙ X)).op ≅
      diagonalSSet (X ⋙ SSet.opFunctor) :=
  NatIso.ofComponents (fun n ↦ Iso.refl _) (by
    intro n m f
    ext x : 3
    change (X.obj m).map (SimplexCategory.rev.map f.unop).op
      ((X.map (SimplexCategory.rev.map (SimplexCategory.rev.map f.unop)).op).app n x) =
      (X.obj m).map (SimplexCategory.rev.map f.unop).op ((X.map f).app n x)
    rw [SimplexCategory.rev_map_rev_map]
    rfl)

/-- Inner reversal is naturally invisible after realizing each row. -/
def innerOppositeRowsIso (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (X ⋙ SSet.opFunctor) ⋙ SSet.toTop ≅ X ⋙ SSet.toTop :=
  NatIso.ofComponents (fun n ↦ realizationOppositeNatIso.app (X.obj n)) (by
    intro n m f
    exact realizationOppositeNatIso.hom.naturality (X.map f))

/-- Reversing only the outer simplicial coordinate preserves the actual
realization of the diagonal. The bridge uses inner coordinate reversal on rows. -/
def outerOppositeRealizationIso (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    |diagonalSSet (SimplexCategory.rev.op ⋙ X)| ≅ |diagonalSSet X| :=
  (realizationOppositeNatIso.app (diagonalSSet (SimplexCategory.rev.op ⋙ X))).symm ≪≫
    SSet.toTop.mapIso (diagonalOuterOppositeIso X) ≪≫
    diagonalIteratedRealizationIso (X ⋙ SSet.opFunctor) ≪≫
    iteratedRealizationFunctor.mapIso (innerOppositeRowsIso X) ≪≫
    (diagonalIteratedRealizationIso X).symm

/-- The inner-row comparison is natural in a bisimplicial map. -/
theorem innerOppositeRowsIso_naturality
    {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) :
    Functor.whiskerRight (Functor.whiskerRight η SSet.opFunctor) SSet.toTop ≫
        (innerOppositeRowsIso Y).hom =
      (innerOppositeRowsIso X).hom ≫ Functor.whiskerRight η SSet.toTop := by
  apply NatTrans.ext
  funext n
  exact realizationOppositeNatIso.hom.naturality (η.app n)

/-- Outer/inner diagonal reversal is natural in the bisimplicial map. -/
theorem diagonalOuterOppositeIso_naturality
    {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) :
    SSet.opFunctor.map (diagonalMap (Functor.whiskerLeft SimplexCategory.rev.op η)) ≫
        (diagonalOuterOppositeIso Y).hom =
      (diagonalOuterOppositeIso X).hom ≫ diagonalMap (Functor.whiskerRight η SSet.opFunctor) := by
  ext n x : 4
  rfl

/-- Reversing the outer coordinate respects the exact canonical diagonal map. -/
theorem outerOppositeRealizationIso_naturality
    {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) :
    SSet.toTop.map (diagonalMap (Functor.whiskerLeft SimplexCategory.rev.op η)) ≫
        (outerOppositeRealizationIso Y).hom =
      (outerOppositeRealizationIso X).hom ≫ SSet.toTop.map (diagonalMap η) := by
  have h₁ := realizationOppositeNatIso.inv.naturality
    (diagonalMap (Functor.whiskerLeft SimplexCategory.rev.op η))
  change SSet.toTop.map (diagonalMap (Functor.whiskerLeft SimplexCategory.rev.op η)) ≫
      (realizationOppositeNatIso.app (diagonalSSet (SimplexCategory.rev.op ⋙ Y))).inv =
    (realizationOppositeNatIso.app (diagonalSSet (SimplexCategory.rev.op ⋙ X))).inv ≫
      SSet.toTop.map (SSet.opFunctor.map (diagonalMap (Functor.whiskerLeft SimplexCategory.rev.op
        η))) at h₁
  have h₂ := congrArg SSet.toTop.map (diagonalOuterOppositeIso_naturality η)
  simp only [Functor.map_comp] at h₂
  have h₃ := diagonalIteratedRealizationIso_naturality (Functor.whiskerRight η SSet.opFunctor)
  have h₄ := congrArg iteratedRealizationFunctor.map (innerOppositeRowsIso_naturality η)
  simp only [Functor.map_comp] at h₄
  have h₅ : iteratedRealizationMap (Functor.whiskerRight η SSet.toTop) ≫
      (diagonalIteratedRealizationIso Y).inv =
      (diagonalIteratedRealizationIso X).inv ≫ SSet.toTop.map (diagonalMap η) := by
    apply (cancel_mono (diagonalIteratedRealizationIso Y).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [diagonalIteratedRealizationIso_naturality, Iso.inv_hom_id_assoc]
  have c₁ := CommSq.mk h₁
  have c₂ := CommSq.mk h₂
  have c₃ := CommSq.mk h₃
  have c₄ := CommSq.mk h₄
  have c₅ := CommSq.mk h₅
  exact (c₁.vert_comp (c₂.vert_comp (c₃.vert_comp (c₄.vert_comp c₅)))).w

end CategoryTheory.TheoremA
