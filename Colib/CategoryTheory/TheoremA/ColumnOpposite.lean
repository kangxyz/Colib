/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.Augmentations
public import Colib.Topology.Realization.Opposite
public import Colib.Topology.ClassifyingSpace.NerveOpposite

/-! Source: Quillen/CategoryTheory/TheoremA/ColumnOpposite.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universal properties retained. -/

/-! Opposite-chain presentation of the source columns. -/
@[expose] public section

noncomputable section
open SSet CategoryTheory Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremA

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- Under categories vary covariantly with the opposite source category. -/
def sourceUnderDiagram (F : C ⥤ D) : Cᵒᵖ ⥤ Cat.{u, u} where
  obj c := Cat.of (StructuredArrow (F.obj c.unop) (𝟭 D))
  map f := (StructuredArrow.map (F.map f.unop)).toCatHom
  map_id c := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun X ↦ ?_) ?_
    · simp only [unop_id, F.map_id]
      exact StructuredArrow.map_id
    · intro X Y f
      apply StructuredArrow.hom_ext
      simp
  map_comp f g := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun X ↦ ?_) ?_
    · simp only [unop_comp, F.map_comp]
      exact StructuredArrow.map_comp
    · intro X Y h
      apply StructuredArrow.hom_ext
      simp

/-- The covariant nerve-valued diagram used for the source augmentation. -/
def sourceUnderNerveDiagram (F : C ⥤ D) : Cᵒᵖ ⥤ SSet.{u} :=
  sourceUnderDiagram F ⋙ nerveFunctor

/-- Reindex the under-category summands by reversed chains. -/
def sourceUnderColumnEquiv (F : C ⥤ D) (q p : SimplexCategoryᵒᵖ) :
    (commaColumnSummands F q).obj p ≃
      (replacementRow (sourceUnderNerveDiagram F) q).obj p :=
  Equiv.sigmaCongr (reverseChainEquiv q.unop.len) (fun _ ↦ Equiv.refl _)

/-- The decomposition with opposite chains respects the inner simplicial maps. -/
def sourceUnderColumnIso (F : C ⥤ D) (q : SimplexCategoryᵒᵖ) :
    commaColumnSummands F q ≅ replacementRow (sourceUnderNerveDiagram F) q :=
  NatIso.ofComponents (fun p ↦ (sourceUnderColumnEquiv F q p).toIso) (by
    intro p r α
    ext x : 3
    rfl)

/-- Reversing the outer simplex direction turns the source columns into
an ordinary covariant first-vertex simplicial replacement. -/
def sourceColumnsOppositeIso (F : C ⥤ D) :
    SimplexCategory.rev.op ⋙ (simplicialReplacement (commaNerveDiagram F)).flip ≅
      simplicialReplacement (sourceUnderNerveDiagram F) :=
  NatIso.ofComponents (fun q ↦ commaColumnIso F q ≪≫ sourceUnderColumnIso F q) (by
    intro q r α
    ext p x : 4
    dsimp [commaColumnIso, sourceUnderColumnIso, sourceUnderColumnEquiv,
      commaColumnSimplexEquiv, reverseChainEquiv, simplicialReplacement,
      replacementRowMap, sourceUnderNerveDiagram, sourceUnderDiagram,
      commaChainEquiv, structuredChainEquiv]
    apply Sigma.ext
    · exact reverseChain_naturality (C := C) α (x.2 ⋙ CostructuredArrow.proj F (x.1.obj 0))
    · change structuredChainOfFirst (𝟭 D) x.1
        (x.2.obj ((SimplexCategory.rev.map α.unop).toOrderHom
          (Fin.last r.unop.len))).hom ≍
        structuredChainOfFirst (𝟭 D) x.1 (x.2.obj (Fin.last q.unop.len)).hom ⋙
          StructuredArrow.map (F.map ((x.2.map (homOfLE
            (Fin.le_last (α.unop.toOrderHom 0).rev))).left))
      have hindex : (SimplexCategory.rev.map α.unop).toOrderHom
          (Fin.last r.unop.len) = (α.unop.toOrderHom 0).rev := by simp
      rw [hindex]
      apply heq_of_eq
      refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
      · refine StructuredArrow.obj_ext _ _ rfl ?_
        dsimp [structuredChainOfFirst]
        simpa only [Category.comp_id, Category.assoc] using
          congrArg (fun h ↦ h ≫ x.1.map (homOfLE (Fin.zero_le i)))
            (CostructuredArrow.w
              (x.2.map (homOfLE (Fin.le_last (α.unop.toOrderHom 0).rev)))).symm
      · intro i j f
        apply StructuredArrow.hom_ext
        simp [structuredChainOfFirst])

/-- On the base, the same reversal is precisely the nerve-opposite isomorphism. -/
def sourceBaseOppositeIso :
    SimplexCategory.rev.op ⋙
      ((Functor.const SimplexCategoryᵒᵖ).obj (nerve C)).flip ≅
      baseBisimplicial Cᵒᵖ :=
  Functor.isoWhiskerRight nerveOppositeIso (Functor.const SimplexCategoryᵒᵖ)

/-- The opposite-column presentation preserves the actual source augmentation. -/
theorem sourceColumnsOppositeIso_augmentation (F : C ⥤ D) :
    Functor.whiskerLeft SimplexCategory.rev.op
        ((CategoryTheory.flipFunctor _ _ _).map (sourceAugmentation F)) ≫
      sourceBaseOppositeIso.hom =
    (sourceColumnsOppositeIso F).hom ≫ targetAugmentation (sourceUnderNerveDiagram F) := by
  ext p q : 4
  rfl

/-- Every value of the source-column diagram is contractible by its initial object. -/
theorem sourceUnderNerveDiagram_contractible (F : C ⥤ D) (c : Cᵒᵖ) :
    ContractibleSpace |(sourceUnderNerveDiagram F).obj c| :=
  classifyingSpace_contractible_of_isInitial
    (StructuredArrow.mkIdInitial (T := 𝟭 D) (Y := F.obj c.unop))

end CategoryTheory.TheoremA
