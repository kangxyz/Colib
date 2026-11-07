/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionAction
public import Colib.CategoryTheory.ExactCategory.Extensions.ProductKernel

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionProductAction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Compatibility of fixed-quotient pullback multiplication with direct sum -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal extensionFiberDirectSumAction

attribute [simp] extensionAction_obj_hom

/-- The actual pullback product, with fixed quotient, as a fiber object. -/
abbrev extensionProductFiber {C : Category.{u, u} R}
    (p q : (exactStructure R).ExtensionFiber C) : (exactStructure R).ExtensionFiber C :=
  ((exactStructure R).extensionFiberProduct C).obj (p, q)

private theorem coprod_decomposition (A B : Category.{u, u} R) :
    coprod.desc (𝟙 A) (0 : B ⟶ A) ≫ coprod.inl +
      coprod.desc (0 : A ⟶ B) (𝟙 B) ≫ coprod.inr = 𝟙 (A ⨿ B) := by
  apply coprod.hom_ext <;> simp [Preadditive.comp_add]

/-- The canonical distributivity map sends the first and second new summands
into the corresponding pullback factors and retains both old projections. -/
def extensionAddProductHom {C : Category.{u, u} R} (S T : IsoCategory R)
    (p q : (exactStructure R).ExtensionFiber C) :
    ((S ⊗ T) ⊙ₗ extensionProductFiber R p q).of.obj.left ⟶
      (extensionProductFiber R (S ⊙ₗ p) (T ⊙ₗ q)).of.obj.left :=
  pullback.lift
    (coprod.desc (coprod.desc coprod.inl 0) (pullback.fst _ _ ≫ coprod.inr))
    (coprod.desc (coprod.desc 0 coprod.inl) (pullback.snd _ _ ≫ coprod.inr)) (by
      apply coprod.hom_ext
      · apply coprod.hom_ext <;> simp
      · simpa only [Category.assoc, coprod.inr_desc_assoc, extensionAction_obj_hom,
          coprod.inr_desc] using (pullback.condition (f := p.of.obj.hom) (g := q.of.obj.hom)))

/-- The first pullback projection of distributivity. -/
@[reassoc]
theorem extensionAddProductHom_fst {C : Category.{u, u} R} (S T : IsoCategory R)
    (p q : (exactStructure R).ExtensionFiber C) :
    extensionAddProductHom R S T p q ≫
      pullback.fst (S ⊙ₗ p).of.obj.hom (T ⊙ₗ q).of.obj.hom =
    coprod.desc (coprod.desc coprod.inl 0) (pullback.fst _ _ ≫ coprod.inr) :=
  pullback.lift_fst _ _ _

/-- The second pullback projection of distributivity. -/
@[reassoc]
theorem extensionAddProductHom_snd {C : Category.{u, u} R} (S T : IsoCategory R)
    (p q : (exactStructure R).ExtensionFiber C) :
    extensionAddProductHom R S T p q ≫
      pullback.snd (S ⊙ₗ p).of.obj.hom (T ⊙ₗ q).of.obj.hom =
    coprod.desc (coprod.desc 0 coprod.inl) (pullback.snd _ _ ≫ coprod.inr) :=
  pullback.lift_snd _ _ _

/-- Forget the two new summands to recover a point of the original pullback. -/
def extensionAddProductOld {C : Category.{u, u} R} (S T : IsoCategory R)
    (p q : (exactStructure R).ExtensionFiber C) :
    (extensionProductFiber R (S ⊙ₗ p) (T ⊙ₗ q)).of.obj.left ⟶
      (extensionProductFiber R p q).of.obj.left :=
  pullback.lift
    (pullback.fst _ _ ≫ coprod.desc 0 (𝟙 _))
    (pullback.snd _ _ ≫ coprod.desc 0 (𝟙 _)) (by
      simpa only [Category.assoc, coprod.desc_comp, zero_comp, Category.id_comp,
        extensionAction_obj_hom]
        using (pullback.condition (f := (S ⊙ₗ p).of.obj.hom)
          (g := (T ⊙ₗ q).of.obj.hom)))

/-- The old pullback coordinates are unchanged by distributivity. -/
@[reassoc (attr := simp)]
theorem extensionAddProductHom_old {C : Category.{u, u} R} (S T : IsoCategory R)
    (p q : (exactStructure R).ExtensionFiber C) :
    extensionAddProductHom R S T p q ≫ extensionAddProductOld R S T p q =
      coprod.desc 0 (𝟙 _) := by
  apply pullback.hom_ext
  all_goals apply coprod.hom_ext
  · apply coprod.hom_ext <;> simp [extensionAddProductHom, extensionAddProductOld]
  · simp [extensionAddProductHom, extensionAddProductOld]
  · apply coprod.hom_ext <;> simp [extensionAddProductHom, extensionAddProductOld]
  · simp [extensionAddProductHom, extensionAddProductOld]

/-- The canonical inverse extracts the two new summands and the old pullback. -/
def extensionAddProductInv {C : Category.{u, u} R} (S T : IsoCategory R)
    (p q : (exactStructure R).ExtensionFiber C) :
    (extensionProductFiber R (S ⊙ₗ p) (T ⊙ₗ q)).of.obj.left ⟶
      ((S ⊗ T) ⊙ₗ extensionProductFiber R p q).of.obj.left :=
  pullback.fst _ _ ≫ coprod.desc (𝟙 _) 0 ≫ coprod.inl ≫ coprod.inl +
  pullback.snd _ _ ≫ coprod.desc (𝟙 _) 0 ≫ coprod.inr ≫ coprod.inl +
  extensionAddProductOld R S T p q ≫ coprod.inr

/-- Adding two separate summands commutes with the actual pullback product. -/
def extensionAddProductMiddleIso {C : Category.{u, u} R} (S T : IsoCategory R)
    (p q : (exactStructure R).ExtensionFiber C) :
    ((S ⊗ T) ⊙ₗ extensionProductFiber R p q).of.obj.left ≅
      (extensionProductFiber R (S ⊙ₗ p) (T ⊙ₗ q)).of.obj.left where
  hom := extensionAddProductHom R S T p q
  inv := extensionAddProductInv R S T p q
  hom_inv_id := by
    change _ = 𝟙 ((S.of ⨿ T.of) ⨿ pullback p.of.obj.hom q.of.obj.hom)
    simp only [extensionAddProductInv, Preadditive.comp_add,
      extensionAddProductHom_old_assoc]
    apply coprod.hom_ext
    · apply coprod.hom_ext
      · simp only [extensionAddProductHom, extensionAction_obj_hom, coprod.desc_comp,
      Category.id_comp, zero_comp,
          limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app,
          colimit.ι_desc, BinaryCofan.mk_pt,
          BinaryCofan.mk_inl, Category.assoc, BinaryCofan.mk_inr, comp_zero, cospan_right,
          Preadditive.comp_add, add_zero]
        exact congrArg (fun f => coprod.inl ≫ f) (Category.comp_id _).symm
      · simp only [extensionAddProductHom, extensionAction_obj_hom, coprod.desc_comp,
      Category.id_comp, zero_comp,
          limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app,
          colimit.ι_desc, BinaryCofan.mk_pt,
          BinaryCofan.mk_inl, Category.assoc, BinaryCofan.mk_inr, comp_zero, cospan_right,
          Preadditive.comp_add, add_zero,
          zero_add]
        exact congrArg (fun f => coprod.inr ≫ f) (Category.comp_id _).symm
    · simp only [extensionAddProductHom, extensionAction_obj_hom, coprod.desc_comp,
    Category.id_comp, zero_comp,
          limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app,
          colimit.ι_desc, BinaryCofan.mk_pt,
          BinaryCofan.mk_inl, Category.assoc, BinaryCofan.mk_inr, comp_zero, cospan_right,
          Preadditive.comp_add, add_zero,
          zero_add]
      exact (Category.comp_id _).symm
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [extensionAddProductHom, extensionAddProductInv, extensionAddProductOld,
        Preadditive.add_comp,
        Category.assoc, pullback.lift_fst,
        coprod.inl_desc, coprod.inr_desc, pullback.lift_fst_assoc, comp_zero, add_zero]
      rw [← Preadditive.comp_add, coprod_decomposition]
      simp
    · simp only [extensionAddProductHom, extensionAddProductInv, extensionAddProductOld,
        Preadditive.add_comp,
        Category.assoc, pullback.lift_snd,
        coprod.inl_desc, coprod.inr_desc, pullback.lift_snd_assoc, comp_zero, zero_add]
      rw [← Preadditive.comp_add, coprod_decomposition]
      simp

/-- The distributivity isomorphism preserves the original fixed quotient. -/
def extensionAddProductIso {C : Category.{u, u} R} (S T : IsoCategory R)
    (p q : (exactStructure R).ExtensionFiber C) :
    (S ⊗ T) ⊙ₗ extensionProductFiber R p q ≅
      extensionProductFiber R (S ⊙ₗ p) (T ⊙ₗ q) :=
  Core.isoMk ((exactStructure R).extensionProperty C |>.isoMk
    (Over.isoMk (extensionAddProductMiddleIso R S T p q) (by
      change extensionAddProductHom R S T p q ≫
        (pullback.snd _ _ ≫ (T ⊙ₗ q).of.obj.hom) = _
      simp only [extensionProductFiber,
        CategoryTheory.ExactCategory.ExactStructure.extensionFiberProduct,
      CategoryTheory.ExactCategory.ExactStructure.extensionProductObj,
        prod_Hom, extensionAction_obj_hom, Over.mk_left, extensionAddProductHom,
        limit.lift_π_assoc, PullbackCone.mk_pt,
        cospan_right, PullbackCone.mk_π_app, coprod.desc_comp, zero_comp, colimit.ι_desc,
        BinaryCofan.mk_pt,
        BinaryCofan.mk_inl, Category.assoc, BinaryCofan.mk_inr, Over.mk_hom]
      congr 1
      apply coprod.hom_ext <;> simp)))

end ModuleCat.FiniteProjective
