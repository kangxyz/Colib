/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionArrows
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionMultiplication

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionProductCoordinates.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Section and retraction coordinates of the genuine pullback multiplication -/
@[expose] public section

open CategoryTheory.GroupCompletion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal extensionFiberDirectSumAction
open GroupCompletion ActionLocalization

/-- The first section coordinate is the original first section. -/
@[reassoc (attr := simp)]
theorem extensionProductHom_section_fst {C : Category.{u, u} R}
    {p p' q q' : ExtensionActionCategory R C} (f : p ⟶ p') (g : q ⟶ q') :
    extensionActionSection R (extensionProductHom R f g) ≫
      pullback.fst p'.obj.of.obj.hom q'.obj.of.obj.hom =
    pullback.fst p.obj.of.obj.hom q.obj.of.obj.hom ≫ extensionActionSection R f := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      change (coprod.inr ≫ (extensionProductRep R f g).map.iso.hom.hom.left) ≫ _ =
        _ ≫ (coprod.inr ≫ f.map.iso.hom.hom.left)
      simp only [extensionProductRep_map, extensionAddProductHom, extensionAction_obj_hom,
      Category.assoc,
        extensionFiberProduct_map_fst, limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left,
        PullbackCone.mk_π_app,
        coprod.desc_comp, zero_comp]
      exact coprod.inr_desc _ _

/-- The second section coordinate is the original second section. -/
@[reassoc (attr := simp)]
theorem extensionProductHom_section_snd {C : Category.{u, u} R}
    {p p' q q' : ExtensionActionCategory R C} (f : p ⟶ p') (g : q ⟶ q') :
    extensionActionSection R (extensionProductHom R f g) ≫
      pullback.snd p'.obj.of.obj.hom q'.obj.of.obj.hom =
    pullback.snd p.obj.of.obj.hom q.obj.of.obj.hom ≫ extensionActionSection R g := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      change (coprod.inr ≫ (extensionProductRep R f g).map.iso.hom.hom.left) ≫ _ =
        _ ≫ (coprod.inr ≫ g.map.iso.hom.hom.left)
      simp only [extensionProductRep_map, extensionAddProductHom, extensionAction_obj_hom,
      Category.assoc,
        extensionFiberProduct_map_snd, limit.lift_π_assoc, PullbackCone.mk_pt, cospan_right,
        PullbackCone.mk_π_app,
        coprod.desc_comp, zero_comp]
      exact coprod.inr_desc _ _

/-- Forgetting new summands after the inverse distributivity is the old projection. -/
@[reassoc (attr := simp)]
theorem extensionAddProductInv_old {C : Category.{u, u} R} (S T : IsoCategory R)
    (p q : (exactStructure R).ExtensionFiber C) :
    extensionAddProductInv R S T p q ≫ coprod.desc 0 (𝟙 _) =
      extensionAddProductOld R S T p q := by
  simp only [extensionAddProductInv, Preadditive.add_comp, Category.assoc,
    coprod.inl_desc, coprod.inr_desc, comp_zero, add_zero, zero_add, Category.comp_id]

/-- The first retraction coordinate is the original first retraction. -/
@[reassoc (attr := simp)]
theorem extensionProductHom_retraction_fst {C : Category.{u, u} R}
    {p p' q q' : ExtensionActionCategory R C} (f : p ⟶ p') (g : q ⟶ q') :
    extensionActionRetraction R (extensionProductHom R f g) ≫
      pullback.fst p.obj.of.obj.hom q.obj.of.obj.hom =
    pullback.fst p'.obj.of.obj.hom q'.obj.of.obj.hom ≫ extensionActionRetraction R f := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      change ((((exactStructure R).extensionFiberProduct C).map
          (Prod.mkHom (⟨f.map.iso.symm⟩ : p'.obj ⟶ f.denom ⊙ₗ p.obj)
            (⟨g.map.iso.symm⟩ : q'.obj ⟶ g.denom ⊙ₗ q.obj))).iso.hom.hom.left ≫
        extensionAddProductInv R f.denom g.denom p.obj q.obj) ≫ coprod.desc 0 (𝟙 _) ≫ _ =
        _ ≫ (f.map.iso.inv.hom.left ≫ coprod.desc 0 (𝟙 _))
      rw [Category.assoc, extensionAddProductInv_old_assoc]
      simp only [extensionAddProductOld, pullback.lift_fst]
      erw [extensionFiberProduct_map_fst_assoc]
      rfl

/-- The second retraction coordinate is the original second retraction. -/
@[reassoc (attr := simp)]
theorem extensionProductHom_retraction_snd {C : Category.{u, u} R}
    {p p' q q' : ExtensionActionCategory R C} (f : p ⟶ p') (g : q ⟶ q') :
    extensionActionRetraction R (extensionProductHom R f g) ≫
      pullback.snd p.obj.of.obj.hom q.obj.of.obj.hom =
    pullback.snd p'.obj.of.obj.hom q'.obj.of.obj.hom ≫ extensionActionRetraction R g := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      change ((((exactStructure R).extensionFiberProduct C).map
          (Prod.mkHom (⟨f.map.iso.symm⟩ : p'.obj ⟶ f.denom ⊙ₗ p.obj)
            (⟨g.map.iso.symm⟩ : q'.obj ⟶ g.denom ⊙ₗ q.obj))).iso.hom.hom.left ≫
        extensionAddProductInv R f.denom g.denom p.obj q.obj) ≫ coprod.desc 0 (𝟙 _) ≫ _ =
        _ ≫ (g.map.iso.inv.hom.left ≫ coprod.desc 0 (𝟙 _))
      rw [Category.assoc, extensionAddProductInv_old_assoc]
      simp only [extensionAddProductOld, pullback.lift_snd]
      erw [extensionFiberProduct_map_snd_assoc]
      rfl

end ModuleCat.FiniteProjective
