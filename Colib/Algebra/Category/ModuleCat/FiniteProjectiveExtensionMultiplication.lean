/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensions
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionProductAction
public import Colib.CategoryTheory.GroupCompletion.Monoidal

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionMultiplication.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Pullback multiplication on the fixed-quotient extension action category -/
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
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
attribute [local instance] directSumMonoidal directSumSymmetric extensionFiberDirectSumAction
open GroupCompletion ActionLocalization

/-- Multiply translated extension maps using the direct sum of their translating
objects and the actual pullback distributivity isomorphism. -/
def extensionProductRep {C : Category.{u, u} R}
    {p p' q q' : (exactStructure R).ExtensionFiber C}
    (f : HomRep (C := IsoCategory R) p p') (g : HomRep (C := IsoCategory R) q q') :
    HomRep (C := IsoCategory R) (extensionProductFiber R p q) (extensionProductFiber R p' q') :=
  ⟨f.denom ⊗ g.denom, (extensionAddProductIso R f.denom g.denom p q).hom ≫
    ((exactStructure R).extensionFiberProduct C).map (Prod.mkHom f.map g.map)⟩

/-- The underlying middle-term map of a product representative. -/
@[simp]
theorem extensionProductRep_map {C : Category.{u, u} R}
    {p p' q q' : (exactStructure R).ExtensionFiber C}
    (f : HomRep (C := IsoCategory R) p p') (g : HomRep (C := IsoCategory R) q q') :
    (extensionProductRep R f g).map.iso.hom.hom.left =
      extensionAddProductHom R f.denom g.denom p q ≫
        (((exactStructure R).extensionFiberProduct C).map (Prod.mkHom f.map
        g.map)).iso.hom.hom.left :=
  rfl

/-- Composition of translated extensions on their middle terms. -/
@[simp]
theorem extensionRep_comp_map {C : Category.{u, u} R}
    {p q r : (exactStructure R).ExtensionFiber C}
    (f : HomRep (C := IsoCategory R) p q) (g : HomRep (C := IsoCategory R) q r) :
    (f.comp g).map.iso.hom.hom.left =
      (coprod.associator g.denom.of f.denom.of p.of.obj.left).hom ≫
        coprod.map (𝟙 _) f.map.iso.hom.hom.left ≫ g.map.iso.hom.hom.left := rfl

/-- Both changes of translating object induce the same change in the product. -/
theorem extensionProductRep_rel {C : Category.{u, u} R}
    {p p' q q' : (exactStructure R).ExtensionFiber C}
    {f f' : HomRep (C := IsoCategory R) p p'}
    {g g' : HomRep (C := IsoCategory R) q q'}
    (hf : HomRep.Rel f f') (hg : HomRep.Rel g g') :
    HomRep.Rel (extensionProductRep R f g) (extensionProductRep R f' g') := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨d, hd⟩ := hg
  have he' := congrArg (fun a => a.iso.hom.hom.left) he
  have hd' := congrArg (fun a => a.iso.hom.hom.left) hd
  change coprod.map e.hom.iso.hom (𝟙 _) ≫ f'.map.iso.hom.hom.left =
    f.map.iso.hom.hom.left at he'
  change coprod.map d.hom.iso.hom (𝟙 _) ≫ g'.map.iso.hom.hom.left =
    g.map.iso.hom.hom.left at hd'
  refine ⟨e ⊗ᵢ d, ?_⟩
  apply extensionFiber_hom_ext R
  change coprod.map (coprod.map e.hom.iso.hom d.hom.iso.hom) (𝟙 _) ≫
      (extensionAddProductHom R f'.denom g'.denom p q ≫ _) =
    extensionAddProductHom R f.denom g.denom p q ≫ _
  apply pullback.hom_ext
  · simp only [Category.assoc, extensionFiberProduct_map_fst]
    change _ = extensionAddProductHom R f.denom g.denom p q ≫
      pullback.fst _ _ ≫ f.map.iso.hom.hom.left
    rw [← he']
    simp only [extensionAddProductHom, extensionAction_obj_hom, limit.lift_π_assoc,
    PullbackCone.mk_pt,
      cospan_left, PullbackCone.mk_π_app, coprod.desc_comp, zero_comp, Category.assoc,
      coprod.map_desc, comp_zero,
      Category.id_comp, coprod.inl_map_assoc, coprod.inr_map_assoc]
    rfl
  · simp only [Category.assoc, extensionFiberProduct_map_snd]
    change _ = extensionAddProductHom R f.denom g.denom p q ≫
      pullback.snd _ _ ≫ g.map.iso.hom.hom.left
    rw [← hd']
    simp only [extensionAddProductHom, extensionAction_obj_hom, limit.lift_π_assoc,
    PullbackCone.mk_pt,
      cospan_right, PullbackCone.mk_π_app, coprod.desc_comp, zero_comp, Category.assoc,
      coprod.map_desc, comp_zero,
      Category.id_comp, coprod.inl_map_assoc, coprod.inr_map_assoc]
    rfl

/-- Composition is respected with the genuine middle-four direct-sum interchange. -/
theorem extensionProductRep_comp_rel {C : Category.{u, u} R}
    {p p' p'' q q' q'' : (exactStructure R).ExtensionFiber C}
    (f : HomRep (C := IsoCategory R) p p') (g : HomRep (C := IsoCategory R) p' p'')
    (f' : HomRep (C := IsoCategory R) q q') (g' : HomRep (C := IsoCategory R) q' q'') :
    HomRep.Rel ((extensionProductRep R f f').comp (extensionProductRep R g g'))
      (extensionProductRep R (f.comp g) (f'.comp g')) := by
  refine ⟨Core.isoMk ⟨tensorμ g.denom.of g'.denom.of f.denom.of f'.denom.of,
    tensorδ g.denom.of g'.denom.of f.denom.of f'.denom.of,
    tensorμ_tensorδ _ _ _ _, tensorδ_tensorμ _ _ _ _⟩, ?_⟩
  apply extensionFiber_hom_ext R
  change coprod.map (tensorμ g.denom.of g'.denom.of f.denom.of f'.denom.of) (𝟙 _) ≫
      (extensionAddProductHom R (g.denom ⊗ f.denom) (g'.denom ⊗ f'.denom) p q ≫
        (((exactStructure R).extensionFiberProduct C).map
          (Prod.mkHom (f.comp g).map (f'.comp g').map)).iso.hom.hom.left) =
    (coprod.associator _ _ _).hom ≫
      coprod.map (𝟙 _) ((extensionProductRep R f f').map.iso.hom.hom.left) ≫
        (extensionProductRep R g g').map.iso.hom.hom.left
  apply pullback.hom_ext
  · simp only [extensionProductRep_map, Category.assoc, extensionFiberProduct_map_fst,
      extensionRep_comp_map]
    erw [extensionAddProductHom_fst_assoc R (g.denom ⊗ f.denom) (g'.denom ⊗ f'.denom) p q]
    simp only [monoidalOfHasFiniteCoproducts.tensorObj, tensorμ,
    monoidalOfHasFiniteCoproducts.associator_hom,
      monoidalOfHasFiniteCoproducts.associator_inv, monoidalOfHasFiniteCoproducts.whiskerLeft,
      symmetricOfHasFiniteCoproducts_braiding, coprod.braiding_hom,
      monoidalOfHasFiniteCoproducts.whiskerRight,
      coprod.map_desc, Category.id_comp, coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt,
      BinaryCofan.mk_inl,
      Category.assoc, BinaryCofan.mk_inr, coprod.desc_comp_inl_comp_inr, coprod.inr_map,
      coprod.inl_map,
      coprod.associator_hom, coprod.inl_map_assoc, coprod.inr_map_assoc, zero_comp, comp_zero,
      extensionAddProductHom,
      extensionAction_obj_hom, limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left,
      PullbackCone.mk_π_app,
      extensionFiberProduct_map_fst_assoc]
    with_unfolding_all simp only [coprod.inl_desc, coprod.inr_desc]
    rfl
  · simp only [extensionProductRep_map, Category.assoc, extensionFiberProduct_map_snd,
      extensionRep_comp_map]
    erw [extensionAddProductHom_snd_assoc R (g.denom ⊗ f.denom) (g'.denom ⊗ f'.denom) p q]
    simp only [monoidalOfHasFiniteCoproducts.tensorObj, tensorμ,
    monoidalOfHasFiniteCoproducts.associator_hom,
      monoidalOfHasFiniteCoproducts.associator_inv, monoidalOfHasFiniteCoproducts.whiskerLeft,
      symmetricOfHasFiniteCoproducts_braiding, coprod.braiding_hom,
      monoidalOfHasFiniteCoproducts.whiskerRight,
      coprod.map_desc, Category.id_comp, coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt,
      BinaryCofan.mk_inl,
      Category.assoc, BinaryCofan.mk_inr, coprod.desc_comp_inl_comp_inr, coprod.inr_map,
      coprod.inl_map,
      coprod.associator_hom, coprod.inl_map_assoc, coprod.inr_map_assoc, zero_comp, comp_zero,
      extensionAddProductHom,
      extensionAction_obj_hom, limit.lift_π_assoc, PullbackCone.mk_pt, cospan_right,
      PullbackCone.mk_π_app,
      extensionFiberProduct_map_snd_assoc]
    with_unfolding_all simp only [coprod.inl_desc, coprod.inr_desc]
    rfl

/-- The product representative of identity arrows is the identity after the
canonical isomorphism between two zero summands and one. -/
theorem extensionProductRep_id_rel {C : Category.{u, u} R}
    (p q : (exactStructure R).ExtensionFiber C) :
    HomRep.Rel (extensionProductRep R (HomRep.id p) (HomRep.id q))
      (HomRep.id (extensionProductFiber R p q)) := by
  refine ⟨λ_ (𝟙_ (IsoCategory R)), ?_⟩
  apply extensionFiber_hom_ext R
  change coprod.map (coprod.leftUnitor (𝟙_ (Category R))).hom (𝟙 _) ≫
      (coprod.leftUnitor (extensionProductFiber R p q).of.obj.left).hom =
    extensionAddProductHom R (𝟙_ (IsoCategory R)) (𝟙_ (IsoCategory R)) p q ≫
      (((exactStructure R).extensionFiberProduct C).map
        (Prod.mkHom (HomRep.id p).map (HomRep.id q).map)).iso.hom.hom.left
  apply pullback.hom_ext
  · simp only [Category.assoc, extensionFiberProduct_map_fst]
    change _ = extensionAddProductHom R (𝟙_ (IsoCategory R)) (𝟙_ (IsoCategory R)) p q ≫
      pullback.fst _ _ ≫ (coprod.leftUnitor p.of.obj.left).hom
    simp only [coprod.leftUnitor_hom, MonoOver.initialTo_b_eq_zero, coprod.desc_comp, zero_comp,
    Category.id_comp,
      coprod.map_desc, comp_zero, extensionAddProductHom, extensionAction_obj_hom,
      limit.lift_π_assoc, PullbackCone.mk_pt,
      cospan_left, PullbackCone.mk_π_app, Category.assoc]
    with_unfolding_all simp only [coprod.inl_desc, coprod.inr_desc, Category.comp_id]
    congr 1
    apply coprod.hom_ext
    all_goals exact initialIsInitial.hom_ext _ _
  · simp only [Category.assoc, extensionFiberProduct_map_snd]
    change _ = extensionAddProductHom R (𝟙_ (IsoCategory R)) (𝟙_ (IsoCategory R)) p q ≫
      pullback.snd _ _ ≫ (coprod.leftUnitor q.of.obj.left).hom
    simp only [coprod.leftUnitor_hom, MonoOver.initialTo_b_eq_zero, coprod.desc_comp, zero_comp,
    Category.id_comp,
      coprod.map_desc, comp_zero, extensionAddProductHom, extensionAction_obj_hom,
      limit.lift_π_assoc, PullbackCone.mk_pt,
      cospan_right, PullbackCone.mk_π_app, Category.assoc]
    with_unfolding_all simp only [coprod.inl_desc, coprod.inr_desc, Category.comp_id]
    congr 1
    apply coprod.hom_ext
    all_goals exact initialIsInitial.hom_ext _ _

/-- The multiplication on action-category arrows is well-defined on both
isomorphism classes of translating objects. -/
def extensionProductHom {C : Category.{u, u} R}
    {p p' q q' : ExtensionActionCategory R C} (f : p ⟶ p') (g : q ⟶ q') :
    (⟨extensionProductFiber R p.obj q.obj⟩ : ExtensionActionCategory R C) ⟶
      ⟨extensionProductFiber R p'.obj q'.obj⟩ :=
  Quotient.map₂ (extensionProductRep R)
    (fun _ _ hf _ _ hg => extensionProductRep_rel R hf hg) f g

/-- Multiplication of action-category arrows respects composition. -/
theorem extensionProductHom_comp {C : Category.{u, u} R}
    {p p' p'' q q' q'' : ExtensionActionCategory R C}
    (f : p ⟶ p') (g : p' ⟶ p'') (f' : q ⟶ q') (g' : q' ⟶ q'') :
    extensionProductHom R (f ≫ g) (f' ≫ g') =
      extensionProductHom R f f' ≫ extensionProductHom R g g' := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      induction f' using Quotient.inductionOn with
      | _ f' =>
        induction g' using Quotient.inductionOn with
        | _ g' =>
          exact Quotient.sound (HomRep.rel_symm (extensionProductRep_comp_rel R f g f' g'))

/-- The product of identity arrows is the identity. -/
@[simp]
theorem extensionProductHom_id {C : Category.{u, u} R}
    (p q : ExtensionActionCategory R C) :
    extensionProductHom R (𝟙 p) (𝟙 q) = 𝟙 (⟨extensionProductFiber R p.obj q.obj⟩ :
      ExtensionActionCategory R C) := Quotient.sound (extensionProductRep_id_rel R p.obj q.obj)

/-- The actual pullback multiplication functor on the fixed-quotient action
category, with the genuine sum-of-kernels multiplication on objects. -/
def extensionActionMultiplication (C : Category.{u, u} R) :
    ExtensionActionCategory R C × ExtensionActionCategory R C ⥤ ExtensionActionCategory R C where
  obj p := ⟨extensionProductFiber R p.1.obj p.2.obj⟩
  map f := extensionProductHom R f.1 f.2
  map_id p := extensionProductHom_id R p.1 p.2
  map_comp f g := extensionProductHom_comp R f.1 g.1 f.2 g.2

end ModuleCat.FiniteProjective
