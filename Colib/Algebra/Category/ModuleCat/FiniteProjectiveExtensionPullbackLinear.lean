/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensions
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionPullbackLinearIso
public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionPullbackLinear.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Genuine direct-sum equivariance of extension pullback -/
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
attribute [local instance] pullbackLinearExists

/-- The pullback lineator is natural in the acting projective isomorphism. -/
theorem extensionPullbackAdd_naturality_left {X Y : Category.{u, u} R} (f : X ⟶ Y)
    {S T : IsoCategory R} (h : S ⟶ T) (p : (exactStructure R).ExtensionFiber Y) :
    h ⊵ₗ extensionPullbackFiber R f p ≫ (extensionPullbackAddIso R f T p).hom =
      (extensionPullbackAddIso R f S p).hom ≫
        ((exactStructure R).extensionFiberPullback f).map (h ⊵ₗ p) := by
  apply extensionFiber_hom_ext R
  change coprod.map h.iso.hom (𝟙 _) ≫ extensionPullbackAddHom R f T p =
    extensionPullbackAddHom R f S p ≫
      (((exactStructure R).extensionFiberPullback f).map (h ⊵ₗ p)).iso.hom.hom.left
  apply pullback.hom_ext
  · simp only [Category.assoc]
    erw [extensionPullbackAddHom_fst, extensionFiberPullback_map_fst]
    change coprod.map h.iso.hom (𝟙 _) ≫ coprod.map (𝟙 _) (pullback.fst p.of.obj.hom f) =
      (extensionPullbackAddHom R f S p ≫ pullback.fst (S ⊙ₗ p).of.obj.hom f) ≫
        coprod.map h.iso.hom (𝟙 _)
    erw [extensionPullbackAddHom_fst]
    apply coprod.hom_ext <;> simp
  · simp only [Category.assoc]
    erw [extensionPullbackAddHom_snd, extensionFiberPullback_map_snd,
      extensionPullbackAddHom_snd]
    apply coprod.hom_ext
    · simp only [coprod.map_desc, comp_zero, Category.id_comp,
        colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inl]
      exact (coprod.inl_desc _ _).symm
    · simp only [coprod.map_desc, comp_zero, Category.id_comp,
        colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inr]
      exact (coprod.inr_desc _ _).symm

/-- The pullback lineator is natural in the original extension isomorphism. -/
theorem extensionPullbackAdd_naturality_right {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (S : IsoCategory R) {p q : (exactStructure R).ExtensionFiber Y} (g : p ⟶ q) :
    S ⊴ₗ ((exactStructure R).extensionFiberPullback f).map g ≫
        (extensionPullbackAddIso R f S q).hom =
      (extensionPullbackAddIso R f S p).hom ≫
        ((exactStructure R).extensionFiberPullback f).map (S ⊴ₗ g) := by
  apply extensionFiber_hom_ext R
  change coprod.map (𝟙 S.of)
      (((exactStructure R).extensionFiberPullback f).map g).iso.hom.hom.left ≫
      extensionPullbackAddHom R f S q =
    extensionPullbackAddHom R f S p ≫
      (((exactStructure R).extensionFiberPullback f).map (S ⊴ₗ g)).iso.hom.hom.left
  apply pullback.hom_ext
  · simp only [Category.assoc]
    erw [extensionPullbackAddHom_fst, extensionFiberPullback_map_fst]
    change coprod.map (𝟙 S.of)
        (((exactStructure R).extensionFiberPullback f).map g).iso.hom.hom.left ≫
        coprod.map (𝟙 _) (pullback.fst q.of.obj.hom f) =
      (extensionPullbackAddHom R f S p ≫ pullback.fst (S ⊙ₗ p).of.obj.hom f) ≫
        coprod.map (𝟙 S.of) g.iso.hom.hom.left
    erw [extensionPullbackAddHom_fst]
    apply coprod.hom_ext <;> simp
  · simp only [Category.assoc]
    erw [extensionPullbackAddHom_snd, extensionFiberPullback_map_snd,
      extensionPullbackAddHom_snd]
    apply coprod.hom_ext
    · simp only [coprod.map_desc, comp_zero, extensionFiberPullback_map_snd,
        colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inl]
      exact (coprod.inl_desc _ _).symm
    · simp only [coprod.map_desc, comp_zero, extensionFiberPullback_map_snd,
        colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inr]
      exact (coprod.inr_desc _ _).symm

/-- The canonical pullback comparison respects the genuine direct-sum associator. -/
theorem extensionPullbackAdd_associativity {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (S T : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    (extensionPullbackAddIso R f (S ⊗ T) p).hom ≫
        ((exactStructure R).extensionFiberPullback f).map (αₗ S T p).hom =
      (αₗ S T (extensionPullbackFiber R f p)).hom ≫
        S ⊴ₗ (extensionPullbackAddIso R f T p).hom ≫
          (extensionPullbackAddIso R f S (T ⊙ₗ p)).hom := by
  apply extensionFiber_hom_ext R
  change extensionPullbackAddHom R f (S ⊗ T) p ≫
      (((exactStructure R).extensionFiberPullback f).map (αₗ S T p).hom).iso.hom.hom.left =
    (coprod.associator S.of T.of (pullback p.of.obj.hom f)).hom ≫
      coprod.map (𝟙 S.of) (extensionPullbackAddHom R f T p) ≫
        extensionPullbackAddHom R f S (T ⊙ₗ p)
  apply pullback.hom_ext
  · simp only [Category.assoc]
    erw [extensionFiberPullback_map_fst, extensionPullbackAddHom_fst]
    change (extensionPullbackAddHom R f (S ⊗ T) p ≫
        pullback.fst ((S ⊗ T) ⊙ₗ p).of.obj.hom f) ≫
        (coprod.associator S.of T.of p.of.obj.left).hom = _
    erw [extensionPullbackAddHom_fst]
    erw [coprod.map_map, Category.id_comp, extensionPullbackAddHom_fst]
    change coprod.map (𝟙 (S.of ⨿ T.of)) (pullback.fst p.of.obj.hom f) ≫
        (coprod.associator S.of T.of p.of.obj.left).hom =
      (coprod.associator S.of T.of (pullback p.of.obj.hom f)).hom ≫
        coprod.map (𝟙 S.of) (coprod.map (𝟙 T.of) (pullback.fst p.of.obj.hom f))
    simpa only [coprod.map_id_id] using
      coprod.associator_naturality (𝟙 S.of) (𝟙 T.of) (pullback.fst p.of.obj.hom f)
  · simp only [Category.assoc]
    erw [extensionFiberPullback_map_snd, extensionPullbackAddHom_snd,
      extensionPullbackAddHom_snd]
    erw [coprod.map_desc, comp_zero, extensionPullbackAddHom_snd]
    change coprod.desc (0 : (S.of ⨿ T.of) ⟶ X) (pullback.snd p.of.obj.hom f) =
      (coprod.associator S.of T.of (pullback p.of.obj.hom f)).hom ≫
        coprod.desc (0 : S.of ⟶ X) (coprod.desc (0 : T.of ⟶ X) (pullback.snd p.of.obj.hom f))
    apply coprod.hom_ext
    · apply coprod.hom_ext <;>
        simp [coprod.associator_hom]
    · simp [coprod.associator_hom]

/-- The canonical pullback comparison respects the genuine direct-sum unit. -/
theorem extensionPullbackAdd_unitality {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (p : (exactStructure R).ExtensionFiber Y) :
    (λₗ[IsoCategory R] (extensionPullbackFiber R f p)).hom =
      (extensionPullbackAddIso R f (𝟙_ (IsoCategory R)) p).hom ≫
        ((exactStructure R).extensionFiberPullback f).map (λₗ[IsoCategory R] p).hom := by
  apply extensionFiber_hom_ext R
  change (coprod.leftUnitor (pullback p.of.obj.hom f)).hom =
    extensionPullbackAddHom R f (𝟙_ (IsoCategory R)) p ≫
      (((exactStructure R).extensionFiberPullback f).map
        (λₗ[IsoCategory R] p).hom).iso.hom.hom.left
  apply pullback.hom_ext
  · simp only [Category.assoc]
    erw [extensionFiberPullback_map_fst]
    change _ = (extensionPullbackAddHom R f (𝟙_ (IsoCategory R)) p ≫
        pullback.fst ((𝟙_ (IsoCategory R)) ⊙ₗ p).of.obj.hom f) ≫
        (coprod.leftUnitor p.of.obj.left).hom
    erw [extensionPullbackAddHom_fst]
    apply coprod.hom_ext
    · exact initialIsInitial.hom_ext _ _
    · with_unfolding_all
        simp only [coprod.leftUnitor_hom, MonoOver.initialTo_b_eq_zero, coprod.desc_comp,
          zero_comp, Category.id_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inr,
          coprod.map_desc, comp_zero, Category.comp_id]
      exact (coprod.inr_desc _ _).symm
  · simp only [Category.assoc]
    erw [extensionFiberPullback_map_snd, extensionPullbackAddHom_snd]
    apply coprod.hom_ext
    · exact initialIsInitial.hom_ext _ _
    · with_unfolding_all
        simp only [coprod.leftUnitor_hom, MonoOver.initialTo_b_eq_zero, coprod.desc_comp,
          zero_comp, Category.id_comp, colimit.ι_desc, BinaryCofan.mk_pt, BinaryCofan.mk_inr]
      exact (coprod.inr_desc _ _).symm

/-- The original extension pullback has its actual coherent direct-sum lineator. -/
@[instance_reducible]
def extensionFiberPullbackLinear {X Y : Category.{u, u} R} (f : X ⟶ Y) :
    ((exactStructure R).extensionFiberPullback f).LaxLeftLinear (IsoCategory R) where
  μₗ S p := (extensionPullbackAddIso R f S p).hom
  μₗ_naturality_left h p := extensionPullbackAdd_naturality_left R f h p
  μₗ_naturality_right S _ _ g := extensionPullbackAdd_naturality_right R f S g
  μₗ_associativity S T p := extensionPullbackAdd_associativity R f S T p
  μₗ_unitality p := extensionPullbackAdd_unitality R f p

end ModuleCat.FiniteProjective
