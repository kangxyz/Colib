/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionAction
public import Colib.CategoryTheory.ExactCategory.ExtensionBaseChange

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionPullbackLinearIso.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Direct sums commute with the original extension pullback -/
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

local instance pullbackExtensionExists {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (p : (exactStructure R).ExtensionOver Y) : HasPullback p.obj.hom f :=
  (exactStructure R).deflation.hasPullback f p.property

attribute [local simp] extensionAction_obj_hom

/-- Infer the original translated pullback after normalizing its quotient arrow. -/
local instance pullbackExtensionSumExists {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    HasPullback (coprod.desc (0 : S.of ⟶ Y) p.of.obj.hom) f :=
  pullbackExtensionExists R f (S ⊙ₗ p).of

/-- The genuine pullback fiber object, using the existing exact-category functor. -/
abbrev extensionPullbackFiber {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (p : (exactStructure R).ExtensionFiber Y) : (exactStructure R).ExtensionFiber X :=
  ((exactStructure R).extensionFiberPullback f).obj p

/-- The canonical comparison retains the new summand and the old pullback coordinates. -/
def extensionPullbackAddHom {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    (S ⊙ₗ extensionPullbackFiber R f p).of.obj.left ⟶
      (extensionPullbackFiber R f (S ⊙ₗ p)).of.obj.left :=
  pullback.lift
    (coprod.map (𝟙 S.of) (pullback.fst p.of.obj.hom f))
    (coprod.desc 0 (pullback.snd p.of.obj.hom f)) (by
      apply coprod.hom_ext
      · simp
      · simpa using (pullback.condition (f := p.of.obj.hom) (g := f)))

/-- The first projection is the direct sum of the old pullback projection. -/
@[reassoc (attr := simp)]
theorem extensionPullbackAddHom_fst {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    extensionPullbackAddHom R f S p ≫
      pullback.fst (coprod.desc (0 : S.of ⟶ Y) p.of.obj.hom) f =
      coprod.map (𝟙 S.of) (pullback.fst p.of.obj.hom f) :=
  pullback.lift_fst _ _ _

/-- The second projection kills the added summand and retains the old quotient map. -/
@[reassoc (attr := simp)]
theorem extensionPullbackAddHom_snd {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    extensionPullbackAddHom R f S p ≫
      pullback.snd (coprod.desc (0 : S.of ⟶ Y) p.of.obj.hom) f =
      coprod.desc 0 (pullback.snd p.of.obj.hom f) :=
  pullback.lift_snd _ _ _

/-- Forget the new summand and recover the original pullback. -/
def extensionPullbackAddOld {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    (extensionPullbackFiber R f (S ⊙ₗ p)).of.obj.left ⟶
      (extensionPullbackFiber R f p).of.obj.left :=
  pullback.lift
    (pullback.fst _ _ ≫ coprod.desc 0 (𝟙 _)) (pullback.snd _ _) (by
      change (pullback.fst (S ⊙ₗ p).of.obj.hom f ≫
        coprod.desc 0 (𝟙 p.of.obj.left)) ≫ p.of.obj.hom =
          pullback.snd (S ⊙ₗ p).of.obj.hom f ≫ f
      rw [Category.assoc, coprod.desc_comp, zero_comp, Category.id_comp]
      exact pullback.condition)

/-- The comparison followed by forgetting the new summand is the old projection. -/
@[reassoc (attr := simp)]
theorem extensionPullbackAddHom_old {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    extensionPullbackAddHom R f S p ≫ extensionPullbackAddOld R f S p =
      coprod.desc 0 (𝟙 _) := by
  apply pullback.hom_ext <;> apply coprod.hom_ext <;>
    simp [extensionPullbackAddHom, extensionPullbackAddOld]

/-- The inverse separates the new summand from the old pullback. -/
def extensionPullbackAddInv {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    (extensionPullbackFiber R f (S ⊙ₗ p)).of.obj.left ⟶
      (S ⊙ₗ extensionPullbackFiber R f p).of.obj.left :=
  pullback.fst _ _ ≫ coprod.desc (𝟙 _) 0 ≫ coprod.inl +
    extensionPullbackAddOld R f S p ≫ coprod.inr

private theorem pullbackAdd_coprod_decomposition (A B : Category.{u, u} R) :
    coprod.desc (𝟙 A) (0 : B ⟶ A) ≫ coprod.inl +
      coprod.desc (0 : A ⟶ B) (𝟙 B) ≫ coprod.inr = 𝟙 (A ⨿ B) := by
  apply coprod.hom_ext <;> simp [Preadditive.comp_add]

/-- Direct sum preserves the actual pullback middle term. -/
def extensionPullbackAddMiddleIso {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    (S ⊙ₗ extensionPullbackFiber R f p).of.obj.left ≅
      (extensionPullbackFiber R f (S ⊙ₗ p)).of.obj.left where
  hom := extensionPullbackAddHom R f S p
  inv := extensionPullbackAddInv R f S p
  hom_inv_id := by
    change _ = 𝟙 (S.of ⨿ pullback p.of.obj.hom f)
    simp only [extensionPullbackAddInv, Preadditive.comp_add,
      extensionPullbackAddHom_old_assoc]
    apply coprod.hom_ext
    · calc
        _ = (coprod.inl : S.of ⟶ S.of ⨿ pullback p.of.obj.hom f) := by
          simp only [extensionPullbackAddHom, Preadditive.comp_add, pullback.lift_fst_assoc,
            coprod.inl_desc, coprod.map_desc, coprod.desc_comp, Category.id_comp,
            zero_comp, comp_zero, add_zero]
          rfl
        _ = _ := (Category.comp_id _).symm
    · calc
        _ = (coprod.inr : pullback p.of.obj.hom f ⟶ S.of ⨿ pullback p.of.obj.hom f) := by
          simp only [extensionPullbackAddHom, Preadditive.comp_add, pullback.lift_fst_assoc,
            coprod.inr_desc, coprod.map_desc, coprod.desc_comp, Category.id_comp,
            zero_comp, comp_zero, zero_add]
          rfl
        _ = _ := (Category.comp_id _).symm
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [extensionPullbackAddHom, extensionPullbackAddInv,
        Preadditive.add_comp, Category.assoc, pullback.lift_fst,
        coprod.inl_map, coprod.inr_map,
        Category.id_comp, extensionPullbackAddOld]
      erw [pullback.lift_fst_assoc]
      erw [Category.assoc, ← Preadditive.comp_add, pullbackAdd_coprod_decomposition]
      simp
    · have hz : (coprod.desc (0 : S.of ⟶ X) (0 : p.of.obj.left ⟶ X)) = 0 := by
        apply coprod.hom_ext <;> simp
      simp [extensionPullbackAddHom, extensionPullbackAddInv,
        extensionPullbackAddOld, Preadditive.add_comp, hz]

/-- The canonical middle-term isomorphism is an isomorphism over the original quotient. -/
def extensionPullbackAddIso {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    S ⊙ₗ extensionPullbackFiber R f p ≅ extensionPullbackFiber R f (S ⊙ₗ p) :=
  Core.isoMk ((exactStructure R).extensionProperty X |>.isoMk
    (Over.isoMk (extensionPullbackAddMiddleIso R f S p) (by
      exact extensionPullbackAddHom_snd R f S p)))

attribute [-simp] extensionAction_obj_hom

end ModuleCat.FiniteProjective
