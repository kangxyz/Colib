/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionDiagonal

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionUnit.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Actual unit isomorphisms for fixed-quotient extension multiplication -/
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

/-- The identity deflation is the unit of fixed-quotient pullback multiplication. -/
def extensionActionUnit (C : Category.{u, u} R) : ExtensionActionCategory R C :=
  ⟨(exactStructure R).extensionUnit C⟩

local instance unitHasPullbackLeft {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) : HasPullback (𝟙 C) p.of.obj.hom :=
  (exactStructure R).deflation.hasPullback p.of.obj.hom ((exactStructure R).deflation_id C)

local instance unitHasPullbackRight {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) : HasPullback p.of.obj.hom (𝟙 C) :=
  (exactStructure R).deflation.hasPullback (𝟙 C) p.of.property

/-- Pulling back an extension against the identity on the left recovers its middle term. -/
def extensionLeftUnitMiddleIso {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    (extensionProductFiber R ((exactStructure R).extensionUnit C) p).of.obj.left ≅
      p.of.obj.left where
  hom := pullback.snd _ _
  inv := pullback.lift p.of.obj.hom (𝟙 _) (by simp
    [CategoryTheory.ExactCategory.ExactStructure.extensionUnit])
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      simpa [CategoryTheory.ExactCategory.ExactStructure.extensionUnit] using
        (pullback.condition (f := (𝟙 C)) (g := p.of.obj.hom)).symm
    · simp
  inv_hom_id := by simp

/-- Pulling back against the identity on the right recovers the original middle term. -/
def extensionRightUnitMiddleIso {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    (extensionProductFiber R p ((exactStructure R).extensionUnit C)).of.obj.left ≅
      p.of.obj.left where
  hom := pullback.fst _ _
  inv := pullback.lift (𝟙 _) p.of.obj.hom (by simp
    [CategoryTheory.ExactCategory.ExactStructure.extensionUnit])
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      simpa [CategoryTheory.ExactCategory.ExactStructure.extensionUnit] using
        (pullback.condition (f := p.of.obj.hom) (g := (𝟙 C)))
  inv_hom_id := by simp

/-- First coordinate of the inverse left unit. -/
@[reassoc (attr := simp)]
theorem extensionLeftUnitMiddleIso_inv_fst {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    (extensionLeftUnitMiddleIso R p).inv ≫
      pullback.fst ((exactStructure R).extensionUnit C).of.obj.hom p.of.obj.hom =
        p.of.obj.hom := pullback.lift_fst _ _ _

/-- Second coordinate of the inverse left unit. -/
@[reassoc (attr := simp)]
theorem extensionLeftUnitMiddleIso_inv_snd {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    (extensionLeftUnitMiddleIso R p).inv ≫
      pullback.snd ((exactStructure R).extensionUnit C).of.obj.hom p.of.obj.hom =
        𝟙 _ := pullback.lift_snd _ _ _

/-- First coordinate of the inverse right unit. -/
@[reassoc (attr := simp)]
theorem extensionRightUnitMiddleIso_inv_fst {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    (extensionRightUnitMiddleIso R p).inv ≫
      pullback.fst p.of.obj.hom ((exactStructure R).extensionUnit C).of.obj.hom =
        𝟙 _ := pullback.lift_fst _ _ _

/-- Second coordinate of the inverse right unit. -/
@[reassoc (attr := simp)]
theorem extensionRightUnitMiddleIso_inv_snd {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    (extensionRightUnitMiddleIso R p).inv ≫
      pullback.snd p.of.obj.hom ((exactStructure R).extensionUnit C).of.obj.hom =
        p.of.obj.hom := pullback.lift_snd _ _ _

/-- The left unit comparison is an isomorphism over the same fixed quotient. -/
def extensionLeftUnitIso {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    extensionProductFiber R ((exactStructure R).extensionUnit C) p ≅ p :=
  Core.isoMk ((exactStructure R).extensionProperty C |>.isoMk
    (Over.isoMk (extensionLeftUnitMiddleIso R p) rfl))

/-- The right unit comparison is also an isomorphism over the fixed quotient. -/
def extensionRightUnitIso {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) :
    extensionProductFiber R p ((exactStructure R).extensionUnit C) ≅ p :=
  Core.isoMk ((exactStructure R).extensionProperty C |>.isoMk
    (Over.isoMk (extensionRightUnitMiddleIso R p) pullback.condition))

/-- The left unit objectwise isomorphism in the actual action category. -/
def extensionActionLeftUnitIso {C : Category.{u, u} R} (p : ExtensionActionCategory R C) :
    (extensionActionMultiplication R C).obj (extensionActionUnit R C, p) ≅ p :=
  (ofFunctor (C := IsoCategory R)).mapIso (extensionLeftUnitIso R p.obj)

/-- The right unit objectwise isomorphism in the actual action category. -/
def extensionActionRightUnitIso {C : Category.{u, u} R} (p : ExtensionActionCategory R C) :
    (extensionActionMultiplication R C).obj (p, extensionActionUnit R C) ≅ p :=
  (ofFunctor (C := IsoCategory R)).mapIso (extensionRightUnitIso R p.obj)

/-- Naturality of the left unit includes all stabilized extension arrows. -/
def extensionActionLeftUnit (C : Category.{u, u} R) :
    (((Functor.const (ExtensionActionCategory R C)).obj (extensionActionUnit R C)).prod'
      (𝟭 (ExtensionActionCategory R C))) ⋙ extensionActionMultiplication R C ≅
        𝟭 (ExtensionActionCategory R C) :=
  NatIso.ofComponents (extensionActionLeftUnitIso R) (by
    intro p q f
    change extensionProductHom R (𝟙 (extensionActionUnit R C)) f ≫
        GroupCompletion.ActionLocalization.ofHom (extensionLeftUnitIso R q.obj).hom =
      GroupCompletion.ActionLocalization.ofHom (extensionLeftUnitIso R p.obj).hom ≫ f
    apply extensionAction_hom_ext R
    · simp only [extensionActionSection_comp, extensionActionSection_ofHom]
      exact extensionProductHom_section_snd R (𝟙 (extensionActionUnit R C)) f
    · simp only [extensionActionRetraction_comp, extensionActionRetraction_ofHom]
      change (extensionLeftUnitMiddleIso R q.obj).inv ≫
          extensionActionRetraction R (extensionProductHom R (𝟙 (extensionActionUnit R C)) f) =
        extensionActionRetraction R f ≫ (extensionLeftUnitMiddleIso R p.obj).inv
      apply pullback.hom_ext
      · simp only [Category.assoc, extensionProductHom_retraction_fst,
          extensionActionRetraction_id]
        erw [extensionLeftUnitMiddleIso_inv_fst_assoc, extensionLeftUnitMiddleIso_inv_fst]
        simp only [extensionActionRetraction_w]
        exact Category.comp_id _
      · simp only [Category.assoc, extensionProductHom_retraction_snd]
        erw [extensionLeftUnitMiddleIso_inv_snd_assoc, extensionLeftUnitMiddleIso_inv_snd]
        simp)

/-- Naturality of the right unit includes all stabilized extension arrows. -/
def extensionActionRightUnit (C : Category.{u, u} R) :
    ((𝟭 (ExtensionActionCategory R C)).prod'
      ((Functor.const (ExtensionActionCategory R C)).obj (extensionActionUnit R C))) ⋙
        extensionActionMultiplication R C ≅ 𝟭 (ExtensionActionCategory R C) :=
  NatIso.ofComponents (extensionActionRightUnitIso R) (by
    intro p q f
    change extensionProductHom R f (𝟙 (extensionActionUnit R C)) ≫
        GroupCompletion.ActionLocalization.ofHom (extensionRightUnitIso R q.obj).hom =
      GroupCompletion.ActionLocalization.ofHom (extensionRightUnitIso R p.obj).hom ≫ f
    apply extensionAction_hom_ext R
    · simp only [extensionActionSection_comp, extensionActionSection_ofHom]
      exact extensionProductHom_section_fst R f (𝟙 (extensionActionUnit R C))
    · simp only [extensionActionRetraction_comp, extensionActionRetraction_ofHom]
      change (extensionRightUnitMiddleIso R q.obj).inv ≫
          extensionActionRetraction R (extensionProductHom R f (𝟙 (extensionActionUnit R C))) =
        extensionActionRetraction R f ≫ (extensionRightUnitMiddleIso R p.obj).inv
      apply pullback.hom_ext
      · simp only [Category.assoc, extensionProductHom_retraction_fst]
        erw [extensionRightUnitMiddleIso_inv_fst_assoc, extensionRightUnitMiddleIso_inv_fst]
        simp
      · simp only [Category.assoc, extensionProductHom_retraction_snd,
          extensionActionRetraction_id]
        erw [extensionRightUnitMiddleIso_inv_snd_assoc, extensionRightUnitMiddleIso_inv_snd]
        simp only [extensionActionRetraction_w]
        exact Category.comp_id _)

/-- Both unit components at the identity extension are the same actual arrow. -/
theorem extensionAction_unit_coherence (C : Category.{u, u} R) :
    (extensionActionLeftUnit R C).hom.app (extensionActionUnit R C) =
      (extensionActionRightUnit R C).hom.app (extensionActionUnit R C) := by
  apply congrArg (GroupCompletion.ActionLocalization.ofHom (C := IsoCategory R))
  apply extensionFiber_hom_ext R
  change pullback.snd (𝟙 C) (𝟙 C) = pullback.fst (𝟙 C) (𝟙 C)
  simpa using (pullback.condition (f := (𝟙 C)) (g := (𝟙 C))).symm

/-- The genuine diagonal at the unit is precisely the inverse left unit component. -/
theorem extensionAction_diagonal_unit (C : Category.{u, u} R) :
    (extensionActionDiagonalNatTrans R C).app (extensionActionUnit R C) =
      (extensionActionLeftUnit R C).inv.app (extensionActionUnit R C) := by
  apply extensionAction_hom_ext R
  · change extensionActionSection R (extensionActionDiagonal R (extensionActionUnit R C)) =
      extensionActionSection R
        (GroupCompletion.ActionLocalization.ofHom
          (extensionLeftUnitIso R (extensionActionUnit R C).obj).inv)
    rw [extensionActionSection_ofHom]
    change _ = (extensionLeftUnitMiddleIso R (extensionActionUnit R C).obj).inv
    apply pullback.hom_ext
    · simp only [extensionActionDiagonal_section_fst]
      exact (extensionLeftUnitMiddleIso_inv_fst R (extensionActionUnit R C).obj).symm
    · simp only [extensionActionDiagonal_section_snd]
      exact (extensionLeftUnitMiddleIso_inv_snd R (extensionActionUnit R C).obj).symm
  · change extensionActionRetraction R (extensionActionDiagonal R (extensionActionUnit R C)) =
      extensionActionRetraction R
        (GroupCompletion.ActionLocalization.ofHom
          (extensionLeftUnitIso R (extensionActionUnit R C).obj).inv)
    rw [extensionActionRetraction_ofHom, extensionActionDiagonal_retraction]
    change pullback.fst (𝟙 C) (𝟙 C) = pullback.snd (𝟙 C) (𝟙 C)
    simpa using (pullback.condition (f := (𝟙 C)) (g := (𝟙 C)))

end ModuleCat.FiniteProjective
