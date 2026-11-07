/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensions
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveMonoidal
public import Colib.CategoryTheory.ExactCategory.Extensions.Basic
public import Colib.CategoryTheory.ExactCategory.CoproductDeflation
public import Colib.CategoryTheory.GroupCompletion.ActionLocalization

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionAction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Direct sum on extensions with fixed quotient

The acting projective is added to the kernel: the quotient remains exactly `C`.
This is the fixed-quotient extension action in Grayson's construction, distinct
from the direct-sum action on the total category of admissible inflations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
attribute [local instance] directSumMonoidal directSumSymmetric

/-- Add a projective summand to the middle term and send it to zero in the
unchanged quotient. -/
def extensionAdd (C : Category.{u, u} R) (S : IsoCategory R)
    (p : (exactStructure R).ExtensionFiber C) : (exactStructure R).ExtensionFiber C :=
  ⟨⟨Over.mk (coprod.desc (0 : S.of ⟶ C) p.of.obj.hom),
    (exactStructure R).deflation_coprod_desc _ _ p.of.property⟩⟩

/-- Isomorphisms of projectives and of extensions induce actual isomorphisms
of the translated extensions over the fixed quotient. -/
def extensionAddIso {C : Category.{u, u} R} {S T : IsoCategory R}
    {p q : (exactStructure R).ExtensionFiber C} (f : S.of ≅ T.of) (g : p.of ≅ q.of) :
    (extensionAdd R C S p).of ≅ (extensionAdd R C T q).of :=
  (exactStructure R).extensionProperty C |>.isoMk
    (Over.isoMk (f ⊗ᵢ ((exactStructure R).extensionMiddle C).mapIso g) (by
      change coprod.map f.hom g.hom.hom.left ≫ coprod.desc 0 q.of.obj.hom =
        coprod.desc 0 p.of.obj.hom
      simp [Over.w]))

/-- The action associator is the ordinary direct-sum associator on middle terms. -/
def extensionAddAssoc (C : Category.{u, u} R) (S T : IsoCategory R)
    (p : (exactStructure R).ExtensionFiber C) :
    extensionAdd R C (S ⊗ T) p ≅ extensionAdd R C S (extensionAdd R C T p) :=
  Core.isoMk ((exactStructure R).extensionProperty C |>.isoMk
    (Over.isoMk (α_ S.of T.of p.of.obj.left) (by
      change (coprod.associator _ _ _).hom ≫ coprod.desc 0 (coprod.desc 0 p.of.obj.hom) =
        coprod.desc 0 p.of.obj.hom
      apply coprod.hom_ext
      · apply coprod.hom_ext <;> simp
      · simp)))

/-- The action unit is the ordinary direct-sum unitor on middle terms. -/
def extensionAddUnit (C : Category.{u, u} R) (p : (exactStructure R).ExtensionFiber C) :
    extensionAdd R C (𝟙_ (IsoCategory R)) p ≅ p :=
  Core.isoMk ((exactStructure R).extensionProperty C |>.isoMk
    (Over.isoMk (λ_ p.of.obj.left) (by
      change (coprod.leftUnitor _).hom ≫ p.of.obj.hom = coprod.desc 0 p.of.obj.hom
      apply coprod.hom_ext
      · exact initialIsInitial.hom_ext _ _
      · simp)))

/-- The actual direct-sum action on the groupoid of extensions with quotient `C`. -/
@[instance_reducible]
def extensionFiberDirectSumAction (C : Category.{u, u} R) :
    MonoidalLeftAction (IsoCategory R) ((exactStructure R).ExtensionFiber C) where
  actionObj := extensionAdd R C
  actionHomLeft f p := ⟨extensionAddIso R f.iso (Iso.refl p.of)⟩
  actionHomRight S _ _ g := ⟨extensionAddIso R (Iso.refl S.of) g.iso⟩
  actionAssocIso := extensionAddAssoc R C
  actionUnitIso := extensionAddUnit R C
  actionHomRight_id S p := by
    apply extensionFiber_hom_ext R
    change coprod.map (𝟙 _) (𝟙 _) = 𝟙 _
    simp
  id_actionHomLeft S p := by
    apply extensionFiber_hom_ext R
    change coprod.map (𝟙 _) (𝟙 _) = 𝟙 _
    simp
  actionHom_comp := by
    intro S T U p q r f₁ f₂ g₁ g₂
    apply extensionFiber_hom_ext R
    change (((f₁.iso.hom ≫ f₂.iso.hom) ▷ p.of.obj.left) ≫
        U.of ◁ (g₁.iso.hom.hom.left ≫ g₂.iso.hom.hom.left)) =
      (f₁.iso.hom ▷ p.of.obj.left ≫ T.of ◁ g₁.iso.hom.hom.left) ≫
        (f₂.iso.hom ▷ q.of.obj.left ≫ U.of ◁ g₂.iso.hom.hom.left)
    simp only [← tensorHom_def, tensorHom_comp_tensorHom]
  actionAssocIso_hom_naturality := by
    intro S T U V p q f g h
    apply extensionFiber_hom_ext R
    change (((f.iso.hom ⊗ₘ g.iso.hom) ▷ p.of.obj.left) ≫
      (T.of ⊗ V.of) ◁ h.iso.hom.hom.left) ≫ (α_ T.of V.of q.of.obj.left).hom =
      (α_ S.of U.of p.of.obj.left).hom ≫
        (f.iso.hom ▷ (U.of ⊗ p.of.obj.left) ≫
          T.of ◁ (g.iso.hom ▷ p.of.obj.left ≫ V.of ◁ h.iso.hom.hom.left))
    simpa only [← tensorHom_def] using
      associator_naturality f.iso.hom g.iso.hom h.iso.hom.hom.left
  actionUnitIso_hom_naturality := by
    intro p q f
    apply extensionFiber_hom_ext R
    change (λ_ p.of.obj.left).hom ≫ f.iso.hom.hom.left =
      (𝟙_ (Category R)) ◁ f.iso.hom.hom.left ≫ (λ_ q.of.obj.left).hom
    exact (leftUnitor_naturality f.iso.hom.hom.left).symm
  whiskerLeft_actionHomLeft := by
    intro S T U f p
    apply extensionFiber_hom_ext R
    change (S.of ◁ f.iso.hom) ▷ p.of.obj.left =
      (α_ S.of T.of p.of.obj.left).hom ≫ S.of ◁ (f.iso.hom ▷ p.of.obj.left) ≫
        (α_ S.of U.of p.of.obj.left).inv
    exact MonoidalLeftAction.whiskerLeft_actionHomLeft S.of f.iso.hom p.of.obj.left
  whiskerRight_actionHomLeft := by
    intro S T U f p
    apply extensionFiber_hom_ext R
    change (f.iso.hom ▷ U.of) ▷ p.of.obj.left =
      (α_ S.of U.of p.of.obj.left).hom ≫ f.iso.hom ▷ (U.of ⊗ p.of.obj.left) ≫
        (α_ T.of U.of p.of.obj.left).inv
    exact MonoidalLeftAction.whiskerRight_actionHomLeft U.of f.iso.hom p.of.obj.left
  associator_actionHom := by
    intro S T U p
    apply extensionFiber_hom_ext R
    change (α_ S.of T.of U.of).hom ▷ p.of.obj.left ≫
        (α_ S.of (T.of ⊗ U.of) p.of.obj.left).hom ≫
        S.of ◁ (α_ T.of U.of p.of.obj.left).hom =
      (α_ (S.of ⊗ T.of) U.of p.of.obj.left).hom ≫
        (α_ S.of T.of (U.of ⊗ p.of.obj.left)).hom
    exact pentagon S.of T.of U.of p.of.obj.left
  leftUnitor_actionHom := by
    intro S p
    apply extensionFiber_hom_ext R
    change (λ_ S.of).hom ▷ p.of.obj.left =
      (α_ (𝟙_ (Category R)) S.of p.of.obj.left).hom ≫ (λ_ (S.of ⊗ p.of.obj.left)).hom
    exact MonoidalLeftAction.leftUnitor_actionHom S.of p.of.obj.left
  rightUnitor_actionHom := by
    intro S p
    apply extensionFiber_hom_ext R
    change (ρ_ S.of).hom ▷ p.of.obj.left =
      (α_ S.of (𝟙_ (Category R)) p.of.obj.left).hom ≫ S.of ◁ (λ_ p.of.obj.left).hom
    exact MonoidalLeftAction.rightUnitor_actionHom S.of p.of.obj.left

attribute [local instance] extensionFiberDirectSumAction

/-- Direct sum retains the original quotient and kills the added summand. -/
theorem extensionAction_obj_hom {C : Category.{u, u} R} (S : IsoCategory R)
    (p : (exactStructure R).ExtensionFiber C) :
    (S ⊙ₗ p).of.obj.hom = coprod.desc (0 : S.of ⟶ C) p.of.obj.hom := rfl

/-- Grayson's category associated to the actual fixed-quotient extension action. -/
abbrev ExtensionActionCategory (C : Category.{u, u} R) :=
  GroupCompletion.ActionLocalization (IsoCategory R) ((exactStructure R).ExtensionFiber C)

/-- The fixed quotient does not discard the acting isomorphism: restriction to
its direct summand detects it. -/
theorem extensionActionRight_faithful (C : Category.{u, u} R)
    (p : (exactStructure R).ExtensionFiber C) :
    (MonoidalLeftAction.actionRight (IsoCategory R) p).Faithful where
  map_injective {S T} {f g} h := by
    apply Core.hom_ext
    have h' := congrArg (fun k => k.iso.hom.hom.left) h
    change coprod.map f.iso.hom (𝟙 _) = coprod.map g.iso.hom (𝟙 _) at h'
    have h'' := congrArg (fun k => (coprod.inl : S.of ⟶ S.of ⨿ p.of.obj.left) ≫ k ≫
      coprod.desc (𝟙 T.of) (0 : p.of.obj.left ⟶ T.of)) h'
    simpa using h''

end ModuleCat.FiniteProjective
