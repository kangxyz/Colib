/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.UnitArrows

/-!
Implementation provenance: `Quillen/CategoryTheory/GroupCompletion/UnitArrowEquiv.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original arrows out of zero as actual coordinate isomorphisms

The original diagonal-action quotient does not identify distinct zero-to-pair
arrows. Consequently actual arrows act unambiguously on coordinate frames.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory MonoidalCategory
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]

omit [IsGroupoid C] in
/-- The canonical zero arrow remembers its coordinate isomorphism injectively. -/
lemma unitArrow_injective (P Q : C) :
    Function.Injective (unitArrow : (P ⟶ Q) →
      ((⟨𝟙_ C, 𝟙_ C⟩ : Localization C C) ⟶ ⟨P, Q⟩)) := by
  intro f g h
  obtain ⟨e, he₁, he₂⟩ := (mkHom_eq_iff (X := (𝟙_ C, 𝟙_ C)) (Y := (P, Q)) P P
    (ρ_ P).hom ((ρ_ P).hom ≫ f)
    (ρ_ P).hom ((ρ_ P).hom ≫ g)).mp h
  change e.hom ▷ (𝟙_ C) ≫ (ρ_ P).hom ≫ g = (ρ_ P).hom ≫ f at he₂
  rw [← Category.assoc, he₁] at he₂
  exact ((cancel_epi (ρ_ P).hom).mp he₂).symm

/-- Actual zero-to-pair arrows are exactly the actual morphisms between the two coordinates. -/
def unitArrowEquiv (P Q : C) : (P ⟶ Q) ≃
    ((⟨𝟙_ C, 𝟙_ C⟩ : Localization C C) ⟶ ⟨P, Q⟩) :=
  Equiv.ofBijective unitArrow ⟨unitArrow_injective P Q, unitArrow_surjective P Q⟩

/-- The action of an original quotient arrow on an actual coordinate frame. -/
def transportFrame {P Q P' Q' : C}
    (a : (⟨P, Q⟩ : Localization C C) ⟶ ⟨P', Q'⟩) (r : P ⟶ Q) : P' ⟶ Q' :=
  (unitArrowEquiv P' Q').symm (unitArrow r ≫ a)

/-- Frame transport retains the original composition of zero arrows exactly. -/
lemma unitArrow_transportFrame {P Q P' Q' : C}
    (a : (⟨P, Q⟩ : Localization C C) ⟶ ⟨P', Q'⟩) (r : P ⟶ Q) :
    unitArrow (transportFrame a r) = unitArrow r ≫ a :=
  (unitArrowEquiv P' Q').apply_symm_apply _

/-- Identity arrows preserve the original frame. -/
lemma transportFrame_id {P Q : C} (r : P ⟶ Q) :
    transportFrame (𝟙 (⟨P, Q⟩ : Localization C C)) r = r := by
  apply unitArrow_injective
  rw [unitArrow_transportFrame, Category.comp_id]

/-- Frame transport composes along the original quotient arrows. -/
lemma transportFrame_comp {P Q P' Q' P'' Q'' : C}
    (a : (⟨P, Q⟩ : Localization C C) ⟶ ⟨P', Q'⟩)
    (b : (⟨P', Q'⟩ : Localization C C) ⟶ ⟨P'', Q''⟩) (r : P ⟶ Q) :
    transportFrame (a ≫ b) r = transportFrame b (transportFrame a r) := by
  apply unitArrow_injective
  simp only [unitArrow_transportFrame, Category.assoc]

/-- A represented arrow transports frames by its actual translating object and component maps. -/
lemma transportFrame_mkHom {P Q P' Q' : C}
    (a : ActionLocalization.HomRep (C := C) (P, Q) (P', Q')) (r : P ⟶ Q) :
    transportFrame (ActionLocalization.mkHom a) r =
      inv a.map.1 ≫ a.denom ◁ r ≫ a.map.2 := by
  apply unitArrow_injective
  rw [unitArrow_transportFrame, ActionLocalization.mkHom_factorization,
    ← Category.assoc, unitArrow_translation]
  exact unitArrow_postcomp (a.denom ◁ r) a.map.1 a.map.2

/-- Original un-translated arrows act by the original two-coordinate change of frame. -/
lemma transportFrame_ofHom {P Q P' Q' : C} (a : P ⟶ P') (b : Q ⟶ Q') (r : P ⟶ Q) :
    transportFrame (ActionLocalization.ofHom (a, b)) r = inv a ≫ r ≫ b := by
  apply unitArrow_injective
  rw [unitArrow_transportFrame, unitArrow_postcomp]

/-- Original translations tensor the given frame without further choices. -/
lemma transportFrame_translation {P Q : C} (S : C) (r : P ⟶ Q) :
    transportFrame (ActionLocalization.translation S (P, Q)) r = S ◁ r := by
  apply unitArrow_injective
  rw [unitArrow_transportFrame, unitArrow_translation]

end CategoryTheory.GroupCompletion.Localization
