/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.Projection

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/SecondProjection.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The second-coordinate projection in Grayson's comparison theorem -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

instance secondProjectionLinear : (CategoryTheory.Prod.snd C D).LaxLeftLinear C where
  μₗ s X := 𝟙 (s ⊙ₗ X.2)
  μₗ_naturality_left f X := by
    change f ⊵ₗ X.2 ≫ 𝟙 _ = 𝟙 _ ≫ f ⊵ₗ X.2
    simp
  μₗ_naturality_right s _ _ f := by
    change s ⊴ₗ f.2 ≫ 𝟙 _ = 𝟙 _ ≫ s ⊴ₗ f.2
    simp
  μₗ_associativity s t X := by
    change 𝟙 _ ≫ (αₗ s t X.2).hom =
      (αₗ s t X.2).hom ≫ s ⊴ₗ 𝟙 _ ≫ 𝟙 _
    simp
  μₗ_unitality X := by
    change (λₗ[C] X.2).hom = 𝟙 _ ≫ (λₗ[C] X.2).hom
    simp

namespace Localization

/-- Forget the first coordinate, keeping the original acted-on arrow and denominator. -/
def secondProjection : Localization C D ⥤ ActionLocalization C D :=
  ActionLocalization.mapFunctor (CategoryTheory.Prod.snd C D)

@[simp]
theorem secondProjection_obj (X : Localization C D) :
    secondProjection.obj X = ⟨X.obj.2⟩ := rfl

@[simp]
theorem secondProjection_mkHom {X Y : C × D} (s : C)
    (f : s ⊗ X.1 ⟶ Y.1) (g : s ⊙ₗ X.2 ⟶ Y.2) :
    secondProjection.map (mkHom s f g) = ActionLocalization.mkHom ⟨s, g⟩ := by
  change (ActionLocalization.mapFunctor (CategoryTheory.Prod.snd C D)).map
    (ActionLocalization.mkHom ⟨s, (f, g)⟩) = _
  rw [ActionLocalization.mapFunctor_mkHom]
  congr 1
  simp [ActionLocalization.HomRep.mapRep, Functor.LaxLeftLinear.μₗ]

/-- Faithfulness of the orbit functor and a monic target map detect the denominator iso. -/
theorem actionDenominatorIso_unique {X Y : D} {s t : C}
    [(MonoidalLeftAction.actionRight C X).Faithful]
    (f : s ⊙ₗ X ⟶ Y) (g : t ⊙ₗ X ⟶ Y) [Mono g]
    (e e' : s ≅ t) (he : e.hom ⊵ₗ X ≫ g = f) (he' : e'.hom ⊵ₗ X ≫ g = f) : e = e' := by
  apply Iso.ext
  apply (MonoidalLeftAction.actionRight C X).map_injective
  exact (cancel_mono g).1 (he.trans he'.symm)

/-- At a fixed monic second component, quotient equality is equality of the first component. -/
theorem mkHom_eq_iff_same_second {X Y : C × D} (s : C)
    [(MonoidalLeftAction.actionRight C X.2).Faithful]
    (g : s ⊙ₗ X.2 ⟶ Y.2) [Mono g]
    (f f' : s ⊗ X.1 ⟶ Y.1) : mkHom s f g = mkHom s f' g ↔ f = f' := by
  constructor
  · intro h
    obtain ⟨e, he, hg⟩ := (mkHom_eq_iff s s f g f' g).1 h
    have heq : e = Iso.refl s :=
      actionDenominatorIso_unique g g e (Iso.refl s) hg (by simp)
    simpa [heq] using he.symm
  · rintro rfl
    rfl

/-- Every arrow over a specified second-projection representative has a unique normal form. -/
theorem existsUnique_secondNormalized {X Y : C × D} (s : C)
    [(MonoidalLeftAction.actionRight C X.2).Faithful]
    (g : s ⊙ₗ X.2 ⟶ Y.2) [Mono g]
    (h : (⟨X⟩ : Localization C D) ⟶ ⟨Y⟩)
    (hh : secondProjection.map h = ActionLocalization.mkHom ⟨s, g⟩) :
    ∃! f : s ⊗ X.1 ⟶ Y.1, mkHom s f g = h := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X Y h
  have hr : secondProjection.map (mkHom r.denom r.map.1 r.map.2) =
      ActionLocalization.mkHom ⟨s, g⟩ := hh
  rw [secondProjection_mkHom, ActionLocalization.mkHom_eq_iff] at hr
  obtain ⟨e, he⟩ := hr
  change e.hom ⊵ₗ X.2 ≫ g = r.map.2 at he
  let f := e.inv ▷ X.1 ≫ r.map.1
  have hf : mkHom s f g = mkHom r.denom r.map.1 r.map.2 := by
    apply (mkHom_eq_iff _ _ _ _ _ _).2
    refine ⟨e.symm, rfl, ?_⟩
    change e.inv ⊵ₗ X.2 ≫ r.map.2 = g
    rw [← he]
    simp
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  exact (mkHom_eq_iff_same_second s g f' f).1 (hf'.trans hf.symm)

/-- The second-projection lift translates the first coordinate. -/
def secondLift {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) (A : C) :
    (⟨(A, X)⟩ : Localization C D) ⟶ ⟨(s ⊗ A, Y)⟩ := mkHom s (𝟙 _) g

@[simp]
theorem secondProjection_secondLift {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) (A : C) :
    secondProjection.map (secondLift s g A) = ActionLocalization.mkHom ⟨s, g⟩ :=
  secondProjection_mkHom (X := (A, X)) (Y := (s ⊗ A, Y)) s (𝟙 _) g

/-- Composition of the second-coordinate lift with a normalized arrow. -/
theorem secondLift_comp_mkHom {X Y Z : D} (s t : C) (A B : C)
    (g : s ⊙ₗ X ⟶ Y) (g' : t ⊙ₗ Y ⟶ Z) (f : t ⊗ (s ⊗ A) ⟶ B) :
    secondLift s g A ≫ mkHom t f g' =
      mkHom (X := (A, X)) (Y := (B, Z)) (t ⊗ s)
        ((α_ t s A).hom ≫ f) ((αₗ t s X).hom ≫ t ⊴ₗ g ≫ g') := by
  rw [secondLift, mkHom_comp]
  simp

/-- The second projection has actual cocartesian factorizations. Its required
monicity and orbit-faithfulness hypotheses are explicit. -/
theorem secondLift_universal
    [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
    [∀ (X Y : D) (f : X ⟶ Y), Mono f]
    {X Y Z : D} (s : C) (g : s ⊙ₗ X ⟶ Y) (A B : C)
    (w : (⟨Y⟩ : ActionLocalization C D) ⟶ ⟨Z⟩)
    (h : (⟨(A, X)⟩ : Localization C D) ⟶ ⟨(B, Z)⟩)
    (hh : secondProjection.map h = ActionLocalization.mkHom ⟨s, g⟩ ≫ w) :
    ∃! l : (⟨(s ⊗ A, Y)⟩ : Localization C D) ⟶ ⟨(B, Z)⟩,
      secondProjection.map l = w ∧ secondLift s g A ≫ l = h := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective Y Z w
  change secondProjection.map h = ActionLocalization.mkHom
    ⟨r.denom ⊗ s, (αₗ r.denom s X).hom ≫ r.denom ⊴ₗ g ≫ r.map⟩ at hh
  obtain ⟨f, hf, hu⟩ := existsUnique_secondNormalized (X := (A, X)) (Y := (B, Z))
    (r.denom ⊗ s) ((αₗ r.denom s X).hom ≫ r.denom ⊴ₗ g ≫ r.map) h hh
  let k := (α_ r.denom s A).inv ≫ f
  have hk : secondLift s g A ≫ mkHom r.denom k r.map = h := by
    rw [secondLift_comp_mkHom]
    simpa only [k, Iso.hom_inv_id_assoc] using hf
  refine ⟨mkHom r.denom k r.map, ⟨secondProjection_mkHom _ _ _, hk⟩, ?_⟩
  rintro l ⟨hl, hlcomp⟩
  obtain ⟨f', hf', _⟩ := existsUnique_secondNormalized
    (X := (s ⊗ A, Y)) (Y := (B, Z)) r.denom r.map l hl
  have he : (α_ r.denom s A).hom ≫ f' = f := hu _ (by
    dsimp only
    rw [← secondLift_comp_mkHom, hf']
    exact hlcomp)
  have he' : f' = k := by
    dsimp only [k]
    rw [← he]
    simp
  rw [← hf', he']

end Localization
end CategoryTheory.GroupCompletion
