/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.DiagonalAction
public import Colib.CategoryTheory.GroupCompletion.Functoriality

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/Projection.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The projection of Grayson's localization

The first-coordinate projection `C⁻¹D ⥤ ⟨C,C⟩` is defined on the actual
quotient morphisms. Faithful right translations make compatible denominator
isomorphisms unique whenever their target component is monic. This is the
uniqueness needed for the later cocartesian transport construction.
-/

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

instance firstProjectionLinear : (CategoryTheory.Prod.fst C D).LaxLeftLinear C where
  μₗ s X := 𝟙 (s ⊗ X.1)
  μₗ_naturality_left f X := by
    change f ▷ X.1 ≫ 𝟙 _ = 𝟙 _ ≫ f ▷ X.1
    simp
  μₗ_naturality_right s _ _ f := by
    change s ◁ f.1 ≫ 𝟙 _ = 𝟙 _ ≫ s ◁ f.1
    simp
  μₗ_associativity s t X := by
    change 𝟙 _ ≫ (α_ s t X.1).hom = (α_ s t X.1).hom ≫ s ◁ 𝟙 _ ≫ 𝟙 _
    simp
  μₗ_unitality X := by
    change (λ_ X.1).hom = 𝟙 _ ≫ (λ_ X.1).hom
    simp

namespace Localization

/-- Forget the acted-on coordinate while retaining the actual denominator. -/
def projection : Localization C D ⥤ ActionLocalization C C :=
  ActionLocalization.mapFunctor (CategoryTheory.Prod.fst C D)

@[simp]
lemma projection_obj (X : Localization C D) : projection.obj X = ⟨X.obj.1⟩ := rfl

@[simp]
lemma projection_mkHom {X Y : C × D} (s : C) (f : s ⊗ X.1 ⟶ Y.1)
    (g : s ⊙ₗ X.2 ⟶ Y.2) :
    projection.map (mkHom s f g) = ActionLocalization.mkHom ⟨s, f⟩ := by
  change (ActionLocalization.mapFunctor (CategoryTheory.Prod.fst C D)).map
    (ActionLocalization.mkHom ⟨s, (f, g)⟩) = _
  rw [ActionLocalization.mapFunctor_mkHom]
  congr 1
  simp [ActionLocalization.HomRep.mapRep, Functor.LaxLeftLinear.μₗ]

/-- Faithfulness and monicity force uniqueness of a change of denominator. -/
lemma denominatorIso_unique {A B s t : C} [(tensorRight A).Faithful]
    (f : s ⊗ A ⟶ B) (g : t ⊗ A ⟶ B) [Mono g]
    (e e' : s ≅ t) (he : e.hom ▷ A ≫ g = f) (he' : e'.hom ▷ A ≫ g = f) :
    e = e' := by
  apply Iso.ext
  apply (tensorRight A).map_injective
  exact (cancel_mono g).1 (he.trans he'.symm)

/-- Equality in the base projection determines a unique denominator isomorphism. -/
theorem base_mkHom_eq_iff_existsUnique {A B s t : C} [(tensorRight A).Faithful]
    (f : s ⊗ A ⟶ B) (g : t ⊗ A ⟶ B) [Mono g] :
    ActionLocalization.mkHom (C := C) (D := C) ⟨s, f⟩ =
      ActionLocalization.mkHom ⟨t, g⟩ ↔
      ∃! e : s ≅ t, e.hom ▷ A ≫ g = f := by
  rw [ActionLocalization.mkHom_eq_iff]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, he, fun e' he' ↦ denominatorIso_unique f g e' e he' he⟩
  · rintro ⟨e, he, _⟩
    exact ⟨e, he⟩

/-- With a fixed monic first component, quotient equality is literal equality
of the acted-on component. -/
theorem mkHom_eq_iff_same_base {X Y : C × D} (s : C)
    [(tensorRight X.1).Faithful] (f : s ⊗ X.1 ⟶ Y.1) [Mono f]
    (g g' : s ⊙ₗ X.2 ⟶ Y.2) : mkHom s f g = mkHom s f g' ↔ g = g' := by
  constructor
  · intro h
    obtain ⟨e, he, hg⟩ := (mkHom_eq_iff s s f g f g').1 h
    have heq : e = Iso.refl s := denominatorIso_unique f f e (Iso.refl s) he (by simp)
    simpa [heq] using hg.symm
  · rintro rfl
    rfl

/-- Every arrow above a specified base representative has a unique normal form
using that representative's denominator. -/
theorem existsUnique_normalized {X Y : C × D} (s : C)
    [(tensorRight X.1).Faithful] (f : s ⊗ X.1 ⟶ Y.1) [Mono f]
    (h : (⟨X⟩ : Localization C D) ⟶ ⟨Y⟩)
    (hh : projection.map h = ActionLocalization.mkHom ⟨s, f⟩) :
    ∃! g : s ⊙ₗ X.2 ⟶ Y.2, mkHom s f g = h := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X Y h
  have hr : projection.map (mkHom r.denom r.map.1 r.map.2) =
      ActionLocalization.mkHom ⟨s, f⟩ := hh
  rw [projection_mkHom, ActionLocalization.mkHom_eq_iff] at hr
  obtain ⟨e, he⟩ := hr
  change e.hom ▷ X.1 ≫ f = r.map.1 at he
  let g := e.inv ⊵ₗ X.2 ≫ r.map.2
  have hg : mkHom s f g = mkHom r.denom r.map.1 r.map.2 := by
    apply (mkHom_eq_iff _ _ _ _ _ _).2
    refine ⟨e.symm, ?_, rfl⟩
    change e.inv ▷ X.1 ≫ r.map.1 = f
    rw [← he]
    simp
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  exact (mkHom_eq_iff_same_base s f g' g).1 (hg'.trans hg.symm)

/-- Composition on simultaneous representatives retains the actual associators. -/
lemma mkHom_comp {X Y Z : C × D} (s t : C)
    (f : s ⊗ X.1 ⟶ Y.1) (g : s ⊙ₗ X.2 ⟶ Y.2)
    (f' : t ⊗ Y.1 ⟶ Z.1) (g' : t ⊙ₗ Y.2 ⟶ Z.2) :
    mkHom s f g ≫ mkHom t f' g' =
      mkHom (t ⊗ s) ((α_ t s X.1).hom ≫ t ◁ f ≫ f')
        ((αₗ t s X.2).hom ≫ t ⊴ₗ g ≫ g') := rfl

/-- The candidate cocartesian lift translates the second coordinate. -/
def lift {A B : C} (s : C) (f : s ⊗ A ⟶ B) (X : D) :
    (⟨(A, X)⟩ : Localization C D) ⟶ ⟨(B, s ⊙ₗ X)⟩ :=
  mkHom s f (𝟙 _)

@[simp]
lemma projection_lift {A B : C} (s : C) (f : s ⊗ A ⟶ B) (X : D) :
    projection.map (lift s f X) = ActionLocalization.mkHom ⟨s, f⟩ :=
  projection_mkHom (X := (A, X)) (Y := (B, s ⊙ₗ X)) s f (𝟙 _)

/-- A lift followed by a normalized arrow is its translated composite. -/
lemma lift_comp_mkHom {A B T : C} (s t : C) (f : s ⊗ A ⟶ B)
    (k : t ⊗ B ⟶ T) (X Y : D) (g : t ⊙ₗ s ⊙ₗ X ⟶ Y) :
    lift s f X ≫ mkHom t k g =
      mkHom (X := (A, X)) (Y := (T, Y)) (t ⊗ s)
        ((α_ t s A).hom ≫ t ◁ f ≫ k) ((αₗ t s X).hom ≫ g) := by
  rw [lift, mkHom_comp]
  simp

/-- At fixed base representatives, cocartesian factorization is unique on the
acted-on component. No homotopy or group-completion theorem is assumed. -/
theorem existsUnique_lift_component {A B T : C} (s t : C)
    [(tensorRight A).Faithful] (f : s ⊗ A ⟶ B) (k : t ⊗ B ⟶ T)
    [Mono ((α_ t s A).hom ≫ t ◁ f ≫ k)] (X Y : D)
    (h : (⟨(A, X)⟩ : Localization C D) ⟶ ⟨(T, Y)⟩)
    (hh : projection.map h = ActionLocalization.mkHom ⟨s, f⟩ ≫
      ActionLocalization.mkHom ⟨t, k⟩) :
    ∃! g : t ⊙ₗ s ⊙ₗ X ⟶ Y, lift s f X ≫ mkHom t k g = h := by
  change projection.map h = ActionLocalization.mkHom
    ⟨t ⊗ s, (α_ t s A).hom ≫ t ◁ f ≫ k⟩ at hh
  obtain ⟨q, hq, _⟩ := existsUnique_normalized (X := (A, X)) (Y := (T, Y)) (t ⊗ s)
    ((α_ t s A).hom ≫ t ◁ f ≫ k) h hh
  refine ⟨(αₗ t s X).inv ≫ q, ?_, ?_⟩
  · dsimp only
    rw [lift_comp_mkHom]
    simpa using hq
  · intro g hg
    rw [lift_comp_mkHom] at hg
    have he := (mkHom_eq_iff_same_base (X := (A, X)) (Y := (T, Y)) (t ⊗ s)
      ((α_ t s A).hom ≫ t ◁ f ≫ k) ((αₗ t s X).hom ≫ g) q).1
        (hg.trans hq.symm)
    exact ((αₗ t s X).inv_comp_eq.2 he.symm).symm

/-- The lift satisfies the full unique-factorization property over every base
arrow when the actor is a groupoid with faithful translations. -/
theorem lift_universal [IsGroupoid C] [∀ A : C, (tensorRight A).Faithful]
    {A B T : C} (s : C) (f : s ⊗ A ⟶ B) (X Y : D)
    (w : (⟨B⟩ : ActionLocalization C C) ⟶ ⟨T⟩)
    (h : (⟨(A, X)⟩ : Localization C D) ⟶ ⟨(T, Y)⟩)
    (hh : projection.map h = ActionLocalization.mkHom ⟨s, f⟩ ≫ w) :
    ∃! l : (⟨(B, s ⊙ₗ X)⟩ : Localization C D) ⟶ ⟨(T, Y)⟩,
      projection.map l = w ∧ lift s f X ≫ l = h := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective B T w
  obtain ⟨g, hg, hg_unique⟩ := existsUnique_lift_component s r.denom f r.map X Y h hh
  refine ⟨mkHom r.denom r.map g, ⟨projection_mkHom _ _ _, hg⟩, ?_⟩
  rintro l ⟨hl, hlcomp⟩
  obtain ⟨g', hg', _⟩ := existsUnique_normalized
    (X := (B, s ⊙ₗ X)) (Y := (T, Y)) r.denom r.map l hl
  have hgg : g' = g := hg_unique g' (by dsimp only; rw [hg']; exact hlcomp)
  rw [← hg', hgg]

end Localization
end CategoryTheory.GroupCompletion
