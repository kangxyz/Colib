/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.IteratedFiberEquivalence

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/IteratedCocartesian.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Cocartesian lifts of the iterated second projection -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction
/-- The iterated projection has the named trivial action on its base. -/
local instance : MonoidalLeftAction C (ActionLocalization C D) :=
  MonoidalLeftAction.trivial C (ActionLocalization C D)

@[simp]
theorem iteratedSecondProjection_ofHom {X Y : C × Localization C D} (f : X ⟶ Y) :
    iteratedSecondProjection.map (ActionLocalization.ofHom (C := C) f) =
      secondProjection.map f.2 := by
  dsimp only [iteratedSecondProjection, Functor.comp_map]
  rw [secondProjection_ofHom, ActionLocalization.mapFunctor_ofHom,
    ActionLocalization.TrivialAction.forgetFunctor_map_ofHom]

instance secondFiberHom_isIso (X : D) {A B : C} (f : A ⟶ B) [IsIso f] :
    IsIso (secondFiberHom X f) := by
  change IsIso ((fixedSecondEntry X).map f)
  infer_instance

omit [BraidedCategory C] in
/-- Translation carries each canonical lift to a canonical lift followed by
an actual fiber isomorphism, with the original associator retained. -/
theorem firstCoordinateTranslation_secondLift {X Y : D} (s : C)
    (g : s ⊙ₗ X ⟶ Y) (A t : C) :
    (firstCoordinateTranslation t).map (secondLift s g A) =
      secondLift s g (A ⊗ t) ≫ secondFiberHom Y (α_ s A t).inv := by
  change (firstCoordinateTranslation t).map
    (mkHom (X := (A, X)) (Y := (s ⊗ A, Y)) s (𝟙 (s ⊗ A)) g) = _
  rw [firstCoordinateTranslation_mkHom]
  dsimp only [secondLift, secondFiberHom, mkHom]
  rw [ActionLocalization.mkHom_comp_ofHom]
  apply congrArg ActionLocalization.mkHom
  apply congrArg (ActionLocalization.HomRep.mk s)
  change ((α_ s A t).inv ≫ (𝟙 (s ⊗ A)) ▷ t, g) =
    (𝟙 _ ≫ (α_ s A t).inv, g ≫ 𝟙 Y)
  simp

section Cocartesian
variable [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]

instance firstCoordinateTranslation_secondLift_stronglyCocartesian
    {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) (A t : C) :
    secondProjection.IsStronglyCocartesian
      (secondProjection.map ((firstCoordinateTranslation t).map (secondLift s g A)))
      ((firstCoordinateTranslation t).map (secondLift s g A)) := by
  rw [firstCoordinateTranslation_secondLift, Functor.map_comp]
  infer_instance

end Cocartesian

/-- The lift in the twice localized category fixes its outer actor coordinate. -/
def iteratedLift {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) (A B : C) :
    (⟨(A, ⟨(B, X)⟩)⟩ : Localization C (Localization C D)) ⟶
      ⟨(A, ⟨(s ⊗ B, Y)⟩)⟩ :=
  ActionLocalization.ofHom (C := C)
    (X := (A, (⟨(B, X)⟩ : Localization C D)))
    (Y := (A, (⟨(s ⊗ B, Y)⟩ : Localization C D))) (𝟙 A, secondLift s g B)

@[simp]
theorem iteratedSecondProjection_iteratedLift {X Y : D} (s : C)
    (g : s ⊙ₗ X ⟶ Y) (A B : C) :
    iteratedSecondProjection.map (iteratedLift s g A B) =
      ActionLocalization.mkHom ⟨s, g⟩ := by
  rw [iteratedLift, iteratedSecondProjection_ofHom, secondProjection_secondLift]

section Cocartesian
variable [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]

omit [BraidedCategory C]
  [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f] in
private theorem secondFactor {U V W : Localization C D} (v : U ⟶ V)
    [secondProjection.IsStronglyCocartesian (secondProjection.map v) v]
    (w : secondProjection.obj V ⟶ secondProjection.obj W) (h : U ⟶ W)
    (hh : secondProjection.map h = secondProjection.map v ≫ w) :
    ∃! k : V ⟶ W, secondProjection.map k = w ∧ v ≫ k = h := by
  let : secondProjection.IsHomLift (secondProjection.map v ≫ w) h := by
    rw [← hh]
    exact IsHomLift.map _ _
  obtain ⟨k, hk, hu⟩ := Functor.IsStronglyCocartesian.universal_property'
    (p := secondProjection) (f := secondProjection.map v) (φ := v) w h
  let := hk.1
  refine ⟨k, ⟨(IsHomLift.eq_of_isHomLift secondProjection w k).symm, hk.2⟩, ?_⟩
  intro k' hk'
  apply hu k'
  refine ⟨?_, hk'.2⟩
  rw [← hk'.1]
  exact IsHomLift.map _ _

/-- The original inner lift survives the outer quotient, including uniqueness
against representatives with different translating objects. -/
theorem iteratedLift_universal {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) (A B : C)
    (Z : Localization C (Localization C D))
    (w : (⟨Y⟩ : ActionLocalization C D) ⟶ iteratedSecondProjection.obj Z)
    (h : (⟨(A, ⟨(B, X)⟩)⟩ : Localization C (Localization C D)) ⟶ Z)
    (hh : iteratedSecondProjection.map h = ActionLocalization.mkHom ⟨s, g⟩ ≫ w) :
    ∃! k : (⟨(A, ⟨(s ⊗ B, Y)⟩)⟩ : Localization C (Localization C D)) ⟶ Z,
      iteratedSecondProjection.map k = w ∧ iteratedLift s g A B ≫ k = h := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective
    (A, (⟨(B, X)⟩ : Localization C D)) Z.obj h
  change iteratedSecondProjection.map (mkHom r.denom r.map.1 r.map.2) = _ at hh
  rw [iteratedSecondProjection_mkHom] at hh
  have hr : secondProjection.map r.map.2 =
      secondProjection.map ((firstCoordinateTranslation r.denom).map (secondLift s g B)) ≫ w := by
    rw [secondProjection_firstCoordinateTranslation, secondProjection_secondLift]
    exact hh
  obtain ⟨k, hk, _⟩ := secondFactor
    ((firstCoordinateTranslation r.denom).map (secondLift s g B)) w r.map.2 hr
  let l : (⟨(A, ⟨(s ⊗ B, Y)⟩)⟩ : Localization C (Localization C D)) ⟶ Z :=
    mkHom r.denom r.map.1 k
  have hl : iteratedLift s g A B ≫ l = ActionLocalization.mkHom r := by
    dsimp only [iteratedLift, l, mkHom]
    rw [ActionLocalization.ofHom_comp_mkHom]
    apply congrArg ActionLocalization.mkHom
    apply congrArg (ActionLocalization.HomRep.mk r.denom)
    apply Prod.ext
    · change r.denom ◁ 𝟙 A ≫ r.map.1 = r.map.1
      simp
    · exact hk.2
  refine ⟨l, ⟨?_, hl⟩, ?_⟩
  · change iteratedSecondProjection.map (mkHom
      (X := (A, (⟨(s ⊗ B, Y)⟩ : Localization C D))) (Y := Z.obj)
      r.denom r.map.1 k) = w
    rw [iteratedSecondProjection_mkHom]
    exact hk.1
  · intro l' hl'
    obtain ⟨t, rfl⟩ := ActionLocalization.mkHom_surjective
      (A, (⟨(s ⊗ B, Y)⟩ : Localization C D)) Z.obj l'
    have ht := hl'.2.trans hl.symm
    dsimp only [iteratedLift, l, mkHom] at ht
    rw [ActionLocalization.ofHom_comp_mkHom, ActionLocalization.ofHom_comp_mkHom] at ht
    obtain ⟨e, he⟩ := (ActionLocalization.mkHom_eq_iff _ _).1 ht
    have he₁ := congrArg _root_.Prod.fst he
    have he₂ := congrArg _root_.Prod.snd he
    apply (mkHom_eq_iff _ _ _ _ _ _).2
    refine ⟨e, ?_, ?_⟩
    · change e.hom ▷ A ≫ (r.denom ◁ 𝟙 A ≫ r.map.1) =
        t.denom ◁ 𝟙 A ≫ t.map.1 at he₁
      simpa only [whiskerLeft_id, Category.id_comp] using he₁
    · have htq : secondProjection.map t.map.2 = w := by
        have htmap := hl'.1
        change iteratedSecondProjection.map (mkHom t.denom t.map.1 t.map.2) = w at htmap
        rw [iteratedSecondProjection_mkHom] at htmap
        exact htmap
      have heq : secondProjection.map
          (e.hom ⊵ₗ (⟨(s ⊗ B, Y)⟩ : Localization C D) ≫ k) = w := by
        rw [Functor.map_comp, firstCoordinateLeftAction_actorMap,
          secondProjection_secondFiberHom]
        exact (Category.id_comp _).trans hk.1
      have hcomp : (firstCoordinateTranslation t.denom).map (secondLift s g B) ≫
          (e.hom ⊵ₗ (⟨(s ⊗ B, Y)⟩ : Localization C D) ≫ k) =
        (firstCoordinateTranslation t.denom).map (secondLift s g B) ≫ t.map.2 := by
        change (t.denom ⊴ₗ secondLift s g B) ≫ (e.hom ⊵ₗ _ ≫ k) =
          (t.denom ⊴ₗ secondLift s g B) ≫ t.map.2
        rw [← Category.assoc, MonoidalLeftAction.action_exchange, Category.assoc]
        exact he₂
      let : secondProjection.IsHomLift w t.map.2 := by
        rw [← htq]
        exact IsHomLift.map _ _
      let : secondProjection.IsHomLift w
          (e.hom ⊵ₗ (⟨(s ⊗ B, Y)⟩ : Localization C D) ≫ k) := by
        rw [← heq]
        exact IsHomLift.map _ _
      exact Functor.IsStronglyCocartesian.ext (p := secondProjection)
        (f := secondProjection.map ((firstCoordinateTranslation t.denom).map (secondLift s g B)))
        ((firstCoordinateTranslation t.denom).map (secondLift s g B)) w hcomp

/-- The explicit representative lifts satisfy the standard strong predicate. -/
instance iteratedLift_stronglyCocartesian {X Y : D} (s : C)
    (g : s ⊙ₗ X ⟶ Y) (A B : C) :
    iteratedSecondProjection.IsStronglyCocartesian
      (iteratedSecondProjection.map (iteratedLift s g A B)) (iteratedLift s g A B) where
  universal_property' {Z} w h _ := by
    have hh := (IsHomLift.eq_of_isHomLift iteratedSecondProjection
      (iteratedSecondProjection.map (iteratedLift s g A B) ≫ w) h).symm
    rw [iteratedSecondProjection_iteratedLift] at hh
    obtain ⟨l, hl, hu⟩ := iteratedLift_universal s g A B Z w h hh
    refine ⟨l, ⟨?_, hl.2⟩, ?_⟩
    · rw [← hl.1]
      exact IsHomLift.map _ _
    · intro l' hl'
      let := hl'.1
      exact hu l' ⟨(IsHomLift.eq_of_isHomLift iteratedSecondProjection w l').symm, hl'.2⟩

/-- Every base arrow has a genuine strongly cocartesian lift in the iterated
localization, with strict target equality. -/
theorem exists_iteratedSecondProjectionLift (A : Localization C (Localization C D))
    (Y : ActionLocalization C D) (g : iteratedSecondProjection.obj A ⟶ Y) :
    ∃ (B : Localization C (Localization C D)) (f : A ⟶ B),
      iteratedSecondProjection.obj B = Y ∧
        iteratedSecondProjection.IsStronglyCocartesian g f := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective A.obj.2.obj.2 Y.obj g
  refine ⟨⟨(A.obj.1, ⟨(r.denom ⊗ A.obj.2.obj.1, Y.obj)⟩)⟩,
    iteratedLift r.denom r.map A.obj.1 A.obj.2.obj.1, rfl, ?_⟩
  rw [← iteratedSecondProjection_iteratedLift r.denom r.map A.obj.1 A.obj.2.obj.1]
  infer_instance

end Cocartesian
end CategoryTheory.GroupCompletion.Localization
