/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Functor.Basic

/-!
Implementation provenance: `Quillen/Aglib/CategoryTheory/Localization/CharacterExtension.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Extending groupoid-valued characters by common right squares

The cancellation hypothesis concerns the character, not the original category.
In particular, this construction does not assert an Ore cancellation property.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v u' v' w w'
namespace CategoryTheory.Localization.CharacterExtension
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} {U : Type u'} {D : Type w}
  [Category.{v} C] [Category.{v'} U] [Groupoid.{w'} D]
variable (I : U ⥤ C) (F : U ⥤ D)

/-- A common right square whose apex and outgoing arrows lie in the character domain. -/
structure Square {X : C} {Y Z : U} (f : X ⟶ I.obj Y) (g : X ⟶ I.obj Z) where
  /-- The apex lies in the original character domain. -/
  apex : U
  /-- The left leg is an arrow in the original character domain. -/
  left : Y ⟶ apex
  /-- The right leg is an arrow in the original character domain. -/
  right : Z ⟶ apex
  comm : f ≫ I.map left = g ≫ I.map right

/-- The fraction evaluated in the original groupoid-valued character. -/
def Square.value {X : C} {Y Z : U} {f : X ⟶ I.obj Y} {g : X ⟶ I.obj Z}
    (s : Square I f g) : F.obj Y ⟶ F.obj Z := F.map s.left ≫ inv (F.map s.right)

variable (hsquare : ∀ {X : C} {Y Z : U} (f : X ⟶ I.obj Y) (g : X ⟶ I.obj Z),
    Nonempty (Square I f g))
variable (hcancel : ∀ {X : C} {Y Z : U} (r : X ⟶ I.obj Y) (f g : Y ⟶ Z),
    r ≫ I.map f = r ≫ I.map g → F.map f = F.map g)

include hsquare hcancel in
/-- Every choice of common square has the same character value. -/
theorem Square.value_eq {X : C} {Y Z : U} {f : X ⟶ I.obj Y} {g : X ⟶ I.obj Z}
    (s t : Square I f g) : Square.value I F s = Square.value I F t := by
  obtain ⟨c⟩ := hsquare (I.map s.left) (I.map t.left)
  have hleft : F.map (s.left ≫ c.left) = F.map (t.left ≫ c.right) := by
    apply hcancel (𝟙 _) _ _
    simpa only [Category.id_comp, I.map_comp] using c.comm
  have hright : F.map (s.right ≫ c.left) = F.map (t.right ≫ c.right) := by
    apply hcancel g _ _
    simp only [I.map_comp, ← Category.assoc]
    rw [← s.comm, ← t.comm]
    simpa only [Category.assoc] using congrArg (fun k => f ≫ k) c.comm
  dsimp [Square.value]
  apply (cancel_mono (F.map (s.right ≫ c.left))).1
  simp only [F.map_comp, Category.assoc] at hleft hright ⊢
  calc
    _ = F.map s.left ≫ F.map c.left := by simp
    _ = F.map t.left ≫ F.map c.right := hleft
    _ = _ := by rw [hright]; simp


/-- Evaluate any cospan through a chosen common right square. -/
def fraction {X : C} {Y Z : U} (f : X ⟶ I.obj Y) (g : X ⟶ I.obj Z) :
    F.obj Y ⟶ F.obj Z := Square.value I F (hsquare f g).some

include hcancel in
theorem fraction_eq {X : C} {Y Z : U} {f : X ⟶ I.obj Y} {g : X ⟶ I.obj Z}
    (s : Square I f g) : fraction I F hsquare f g = Square.value I F s :=
  Square.value_eq I F hsquare hcancel _ _

include hcancel in
theorem fraction_self {X : C} {Y : U} (f : X ⟶ I.obj Y) :
    fraction I F hsquare f f = 𝟙 (F.obj Y) := by
  rw [fraction_eq I F hsquare hcancel
    (⟨Y, 𝟙 Y, 𝟙 Y, rfl⟩ : Square I f f)]
  simp [Square.value]

include hcancel in
theorem fraction_comp {X : C} {Y Z W : U}
    (f : X ⟶ I.obj Y) (g : X ⟶ I.obj Z) (h : X ⟶ I.obj W) :
    fraction I F hsquare f g ≫ fraction I F hsquare g h = fraction I F hsquare f h := by
  let s := (hsquare f g).some
  let t := (hsquare g h).some
  let c := (hsquare (I.map s.right) (I.map t.left)).some
  have hc : F.map s.right ≫ F.map c.left = F.map t.left ≫ F.map c.right := by
    simpa only [F.map_comp] using hcancel (𝟙 _) (s.right ≫ c.left) (t.left ≫ c.right)
      (by simpa only [Category.id_comp, I.map_comp] using c.comm)
  let r : Square I f h :=
    { apex := c.apex
      left := s.left ≫ c.left
      right := t.right ≫ c.right
      comm := by
        simp only [I.map_comp, ← Category.assoc]
        rw [s.comm, ← t.comm]
        simpa only [Category.assoc] using congrArg (fun k => g ≫ k) c.comm }
  rw [fraction_eq I F hsquare hcancel s, fraction_eq I F hsquare hcancel t,
    fraction_eq I F hsquare hcancel r]
  dsimp [Square.value, r]
  apply (cancel_mono (F.map (t.right ≫ c.right))).1
  simp only [F.map_comp, Category.assoc]
  simp only [IsIso.inv_hom_id_assoc]
  rw [← hc]
  simp

include hcancel in
theorem fraction_precomp {X X' : C} {Y Z : U} (k : X' ⟶ X)
    (f : X ⟶ I.obj Y) (g : X ⟶ I.obj Z) :
    fraction I F hsquare (k ≫ f) (k ≫ g) = fraction I F hsquare f g := by
  let s := (hsquare f g).some
  let r : Square I (k ≫ f) (k ≫ g) :=
    { apex := s.apex
      left := s.left
      right := s.right
      comm := by simpa only [Category.assoc] using congrArg (fun a => k ≫ a) s.comm }
  rw [fraction_eq I F hsquare hcancel r]
  rfl

/-- Actual extension from chosen outgoing arrows, using only character-level cancellation. -/
def extension (obj : C → U) (arrow : ∀ X, X ⟶ I.obj (obj X)) : C ⥤ D where
  obj X := F.obj (obj X)
  map {X Y} f := fraction I F hsquare (arrow X) (f ≫ arrow Y)
  map_id X := by simp only [Category.id_comp, fraction_self I F hsquare hcancel]
  map_comp {X Y Z} f g := by
    rw [← fraction_precomp I F hsquare hcancel f (arrow Y) (g ≫ arrow Z)]
    simpa only [Category.assoc] using
      (fraction_comp I F hsquare hcancel (arrow X) (f ≫ arrow Y) (f ≫ g ≫ arrow Z)).symm

include hcancel in
theorem fraction_map {Y Z : U} (f : Y ⟶ Z) :
    fraction I F hsquare (𝟙 (I.obj Y)) (I.map f) = F.map f := by
  rw [fraction_eq I F hsquare hcancel
    (⟨Z, f, 𝟙 Z, by simp⟩ : Square I (𝟙 (I.obj Y)) (I.map f))]
  simp [Square.value]

/-- The extended functor agrees with the original character by its actual comparison fractions. -/
def extensionIso (obj : C → U) (arrow : ∀ X, X ⟶ I.obj (obj X)) :
    I ⋙ extension I F hsquare hcancel obj arrow ≅ F :=
  NatIso.ofComponents
    (fun Y => asIso (fraction I F hsquare (arrow (I.obj Y)) (𝟙 (I.obj Y)))) (by
      intro Y Z f
      change fraction I F hsquare (arrow (I.obj Y)) (I.map f ≫ arrow (I.obj Z)) ≫
          fraction I F hsquare (arrow (I.obj Z)) (𝟙 (I.obj Z)) =
        fraction I F hsquare (arrow (I.obj Y)) (𝟙 (I.obj Y)) ≫ F.map f
      rw [← fraction_precomp I F hsquare hcancel (I.map f) (arrow (I.obj Z)) (𝟙 (I.obj Z))]
      simp only [Category.comp_id]
      rw [fraction_comp I F hsquare hcancel]
      rw [← fraction_map I F hsquare hcancel f]
      exact (fraction_comp I F hsquare hcancel _ _ _).symm)

end CategoryTheory.Localization.CharacterExtension
