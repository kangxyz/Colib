/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.Cylinder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Homotopy extension and continuous cylinder coordinates
-/
/-! Implementation provenance: adapted from the matching Quillen file at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual cylinder and HEP data are unchanged;
the separate continuous-coordinate conversion entry point is omitted.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat

/-- The homotopy extension property for a map of topological spaces. -/
def HomotopyExtensionProperty {A B : TopCat.{u}} (i : A ⟶ B) : Prop :=
  ∀ (Z : TopCat.{u}) (f : B ⟶ Z) (H : A ⊗ TopCat.I ⟶ Z),
    TopCat.ι₀ ≫ H = i ≫ f →
    ∃ K : B ⊗ TopCat.I ⟶ Z,
      TopCat.ι₀ ≫ K = f ∧ (i ▷ TopCat.I) ≫ K = H

/-- Isomorphisms have the homotopy extension property. -/
theorem homotopyExtensionProperty_of_isIso {A B : TopCat.{u}}
    (i : A ⟶ B) [IsIso i] : TopCat.HomotopyExtensionProperty i := by
  intro Z f H h
  refine ⟨(inv i ▷ TopCat.I) ≫ H, ?_, ?_⟩
  · rw [← Category.assoc, TopCat.ι₀_comp, Category.assoc, h]
    simp
  · rw [← Category.assoc, ← comp_whiskerRight]
    simp

/-- A composite of maps with the homotopy extension property has that property. -/
theorem homotopyExtensionProperty_comp {A B C : TopCat.{u}}
    {i : A ⟶ B} {j : B ⟶ C}
    (hi : TopCat.HomotopyExtensionProperty i) (hj : TopCat.HomotopyExtensionProperty j) :
    TopCat.HomotopyExtensionProperty (i ≫ j) := by
  intro Z f H h
  obtain ⟨K, hK₀, hK⟩ := hi Z (j ≫ f) H (by simpa only [Category.assoc] using h)
  obtain ⟨L, hL₀, hL⟩ := hj Z f K hK₀
  refine ⟨L, hL₀, ?_⟩
  rw [comp_whiskerRight, Category.assoc, hL, hK]

/-- Cobase change along an arbitrary continuous map preserves the homotopy
extension property. This uses the universal property of the actual topological
pushout, not any extra compatibility hypothesis about an extension. -/
theorem homotopyExtensionProperty_pushout {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (hi : TopCat.HomotopyExtensionProperty i) :
    TopCat.HomotopyExtensionProperty j := by
  intro Z k H h
  have hstart : TopCat.ι₀ ≫ (f ▷ TopCat.I) ≫ H = i ≫ g ≫ k := by
    rw [← Category.assoc, TopCat.ι₀_comp, Category.assoc, h, ← Category.assoc,
      ← sq.w, Category.assoc]
  obtain ⟨K, hK₀, hK⟩ := hi Z (g ≫ k) ((f ▷ TopCat.I) ≫ H) hstart
  have sqI : IsPushout (i ▷ TopCat.I) (f ▷ TopCat.I)
      (g ▷ TopCat.I) (j ▷ TopCat.I) := sq.map (tensorRight TopCat.I)
  let L := sqI.desc K H hK
  have hgL : (g ▷ TopCat.I) ≫ L = K := sqI.inl_desc K H hK
  have hjL : (j ▷ TopCat.I) ≫ L = H := sqI.inr_desc K H hK
  refine ⟨L, ?_, hjL⟩
  apply sq.hom_ext
  · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hgL, hK₀]
  · rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hjL, h]

/-- HEP in categorical cylinder coordinates also gives extensions in ordinary
continuous-map coordinates, including an arbitrary compact-open target. -/
theorem homotopyExtensionProperty_continuous {A B : TopCat.{u}} {i : A ⟶ B}
    (hi : TopCat.HomotopyExtensionProperty i) (Z : TopCat.{u})
    (f : C(B, Z)) (H : C(unitInterval × A, Z))
    (hzero : ∀ a, H (0, a) = f (i a)) :
    ∃ K : C(unitInterval × B, Z), (∀ b, K (0, b) = f b) ∧
      ∀ t a, K (t, i a) = H (t, a) := by
  let H' : A ⊗ TopCat.I ⟶ Z := TopCat.ofHom
    ⟨fun p ↦ H (p.2.down, p.1), H.continuous.comp
      ((continuous_uliftDown.comp continuous_snd).prodMk continuous_fst)⟩
  obtain ⟨K, hK₀, hK⟩ := hi Z (TopCat.ofHom f) H' (by ext a; exact hzero a)
  refine ⟨⟨fun p ↦ K (p.2, ULift.up p.1), K.hom.continuous.comp
    (continuous_snd.prodMk (continuous_uliftUp.comp continuous_fst))⟩, ?_, ?_⟩
  · intro b
    exact ConcreteCategory.congr_hom hK₀ b
  · intro t a
    exact ConcreteCategory.congr_hom hK (a, ULift.up t)


/-- Homotopy extension is invariant under an isomorphism of arrows. -/
theorem homotopyExtensionProperty_of_iso_square
    {A B C D : TopCat.{u}} (i : A ⟶ B) (j : C ⟶ D)
    (eA : A ≅ C) (eB : B ≅ D) (h : i ≫ eB.hom = eA.hom ≫ j)
    (hj : TopCat.HomotopyExtensionProperty j) : TopCat.HomotopyExtensionProperty i := by
  have hi : i = eA.hom ≫ j ≫ eB.inv := by
    rw [← Category.assoc, ← h]
    simp
  rw [hi]
  exact TopCat.homotopyExtensionProperty_comp (TopCat.homotopyExtensionProperty_of_isIso eA.hom)
    (TopCat.homotopyExtensionProperty_comp hj (TopCat.homotopyExtensionProperty_of_isIso eB.inv))

end TopCat
