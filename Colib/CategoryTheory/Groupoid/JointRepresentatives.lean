/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Mathlib.CategoryTheory.Localization.Construction

/-!
# Joint Representatives

A single graph representative retains BOTH the decoded morphism and its
original ambient comparison image, with exact endpoint identifications.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe u₁ v₁ u₂ v₂ u₃ v₃
namespace CategoryTheory.Groupoid.JointRepresentation
variable {A : Type u₁} [Groupoid.{v₁} A] {B : Type u₂} [Groupoid.{v₂} B]
    {D : Type u₃} [Groupoid.{v₃} D]
    (F : A ⥤ B) (H : A ⥤ D) (L : B ⥤ D) (s : B → A)
    (τ : ∀ b, F.obj (s b) ≅ b) (σ : ∀ b, H.obj (s b) ≅ L.obj b)

/-- A single graph representative retains BOTH the decoded morphism and its
original ambient comparison image, with exact endpoint identifications. -/
def jointProperty : MorphismProperty B := fun x y f =>
  ∃ a : s x ⟶ s y,
    F.map a = (τ x).hom ≫ f ≫ (τ y).inv ∧
      H.map a = (σ x).hom ≫ L.map f ≫ (σ y).inv

/-- Joint representatives compose using the same actual intermediate graph object. -/
instance jointProperty_comp : (jointProperty F H L s τ σ).IsStableUnderComposition where
  comp_mem := by
    intro x y z f g hf hg
    obtain ⟨a, ha, ha'⟩ := hf
    obtain ⟨b, hb, hb'⟩ := hg
    refine ⟨a ≫ b, ?_, ?_⟩
    · rw [F.map_comp, ha, hb]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · rw [H.map_comp, ha', hb', L.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Joint representatives are closed under actual inverse morphisms. -/
theorem jointProperty_inv {x y : B} (e : x ≅ y)
    (he : jointProperty F H L s τ σ e.hom) : jointProperty F H L s τ σ e.inv := by
  obtain ⟨a, ha, ha'⟩ := he
  refine ⟨CategoryTheory.inv a, ?_, ?_⟩
  · apply (cancel_epi (F.map a)).mp
    rw [← F.map_comp]
    simp only [IsIso.hom_inv_id, F.map_id]
    rw [ha]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id]
  · apply (cancel_epi (H.map a)).mp
    rw [← H.map_comp]
    simp only [IsIso.hom_inv_id, H.map_id]
    rw [ha']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← L.map_comp_assoc, e.hom_inv_id, L.map_id]
    simp

/-- If the ambient functor distinguishes decoder values of parallel graph
morphisms, joint representatives make the ORIGINAL comparison injective. -/
theorem map_injective_of_joint
    (hrep : ∀ {x y : B} (f : x ⟶ y), jointProperty F H L s τ σ f)
    (href : ∀ {x y : A} (a b : x ⟶ y), H.map a = H.map b → F.map a = F.map b)
    (x y : B) : Function.Injective (L.map : (x ⟶ y) → (L.obj x ⟶ L.obj y)) := by
  intro f g hfg
  obtain ⟨a, ha, ha'⟩ := hrep f
  obtain ⟨b, hb, hb'⟩ := hrep g
  have hab : H.map a = H.map b := by rw [ha', hb', hfg]
  have hd := href a b hab
  rw [ha, hb] at hd
  exact (cancel_epi (τ x).hom).mp ((cancel_mono (τ y).inv).mp (by
    simpa only [Category.assoc] using hd))

end CategoryTheory.Groupoid.JointRepresentation
