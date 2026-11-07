/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Uses native Q-construction and intrinsic abelian full-subcategory exact structure. -/

public import Colib.KTheory.Quillen.Localization.Serre.KernelPushoutComparison
public import Colib.KTheory.Quillen.Localization.Serre.OverQArrows
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion

/-!
# Uniqueness for the kernel-pushout reflection

An ordinary extension pushout detects a Q-arrow to an epimorphic extension
once its composite with the old extension and its surjective kernel arrow
are fixed. This is the uniqueness part of the kernel-comma reflection.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.SerreLocalization

open CategoryTheory.Abelian.SerreLocalization CategoryTheory.Abelian
attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{u} C] [Abelian C]

/-- An extension pushout detects Q-arrows with a fixed surjective kernel map. -/
theorem overQ_hom_ext_of_kernel_and_inflation {N : C} {X R Y : Over N}
    [Epi X.hom] [Epi R.hom] [Epi Y.hom] (α : X ⟶ R) [Mono α.left]
    (g₁ g₂ : QConstruction.of (overDeflation N) (overInflation N) R ⟶ QConstruction.of _ _ Y)
    (hα : overInflationArrow α ≫ g₁ = overInflationArrow α ≫ g₂)
    (h₁ : QConstruction.IsSurjection ((overKernelQ N).map g₁))
    (h₂ : QConstruction.IsSurjection ((overKernelQ N).map g₂))
    (hk : (overKernelQ N).map g₁ = (overKernelQ N).map g₂) : g₁ = g₂ := by
  obtain ⟨p₁, hp₁, rfl⟩ := overQ_exists_epi_of_kernel_surjection g₁ h₁
  obtain ⟨p₂, hp₂, rfl⟩ := overQ_exists_epi_of_kernel_surjection g₂ h₂
  have hkp : (overKernel N).map p₁ = (overKernel N).map p₂ := by
    apply QConstruction.surjectionArrow_injective
    simpa using hk
  have ha : QConstruction.inflationArrow α.left ≫ QConstruction.surjectionArrow p₁.left =
      QConstruction.inflationArrow α.left ≫ QConstruction.surjectionArrow p₂.left := by
    simpa using congrArg ((overForgetQ N).map) hα
  obtain ⟨e, heα, hep⟩ := QConstruction.exists_cospanIso_of_eq α.left p₁.left α.left p₂.left ha
  have heN : e.hom ≫ R.hom = R.hom := by
    apply (cancel_epi p₁.left).1
    rw [← Category.assoc, hep, Over.w p₂, Over.w p₁]
  let e' : R ≅ R := Over.isoMk e heN
  have he'p : p₁ ≫ e'.hom = p₂ := by
    apply Over.OverMorphism.ext
    exact hep
  have hek : (overKernel N).map e'.hom = 𝟙 _ := by
    apply (cancel_epi ((overKernel N).map p₁)).1
    rw [← Functor.map_comp, he'p, Category.comp_id, hkp]
  have heid : e.hom = 𝟙 R.left := by
    apply (overKernel_mono_isPushout α).hom_ext
    · simpa using heα
    · have h := (overKernel_map_isPullback e'.hom).w
      rw [hek, Category.id_comp] at h
      simpa [e'] using h.symm
  have hp : p₁ = p₂ := by
    apply Over.OverMorphism.ext
    simpa [heid] using hep
  cases hp
  rfl

/-- The two kernel-comma triangles give the kernel equality and surjectivity
needed for uniqueness after an extension pushout. -/
theorem overQ_hom_ext_of_kernel_triangles {N : C} {X R Y : Over N}
    [Epi X.hom] [Epi R.hom] [Epi Y.hom] (α : X ⟶ R) [Mono α.left]
    {T : C} (q : T ⟶ (overKernel N).obj Y) (p : T ⟶ (overKernel N).obj R)
    [Epi q] [Epi p]
    (g₁ g₂ : QConstruction.of (overDeflation N) (overInflation N) R ⟶ QConstruction.of _ _ Y)
    (hα : overInflationArrow α ≫ g₁ = overInflationArrow α ≫ g₂)
    (h₁ : (overKernelQ N).map g₁ ≫ QConstruction.surjectionArrow q = QConstruction.surjectionArrow
      p)
    (h₂ : (overKernelQ N).map g₂ ≫ QConstruction.surjectionArrow q = QConstruction.surjectionArrow
      p) :
    g₁ = g₂ := by
  apply overQ_hom_ext_of_kernel_and_inflation α g₁ g₂ hα
  · apply (QConstruction.IsSurjection.of_comp (f := (overKernelQ N).map g₁) (g :=
    QConstruction.surjectionArrow q) ?_).1
    rw [h₁]
    exact QConstruction.isSurjection_surjectionArrow p
  · apply (QConstruction.IsSurjection.of_comp (f := (overKernelQ N).map g₂) (g :=
    QConstruction.surjectionArrow q) ?_).1
    rw [h₂]
    exact QConstruction.isSurjection_surjectionArrow p
  · exact (cancel_mono (QConstruction.surjectionArrow q)).1 (h₁.trans h₂.symm)

end CategoryTheory.ExactCategory.SerreLocalization
