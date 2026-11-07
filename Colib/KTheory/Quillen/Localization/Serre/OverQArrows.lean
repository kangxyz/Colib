/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Uses native Q-construction and intrinsic abelian full-subcategory exact structure. -/

public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryKernel
public import Colib.CategoryTheory.QConstruction.Abelian.CospanComposition
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion

/-! # Ordinary mono and reversed epi arrows in the auxiliary Q-category -/
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

/-- The Q-arrow of an ordinary monomorphism over the fixed quotient. -/
def overInflationArrow {N : C} {X Y : Over N} (i : X ⟶ Y) [Mono i.left] :
    QConstruction.of (overDeflation N) (overInflation N) X ⟶ QConstruction.of _ _ Y :=
  QConstruction.mkHom _ _ ⟨X, 𝟙 X, i,
    by change Epi (𝟙 X.left); infer_instance, inferInstanceAs (Mono i.left)⟩

/-- The Q-arrow reversing an ordinary epimorphism over the fixed quotient. -/
def overSurjectionArrow {N : C} {X Y : Over N} (p : Y ⟶ X) [Epi p.left] :
    QConstruction.of (overDeflation N) (overInflation N) X ⟶ QConstruction.of _ _ Y :=
  QConstruction.mkHom _ _ ⟨Y, p, 𝟙 Y, inferInstanceAs (Epi p.left),
    by change Mono (𝟙 Y.left); infer_instance⟩

@[simp]
lemma overForgetQ_inflationArrow {N : C} {X Y : Over N} (i : X ⟶ Y) [Mono i.left] :
    (overForgetQ N).map (overInflationArrow i) = QConstruction.inflationArrow i.left := rfl

@[simp]
lemma overForgetQ_surjectionArrow {N : C} {X Y : Over N} (p : Y ⟶ X) [Epi p.left] :
    (overForgetQ N).map (overSurjectionArrow p) = QConstruction.surjectionArrow p.left := rfl

instance overKernel_map_epi {N : C} {X Y : Over N} (p : X ⟶ Y) [Epi p.left] :
    Epi ((overKernel N).map p) :=
  MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
    (overKernel_map_isPullback p).flip (inferInstanceAs (Epi p.left))

instance overKernel_map_mono {N : C} {X Y : Over N} (i : X ⟶ Y) [Mono i.left] :
    Mono ((overKernel N).map i) :=
  MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms C)
    (overKernel_map_isPullback i).flip (inferInstanceAs (Mono i.left))

@[simp]
lemma overKernelQ_inflationArrow {N : C} {X Y : Over N} (i : X ⟶ Y) [Mono i.left] :
    (overKernelQ N).map (overInflationArrow i) = QConstruction.inflationArrow ((overKernel N).map
      i) := by
  change QConstruction.mkHom _ _ ((overKernelCompatible N).mapSpan _) = QConstruction.mkHom _ _ _
  refine QConstruction.mkHom_eq_of_apexIso _ _ _ _ (Iso.refl ((overKernel N).obj X)) ?_ ?_
  · simp [QConstruction.CompatibleFunctor.mapSpan, overKernelCompatible,
    QConstruction.CompatibleFunctor.ofPreservesPullbacks]
  · simp [QConstruction.CompatibleFunctor.mapSpan, overKernelCompatible,
    QConstruction.CompatibleFunctor.ofPreservesPullbacks]

@[simp]
lemma overKernelQ_surjectionArrow {N : C} {X Y : Over N} (p : Y ⟶ X) [Epi p.left] :
    (overKernelQ N).map (overSurjectionArrow p) = QConstruction.surjectionArrow ((overKernel
      N).map p) := by
  change QConstruction.mkHom _ _ ((overKernelCompatible N).mapSpan _) = QConstruction.mkHom _ _ _
  refine QConstruction.mkHom_eq_of_apexIso _ _ _ _ (Iso.refl ((overKernel N).obj Y)) ?_ ?_
  · simp [QConstruction.CompatibleFunctor.mapSpan, overKernelCompatible,
    QConstruction.CompatibleFunctor.ofPreservesPullbacks]
  · simp [QConstruction.CompatibleFunctor.mapSpan, overKernelCompatible,
    QConstruction.CompatibleFunctor.ofPreservesPullbacks]

/-- Surjectivity on kernels forces a span between epimorphic objects to be
an actual reversed epimorphism over the base. -/
theorem overQ_exists_epi_of_kernel_surjection {N : C} {X Y : Over N}
    [Epi X.hom] [Epi Y.hom]
    (f : QConstruction.of (overDeflation N) (overInflation N) X ⟶ QConstruction.of _ _ Y)
    (hf : QConstruction.IsSurjection ((overKernelQ N).map f)) :
    ∃ (p : Y ⟶ X) (_ : Epi p.left), overSurjectionArrow p = f := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  change Span (overDeflation N) (overInflation N) X Y at s
  have hk : IsIso ((overKernel N).map s.r) :=
    (QConstruction.isSurjection_mkHom_iff ((overKernelCompatible N).mapSpan s)).1 hf
  have hl : Epi s.l.left := s.wl
  have hr : Mono s.r.left := s.wr
  have : Epi s.apex.hom := by rw [← Over.w s.l]; infer_instance
  have : IsIso s.r := over_isIso_of_mono_of_kernel_isIso s.r
  have : IsIso s.r.left := inferInstanceAs (IsIso ((Over.forget N).map s.r))
  let p := inv s.r ≫ s.l
  have hp : Epi p.left := by
    change Epi ((Over.forget N).map (inv s.r ≫ s.l))
    rw [Functor.map_comp, Functor.map_inv]
    change Epi (inv s.r.left ≫ s.l.left)
    infer_instance
  refine ⟨p, hp, ?_⟩
  symm
  apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ (asIso s.r)
  · simp [p]
  · simp

/-- Reversed epis retain their underlying ordinary arrow. -/
theorem overSurjectionArrow_injective {N : C} {X Y : Over N} (p q : Y ⟶ X)
    [Epi p.left] [Epi q.left] (h : overSurjectionArrow p = overSurjectionArrow q) : p = q := by
  apply Over.OverMorphism.ext
  exact QConstruction.surjectionArrow_injective p.left q.left (congrArg ((overForgetQ N).map) h)

end CategoryTheory.ExactCategory.SerreLocalization
