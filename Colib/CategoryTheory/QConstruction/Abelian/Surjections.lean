/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.QConstruction.Abelian.ArrowLayers
public import Colib.CategoryTheory.ExactCategory.Functor.QConstruction
public import StacksCore.CategoryTheory.Abelian.CommSq

/-!
# Actual abelian Q-arrows: Surjections

Adapted from `Quillen/CategoryTheory/QConstruction/Abelian/Surjections.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual span maps,
universes and epi/mono hypotheses are retained. Bicartesian implications
use Stacks 08N4 directly.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.QConstruction
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Surjective Q-arrows have the whole target as upper endpoint. -/
def IsSurjection {X Y : C}
    (f : of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y) : Prop :=
  arrowUpper f = ⊤

@[simp]
theorem isSurjection_mkHom_iff {X Y : C} (s : AbelianSpan X Y) :
    IsSurjection (mkHom _ _ s) ↔ IsIso s.r :=
  (Subobject.isIso_iff_mk_eq_top s.r).symm

/-- Reverse an ordinary epimorphism to obtain its actual Q-arrow. -/
def surjectionArrow {X Y : C} (p : Y ⟶ X) [Epi p] :
    of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y :=
  mkHom _ _ ⟨Y, p, 𝟙 Y, (abelianExactStructure_deflation_iff C p).2 inferInstance,
    (abelianExactStructure_inflation_iff C _).2 inferInstance⟩

@[simp]
theorem isSurjection_surjectionArrow {X Y : C} (p : Y ⟶ X) [Epi p] :
    IsSurjection (surjectionArrow p) := Subobject.mk_eq_top_of_isIso _

/-- A monomorphism gives the identity-left-leg Q-arrow. -/
def inflationArrow {X Y : C} (i : X ⟶ Y) [Mono i] :
    of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y :=
  mkHom _ _ ⟨X, 𝟙 X, i, (abelianExactStructure_deflation_iff C _).2 inferInstance,
    (abelianExactStructure_inflation_iff C i).2 inferInstance⟩

/-- Surjective Q-arrows are precisely reversals of actual epimorphisms. -/
theorem isSurjection_iff_exists_epi {X Y : C}
    (f : of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y) :
    IsSurjection f ↔ ∃ (p : Y ⟶ X) (_ : Epi p), surjectionArrow p = f := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  change AbelianSpan X Y at s
  constructor
  · intro h
    have := (isSurjection_mkHom_iff s).1 h
    let p := inv s.r ≫ s.l
    refine ⟨p, inferInstance, ?_⟩
    symm
    apply mkHom_eq_of_apexIso _ _ s _ (asIso s.r)
    · simp [p]
    · simp
  · rintro ⟨p, hp, h⟩
    rw [← h]
    exact isSurjection_surjectionArrow p

/-- Surjective Q-arrows are closed under composition. -/
theorem IsSurjection.comp {X Y Z : C}
    {f : of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y}
    {g : of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Z}
    (hf : IsSurjection f) (hg : IsSurjection g) : IsSurjection (f ≫ g) := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  obtain ⟨t, rfl⟩ := Quotient.exists_rep g
  have := (isSurjection_mkHom_iff s).1 hf
  have := (isSurjection_mkHom_iff t).1 hg
  have : IsIso (pullback.snd s.r t.l) := (IsPullback.of_hasPullback s.r t.l).isIso_snd_of_isIso
  apply (isSurjection_mkHom_iff (Span.comp s t)).2
  change IsIso (pullback.snd s.r t.l ≫ t.r)
  infer_instance

/-- If a composite Q-arrow is surjective, both factors are surjective. -/
theorem IsSurjection.of_comp {X Y Z : C}
    {f : of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y}
    {g : of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Z}
    (h : IsSurjection (f ≫ g)) : IsSurjection f ∧ IsSurjection g := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  obtain ⟨t, rfl⟩ := Quotient.exists_rep g
  have hR : IsIso (pullback.snd s.r t.l ≫ t.r) := (isSurjection_mkHom_iff (Span.comp s t)).1 h
  have : Epi t.r := epi_of_epi_fac (rfl : pullback.snd s.r t.l ≫ t.r = _)
  have ht : IsIso t.r := isIso_of_mono_of_epi _
  have : IsIso (pullback.snd s.r t.l) := IsIso.of_isIso_comp_right _ t.r
  have : Epi (pullback.fst s.r t.l ≫ s.r) := by rw [pullback.condition]; infer_instance
  have : Epi s.r := epi_of_epi_fac (rfl : pullback.fst s.r t.l ≫ s.r = _)
  exact ⟨(isSurjection_mkHom_iff s).2 (isIso_of_mono_of_epi _), (isSurjection_mkHom_iff t).2 ht⟩

/-- The upper endpoint determines a Q-arrow from any original zero object. -/
theorem arrowUpper_injective_of_isZero {X Y : C} (hX : IsZero X) :
    Function.Injective (arrowUpper (C := C) (X := X) (M := Y)) := by
  intro f g h
  let e := (isZero_zero C).iso hX
  apply (cancel_epi ((abelianExactStructure C).qIsoOfIso e).hom).1
  apply zeroArrowSubobject_injective
  change arrowUpper (((abelianExactStructure C).qIsoOfIso e).hom ≫ f) =
    arrowUpper (((abelianExactStructure C).qIsoOfIso e).hom ≫ g)
  simpa only [arrowUpper_comp_iso] using h

/-- Exact functors preserve surjective Q-arrows, directly on their span legs. -/
theorem IsSurjection.mapQ {D : Type u} [Category.{v} D] [Abelian D]
    (F : ExactCategory.ExactFunctor (abelianExactStructure C) (abelianExactStructure D))
    {X Y : C}
    {f : of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y}
    (hf : IsSurjection f) : IsSurjection (F.mapQ.map f) := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  have := (isSurjection_mkHom_iff s).1 hf
  apply (isSurjection_mkHom_iff (F.toQCompatibleFunctor.mapSpan s)).2
  change IsIso (F.toFunctor.map s.r)
  infer_instance

/-- An exact functor reflecting ambient isomorphisms reflects surjective Q-arrows. -/
theorem isSurjection_mapQ_iff {D : Type u} [Category.{v} D] [Abelian D]
    (F : ExactCategory.ExactFunctor (abelianExactStructure C) (abelianExactStructure D))
    [F.toFunctor.ReflectsIsomorphisms] {X Y : C}
    (f : of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y) :
    IsSurjection (F.mapQ.map f) ↔ IsSurjection f := by
  constructor
  · obtain ⟨s, rfl⟩ := Quotient.exists_rep f
    intro h
    have : IsIso (F.toFunctor.map s.r) :=
      (isSurjection_mkHom_iff (F.toQCompatibleFunctor.mapSpan s)).1 h
    exact (isSurjection_mkHom_iff s).2 (isIso_of_reflects_iso s.r F.toFunctor)
  · exact IsSurjection.mapQ F

/-- The ordinary pushout cospan represents the same Q-arrow as the original span. -/
theorem span_cospan_factorization {X Y : C} (s : AbelianSpan X Y) :
    inflationArrow (pushout.inl s.l s.r) ≫ surjectionArrow (pushout.inr s.l s.r) =
      mkHom _ _ s := by
  let sq := (CommSq.IsPushout.mono_to_isPullback (IsPushout.of_hasPushout s.l s.r).flip).1.flip
  symm
  apply mkHom_eq_of_apexIso _ _ s _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst (pushout.inl s.l s.r)
      (pushout.inr s.l s.r) ≫ 𝟙 X = s.l
    simp
  · change sq.isoPullback.hom ≫ pullback.snd (pushout.inl s.l s.r)
      (pushout.inr s.l s.r) ≫ 𝟙 Y = s.r
    simp
end CategoryTheory.QConstruction
