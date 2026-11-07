/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Abelian.Devissage.Filtration
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite image filtrations for nilpotent central endomorphisms

For a natural endomorphism `t` of the identity of an abelian category, the
objects annihilated by `t` contain zero and are closed under subobjects,
quotients and finite products. A nilpotent component has an actual finite
admissible filtration with annihilated factors, obtained recursively from
its image inclusion and cokernel. Objectwise nilpotence suffices; neither
extension closure nor a uniform bound on the filtration lengths is assumed.

## Implementation provenance

Adapted from lines 41–143 of
`Quillen/Aglib/CategoryTheory/ExactCategory/Filtration/CentralEndomorphism.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native Mathlib category, images, cokernels and zero objects, and Colib's
actual `ExactStructure.Filtration` and standard abelian exact structure are
retained. The finite tower is exposed as data as well as an existence theorem.
-/
@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

namespace CategoryTheory.Abelian.Devissage.CentralEndomorphism

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Objects annihilated by a natural central endomorphism. -/
def killed (t : 𝟭 C ⟶ 𝟭 C) : ObjectProperty C := fun X ↦ t.app X = 0

variable (t : 𝟭 C ⟶ 𝟭 C)

instance killed_containsZero : (killed t).ContainsZero :=
  ⟨⟨0, isZero_zero C, (isZero_zero C).eq_of_src _ _⟩⟩

instance killed_subobjects : (killed t).IsClosedUnderSubobjects where
  prop_of_mono {X Y} i _ h := by
    change t.app Y = 0 at h
    change t.app X = 0
    apply (cancel_mono i).1
    simpa only [Functor.id_map, h, comp_zero, zero_comp] using (t.naturality i).symm

instance killed_quotients : (killed t).IsClosedUnderQuotients where
  prop_of_epi {X Y} p _ h := by
    change t.app X = 0 at h
    change t.app Y = 0
    apply (cancel_epi p).1
    simpa only [Functor.id_map, h, comp_zero, zero_comp] using t.naturality p

instance killed_finiteProducts : (killed t).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := {
    limitsOfShape_le := by
      rintro X ⟨p⟩
      change t.app X = 0
      apply p.isLimit.hom_ext
      intro j
      have h : t.app (p.diag.obj j) = 0 := p.prop_diag_obj j
      have hn := t.naturality (p.cone.π.app j)
      change p.cone.π.app j ≫ t.app (p.diag.obj j) =
        t.app X ≫ p.cone.π.app j at hn
      rw [h, comp_zero] at hn
      simpa only [zero_comp] using hn.symm }

/-- The iterated central endomorphism, viewed as an actual categorical arrow. -/
def power (X : C) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => t.app X ≫ power X n

omit [Abelian C] in
@[simp] lemma power_zero (X : C) : power t X 0 = 𝟙 X := rfl

omit [Abelian C] in
@[simp] lemma power_succ (X : C) (n : ℕ) :
    power t X (n + 1) = t.app X ≫ power t X n := rfl

omit [Abelian C] in
lemma power_naturality {X Y : C} (a : X ⟶ Y) (n : ℕ) :
    power t X n ≫ a = a ≫ power t Y n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [power_succ, Category.assoc]
    rw [ih, ← Category.assoc]
    have hn : t.app X ≫ a = a ≫ t.app Y := (t.naturality a).symm
    rw [hn, Category.assoc]

/-- Multiplication by `t` lowers its nilpotence exponent on its actual image. -/
lemma image_power_eq_zero (X : C) (n : ℕ) (h : power t X (n + 1) = 0) :
    power t (Limits.image (t.app X)) n = 0 := by
  apply (cancel_mono (Limits.image.ι (t.app X))).1
  apply (cancel_epi (Limits.factorThruImage (t.app X))).1
  simp only [zero_comp, comp_zero]
  rw [power_naturality, ← Category.assoc, Limits.image.fac]
  exact h

/-- The quotient by the actual image of `t` is killed by `t`. -/
lemma killed_cokernel_image (X : C) :
    killed t (cokernel (Limits.image.ι (t.app X))) := by
  change t.app _ = 0
  apply (cancel_epi (cokernel.π (Limits.image.ι (t.app X)))).1
  rw [comp_zero]
  have hn := t.naturality (cokernel.π (Limits.image.ι (t.app X)))
  change cokernel.π (Limits.image.ι (t.app X)) ≫ t.app _ =
    t.app X ≫ cokernel.π (Limits.image.ι (t.app X)) at hn
  apply hn.trans
  calc
    _ = (Limits.factorThruImage (t.app X) ≫ Limits.image.ι (t.app X)) ≫
        cokernel.π (Limits.image.ι (t.app X)) :=
      congrArg (fun a ↦ a ≫ cokernel.π (Limits.image.ι (t.app X))) (Limits.image.fac (t.app X)).symm
    _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]

/-- The actual finite image filtration. The successive conflations are the
image inclusions and their cokernels; each step lowers the nilpotence exponent. -/
def filtrationOfPowerEqZero (n : ℕ) (X : C) (h : power t X n = 0) :
    (abelianExactStructure C).Filtration (killed t) X := by
  induction n generalizing X with
  | zero =>
    exact .zero ((IsZero.iff_id_eq_zero X).2 (by simpa using h))
  | succ n ih =>
    let i := Limits.image.ι (t.app X)
    exact .step (ShortComplex.mk i (cokernel.π i) (cokernel.condition i))
      { exact := ShortComplex.cokernelSequence_exact i }
      (ih (Limits.image (t.app X)) (image_power_eq_zero t X n h)) (killed_cokernel_image t X)

/-- A specified annihilating exponent supplies a finite admissible filtration. -/
theorem filtration_of_power_eq_zero (n : ℕ) (X : C) (h : power t X n = 0) :
    Nonempty ((abelianExactStructure C).Filtration (killed t) X) :=
  ⟨filtrationOfPowerEqZero t n X h⟩

/-- Objectwise nilpotence supplies the complete classical dévissage hypothesis. -/
theorem filtrationHypothesis (h : ∀ X : C, ∃ n : ℕ, power t X n = 0) :
    Devissage.FiltrationHypothesis (killed t) := by
  intro X
  obtain ⟨n, hn⟩ := h X
  exact filtration_of_power_eq_zero t n X hn

end CategoryTheory.Abelian.Devissage.CentralEndomorphism
