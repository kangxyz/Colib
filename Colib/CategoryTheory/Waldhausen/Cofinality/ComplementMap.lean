/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Cofinality.DenseGrading
public import Colib.CategoryTheory.Waldhausen.Cofinality.GradingFunctor

/-! # Actual complement classes under exact functors
Implementation provenance: `Quillen/Waldhausen/Cofinality/ComplementMap.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v u' v' w
namespace CategoryTheory.Waldhausen.Cofinality

namespace DenseCofiberData
variable {C : Type u} [Category.{v} C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)
  {G : Type w} [AddCommGroup G] (d : Grading W G)
  (hz : ∀ A, P A → d.value A = 0)

lemma grading_coprod (A B : C) : d.value (A ⨿ B) = d.value A + d.value B := by
  rw [d.pushout (W.cof_zero A) (Additivity.coprod_isPushout W A B), d.zero, sub_zero]

/-- Common complements, rather than a K-zero presentation, make every
membership-vanishing original grading descend to actual complement classes. -/
def liftGrading : h.Classes →+ G where
  toFun := _root_.Quotient.lift d.value (by
    intro A B hAB
    obtain ⟨Z,hAZ,hBZ⟩ := hAB
    have ha := hz _ hAZ
    have hb := hz _ hBZ
    rw [grading_coprod d A Z] at ha
    rw [grading_coprod d B Z] at hb
    exact add_right_cancel (ha.trans hb.symm))
  map_zero' := d.zero
  map_add' a b := Quotient.inductionOn₂ a b (fun A B ↦ grading_coprod d A B)

@[simp] theorem liftGrading_classOf (A : C) : h.liftGrading d hz (h.classOf A) = d.value A := rfl

/-- The exact zero criterion and actual object representatives prove injectivity. -/
theorem liftGrading_injective (hreflect : ∀ A, d.value A = 0 → P A) :
    Function.Injective (h.liftGrading d hz) := by
  apply (injective_iff_map_eq_zero (h.liftGrading d hz)).mpr
  intro a ha
  obtain ⟨A,rfl⟩ := h.classOf_surjective a
  exact (h.classOf_eq_zero_iff A).mpr (hreflect A ha)

section Functor
variable {D : Type u'} [Category.{v'} D] {V : Structure D} [HasBinaryCoproducts D]
  {Q : ObjectProperty D} (k : DenseCofiberData V Q) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F) (hp : ∀ A, P A → Q (F.obj A))

/-- The original exact functor induces the actual common-complement class map. -/
def classMap : h.Classes →+ k.Classes :=
  h.liftGrading (k.grading.comap hF) (fun A hA ↦ (k.classOf_eq_zero_iff _).mpr (hp A hA))

@[simp] theorem classMap_classOf (A : C) :
    h.classMap k hF hp (h.classOf A) = k.classOf (F.obj A) := rfl

/-- Exact membership reflection, not an object presentation of K-zero,
proves injectivity of the actual complement obstruction. -/
theorem classMap_injective (hback : ∀ A, Q (F.obj A) → P A) :
    Function.Injective (h.classMap k hF hp) :=
  h.liftGrading_injective _ _ (fun A ha ↦ hback A ((k.classOf_eq_zero_iff _).mp ha))

end Functor
end DenseCofiberData
end CategoryTheory.Waldhausen.Cofinality
