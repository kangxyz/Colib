/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Cofiber

/-! # Weak cofibrations and actual acyclic cofibers

The extension axiom is a purely categorical condition on actual displayed
cofiber pushout squares. It does not contain a homotopy-fiber, realization,
or K-theoretic conclusion. Together with gluing, it characterizes a weak
cofibration by acyclicity of its actual cofiber. No cylinder or saturation
hypothesis is needed for this characterization.


Implementation provenance:
`Quillen/Waldhausen/Fibration/WeakEquivalenceCofiber.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The structural extension axiom: in a map of genuine cofibration/cofiber
sequences, weak equivalences on the source and quotient imply one on the middle. -/
structure ExtensionAxiom : Prop where
  extension {A B Q A' B' Q' : C}
    {i : A ⟶ B} {q : B ⟶ Q} {i' : A' ⟶ B'} {q' : B' ⟶ Q'}
    (hi : W.cof i) (hi' : W.cof i')
    (h : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q))
    (h' : IsPushout i' (W.isZero.from_ A') q' (W.isZero.to_ Q'))
    (a : A ⟶ A') (b : B ⟶ B') (c : Q ⟶ Q')
    (wi : i ≫ b = a ≫ i') (wq : q ≫ c = b ≫ q') :
    W.weq a → W.weq c → W.weq b

/-- Acyclicity is the actual weak-equivalence property of the zero-to-object map. -/
def Acyclic (X : C) : Prop := W.weq (W.isZero.to_ X)

/-- Every genuine zero object is acyclic. -/
theorem acyclic_of_isZero {X : C} (hX : IsZero X) : Acyclic W X := by
  have h : W.isZero.to_ X = (W.isZero.iso hX).hom := W.isZero.eq_of_src _ _
  unfold Acyclic
  rw [h]
  exact W.weq_iso _ inferInstance

@[simp] theorem acyclic_zero : Acyclic W W.zero := acyclic_of_isZero W W.isZero

/-- The cofiber of an actual weak cofibration is acyclic, by genuine gluing. -/
theorem acyclic_of_weak_of_isPushout {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (h : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q))
    (hw : W.weq i) : Acyclic W Q := by
  have hs : IsPushout (𝟙 A) (W.isZero.from_ A) (W.isZero.from_ A)
      (W.isZero.to_ W.zero) := by
    have he : W.isZero.to_ W.zero = 𝟙 W.zero := W.isZero.eq_of_src _ _
    rw [he]
    exact IsPushout.id_horiz _
  exact W.gluing (𝟙 A) i (𝟙 W.zero) (W.isZero.to_ Q)
    (W.cof.id_mem A) hi hs h
    (by simp) (by simp) (by simpa using h.w.symm) (W.isZero.eq_of_src _ _)
    (W.weq.id_mem A) hw (W.weq.id_mem W.zero)

/-- Conversely, the extension axiom applied to the identity cofiber sequence
makes a cofibration with acyclic displayed quotient a weak equivalence. -/
theorem weak_of_acyclic_of_isPushout (he : ExtensionAxiom W)
    {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (h : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q))
    (hQ : Acyclic W Q) : W.weq i := by
  have hs : IsPushout (𝟙 A) (W.isZero.from_ A) (W.isZero.from_ A)
      (W.isZero.to_ W.zero) := by
    have hz : W.isZero.to_ W.zero = 𝟙 W.zero := W.isZero.eq_of_src _ _
    rw [hz]
    exact IsPushout.id_horiz _
  exact he.extension (W.cof.id_mem A) hi hs h (𝟙 A) i (W.isZero.to_ Q)
    (by simp) h.w.symm (W.weq.id_mem A) hQ

/-- A displayed genuine cofiber detects whether its cofibration is weak. -/
theorem weak_iff_acyclic_of_isPushout (he : ExtensionAxiom W)
    {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (h : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    W.weq i ↔ Acyclic W Q :=
  ⟨acyclic_of_weak_of_isPushout W hi h, weak_of_acyclic_of_isPushout W he hi h⟩

/-- The quotient in this characterization can be the existing actual cofiber
functor of the genuine extension category; no new quotient is substituted. -/
theorem cofiber_acyclic_iff (he : ExtensionAxiom W) (X : ExtensionCategory.Obj W) :
    Acyclic W ((ExtensionCategory.cofiber W).obj X) ↔ W.weq X.obj.hom :=
  (weak_iff_acyclic_of_isPushout W he X.property
    (ExtensionCategory.cofiber_isPushout W X)).symm

end CategoryTheory.Waldhausen.Fibration


namespace CategoryTheory.Waldhausen.Fibration

attribute [colib_tag "COL-0251",
  colib_ref "Waldhausen1985" "Section 1.6, Theorem 1.6.4, extension and acyclic objects"
    "adaptation"
    "Cofiber detection from the extension condition on actual displayed pushout squares"]
  weak_iff_acyclic_of_isPushout

end CategoryTheory.Waldhausen.Fibration
