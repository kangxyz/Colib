/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.QuasiIsoGluing
public import Colib.CategoryTheory.Waldhausen.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# The Waldhausen category of complexes

Adapted from Quillen/Waldhausen/Complexes.lean at c561118b7795eb9780be9ed391c3251d6a4d0afd.
The original zero, monomorphisms, quasi-isomorphisms and displayed pushout maps are retained.

For complexes in an abelian category, cofibrations are monomorphisms and
weak equivalences are genuine quasi-isomorphisms. The gluing axiom follows
from the exact sequence attached to a pushout and the homology five lemma.
This ambient construction is not a perfect-complex K-theory model by itself.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

universe v u

namespace CategoryTheory.Waldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The genuine Waldhausen structure on all cochain complexes in an
abelian category: monomorphisms and quasi-isomorphisms. -/
@[colib_tag "COL-0177",
  colib_ref "quillen" "Quillen/Waldhausen/Complexes.lean:45-64" "adaptation"
    "The original zero complex, all monomorphisms, genuine quasi-isomorphisms and pushouts",
  colib_ref "Waldhausen1985" "Sections 1.1-1.2, pp.320-321 and 326-327"
    "background" "The cofibration, weak-equivalence and gluing axioms instantiated for complexes"]
def complexes (A : Type u) [Category.{v} A] [Abelian A] :
    Structure (CochainComplex A ℤ) where
  zero := 0
  isZero := isZero_zero _
  cof := MorphismProperty.monomorphisms _
  weq := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := by intro X Y f hf; exact @IsIso.mono_of_iso _ _ _ _ f hf
  weq_iso := by intro X Y f hf; let := hf; exact quasiIso_of_isIso f
  cof_zero X := by dsimp [MorphismProperty.monomorphisms]; infer_instance
  pushout_exists i f _ := ⟨pushout i f, pushout.inl _ _, pushout.inr _ _, .of_hasPushout _ _⟩
  cof_pushout hi h := MorphismProperty.IsStableUnderCobaseChange.of_isPushout h.flip hi
  gluing a b d p hi hi' h h' ei ef eg ej ha hb hd := by
    let : Mono _ := hi
    let : Mono _ := hi'
    let : QuasiIso a := ha
    let : QuasiIso b := hb
    let : QuasiIso d := hd
    exact CochainComplex.quasiIso_gluing h h' a b d p ei ef eg ej

end CategoryTheory.Waldhausen
