/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinderNaturality

/-! # Actual zero-grid constancy of the nerve cylinder -/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/NerveCylinderZero.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd.
   Validation status is recorded in the accompanying release report. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen

variable {D : Type u} [Category.{v} D] {n m : SimplexCategory}
  {A B : Grid₂ n m ⥤ D}

/-- If both actual endpoint diagrams have the same zero object at every
vertex, the categorical cylinder is the actual constant zero diagram.
No condition on its transformation components is needed: zero uniqueness
proves every transported component is the identity. -/
theorem nerveCylinderDiagram_eq_const_of_zero (η : A ⟶ B) (Z : D) (hZ : IsZero Z)
    (hA : ∀ p, A.obj p = Z) (hB : ∀ p, B.obj p = Z) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram η τ = (Functor.const (Grid₂ n m)).obj Z := by
  have hobj (p : Grid₂ n m) : (nerveCylinderDiagram η τ).obj p = Z := by
    change ((ComposableArrows.mk₁ η).obj (τ.toOrderHom p.1)).obj p = Z
    generalize τ.toOrderHom p.1 = a
    fin_cases a
    · exact hA p
    · exact hB p
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q f
  exact (hZ.of_iso (eqToIso (hobj q))).eq_of_tgt _ _

end CategoryTheory.Waldhausen
