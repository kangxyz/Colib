/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.QCategory

/-! # Sources of Q-arrows to zero objects

The epic left leg and monic right leg of an admissible span show that any Q-arrow
to an original zero object has an original zero object as its source. This does
not assert that the Q-category has a zero object.

Adapted from `Quillen/Localization/Serre/LocalizationComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native Q-spans,
comma categories, functors and realization maps are retained.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- A Q-arrow into an original zero object forces its source object to be zero.
No zero-object assertion about the entire Q-category is involved. -/
theorem isZero_source_of_qHom {X Y : E.QCategory} (f : X ⟶ Y)
    (hY : IsZero Y.obj.of) : IsZero X.obj.of := by
  induction f using Quotient.inductionOn with
  | _ s =>
    have : Mono s.r := E.mono_of_inflation s.wr
    have : Epi s.l := E.epi_of_deflation s.wl
    have hS : IsZero s.apex := (IsZero.iff_id_eq_zero _).2 (by
      apply (cancel_mono s.r).1
      exact hY.eq_of_tgt _ _)
    apply (IsZero.iff_id_eq_zero _).2
    apply (cancel_epi s.l).1
    exact hS.eq_of_src _ _

end CategoryTheory.ExactCategory.ExactStructure
