/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Resolution.Finite

/-! Adapted from `Quillen/Aglib/CategoryTheory/ExactCategory/Resolution/Transport.lean`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
This module supplies finite-resolution prerequisites, not the Resolution theorem. -/

/-! # Transporting actual finite admissible resolutions along isomorphisms -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure.FiniteResolution
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {E : ExactStructure C} {P : ObjectProperty C} [P.IsClosedUnderIsomorphisms]

/-- Change only the augmentation target of a finite resolution, using an
actual isomorphism. In positive length the middle terms and syzygies are
retained; in length zero the terminal object is replaced by its isomorphic target. -/
def ofIso {X Y : C} (e : X ≅ Y) : E.FiniteResolution P X → E.FiniteResolution P Y
  | .of_mem hX => .of_mem (P.prop_of_iso e hX)
  | .step S hS hP R =>
    let T := ShortComplex.mk S.f (S.g ≫ e.hom) (by simp)
    .step T (E.iso_closed (S := S) (T := T) (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
      (by simp [T]) (by simp [T])) hS) hP R

@[simp]
theorem length_ofIso {X Y : C} (e : X ≅ Y) (T : E.FiniteResolution P X) :
    (T.ofIso e).length = T.length := by
  cases T <;> rfl

end CategoryTheory.ExactCategory.ExactStructure.FiniteResolution
