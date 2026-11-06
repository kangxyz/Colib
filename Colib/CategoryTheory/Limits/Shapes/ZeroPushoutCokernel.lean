/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Cokernels from actual zero-corner pushouts

In a preadditive category the displayed pushout with a zero corner gives its
actual cokernel cocone and universal property. Original maps are retained. Extracted from
`Quillen/Aglib/CategoryTheory/Limits/Shapes/ZeroPushoutCokernel.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; finite biproducts are not needed.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A pushout whose lower-left vertex is zero supplies the actual cokernel
universal property of its upper edge. -/
def cokernelOfZeroPushout {A B Z D : C} {i : A ⟶ B} {z : A ⟶ Z}
    {p : B ⟶ D} {q : Z ⟶ D} (sq : IsPushout i z p q) (hZ : IsZero Z) :
    IsColimit (CokernelCofork.ofπ p (show i ≫ p = 0 from by
      rw [sq.w, hZ.eq_of_src q 0, comp_zero])) := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {W} f hf ↦ sq.desc f 0 (by simpa using hf)) ?_ ?_
  · intro W f hf
    exact sq.inl_desc _ _ _
  · intro W f hf m hm
    apply sq.hom_ext
    · simpa using hm
    · exact hZ.eq_of_src _ _

end CategoryTheory.Limits
