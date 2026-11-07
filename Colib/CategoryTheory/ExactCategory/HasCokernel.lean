/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Basic

/-!
# Actual cokernels of admissible monomorphisms

The original defining conflation supplies the genuine cokernel universal
property of every admissible monomorphism, without an ambient abelian category.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- An inflation has an actual cokernel, supplied by its defining conflation. -/
theorem hasCokernel_of_inflation {X Y : C} (f : X ⟶ Y) (hf : E.inflation f) : HasCokernel f := by
  obtain ⟨Z, p, w, h⟩ := hf
  exact ⟨⟨CokernelCofork.ofπ p w, E.cokernel _ h⟩⟩

end CategoryTheory.ExactCategory.ExactStructure
