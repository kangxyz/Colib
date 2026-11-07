/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.MatrixDeflation
public import Colib.CategoryTheory.ExactCategory.Isomorphisms

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/ExactCategory/CoproductDeflation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Admissible epimorphisms from binary coproducts -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- An admissible second component makes the coproduct desc map admissible. -/
theorem deflation_coprod_desc {A B X : C} [HasBinaryCoproduct A B]
    (f : A ⟶ X) (p : B ⟶ X) (hp : E.deflation p) :
    E.deflation (coprod.desc f p) := by
  let : HasBinaryBiproduct A B := by
    let := hasBinaryBiproducts_of_finite_biproducts (C := C)
    infer_instance
  have h := E.deflation_comp (biprod.isoCoprod A B).inv (biprod.desc f p)
    (E.deflation_of_iso (biprod.isoCoprod A B).symm) (E.deflation_biprod_desc f p hp)
  convert h using 1
  simp [biprod.isoCoprod_inv, coprod.desc_comp]

end CategoryTheory.ExactCategory.ExactStructure
