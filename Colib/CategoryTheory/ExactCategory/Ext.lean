/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module
public import Colib.CategoryTheory.ExactCategory.Basic

/-! Exact-structure extensionality from pinned Aglib SmallModel/Abelian,
without small-model machinery. -/
@[expose] public section
universe u₁ v₁
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure

/-- The selected conflations determine all the remaining exact structure data,
since the universal-property witnesses are unique. -/
theorem ext_conflation {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [HasFiniteBiproducts C] {E E' : ExactStructure C}
    (h : E.conflation = E'.conflation) : E = E' := by
  cases E
  cases E'
  cases h
  congr <;> apply Subsingleton.elim

end CategoryTheory.ExactCategory.ExactStructure
