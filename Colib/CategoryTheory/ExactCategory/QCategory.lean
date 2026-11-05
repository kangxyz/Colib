/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.QConstruction.Basic

/-!
# The Q-category of an exact structure

The left legs are the admissible epimorphisms and the right legs the admissible
monomorphisms of the selected exact structure. Its axioms supply precisely the
mixed pullback and composition properties required by the restricted-span category.
This definition does not involve a nerve, classifying space or homotopy group.

## Implementation provenance

Extracted from `Quillen/KTheory/Basic.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original `QCategory` abbreviation
retains its exact structure, universes, objects and restricted-span arrows.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The Quillen Q-category attached to the given exact structure. -/
abbrev QCategory := CategoryTheory.QConstruction E.deflation E.inflation

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0038",
  colib_ref "WeibelKBook" "IV, Definition 6.1, equation (6.1.1)" "adaptation"
    "The categorical Q-construction uses the admissible legs of the selected exact structure"]
  CategoryTheory.ExactCategory.ExactStructure.QCategory
