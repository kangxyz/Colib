/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Mathlib.CategoryTheory.Widesubcategory

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/ExactCategory/Inflations.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The category of admissible monomorphisms

The original exact structure supplies the multiplicative inflation
predicate. Its wide subcategory retains the ambient objects and arrows.
-/
@[expose] public section

universe v u
open CategoryTheory
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [Limits.HasFiniteBiproducts C] (E : ExactStructure C)

instance inflation_isMultiplicative : E.inflation.IsMultiplicative where

/-- The original objects and their admissible monomorphisms. -/
abbrev InflationCategory := WideSubcategory E.inflation

end CategoryTheory.ExactCategory.ExactStructure
