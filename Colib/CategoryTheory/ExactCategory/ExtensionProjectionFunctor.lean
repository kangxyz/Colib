/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionIdentity
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionComposition

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionProjectionFunctor.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The actual extension projection to the original Q construction

Both functor laws are proved for the original Q quotient and its genuine
pullback composition. Theorem B's comma-transition condition and the relation
between the strict fibers and extension groupoids remain further theorems.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
universe v u
open CategoryTheory
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- Grayson's extension projection, with the original exact-category Q target. -/
def extensionProjection : E.ExtensionTotal ⥤ QConstruction E.deflation E.inflation where
  obj := E.extensionProjectionQObj
  map := E.extensionProjectionQMap
  map_id := E.extensionProjectionQMap_id
  map_comp := E.extensionProjectionQMap_comp

end CategoryTheory.ExactCategory.ExactStructure
