/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Functor.Pushouts
public import Colib.CategoryTheory.Waldhausen.ExactCategory
public import Colib.CategoryTheory.Waldhausen.ExactFunctor

/-! # Exact Quillen functors are exact Waldhausen functors

The pushout axiom is proved by preservation of the actual biproduct conflation,
not supplied as an extra hypothesis. All other structural conditions follow
from genuine additive exactness and functorial preservation of isomorphisms.

Adapted from `Quillen/Waldhausen/ExactFunctor.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the existing native exact functors.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
open CategoryTheory CategoryTheory.Limits
universe v u v' u'

namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- Genuine exactness implies all Waldhausen-exact structure conditions. -/
theorem waldhausenExact : Waldhausen.IsExact
    (Waldhausen.ofExactCategory EC).cof (Waldhausen.ofExactCategory EC).weq
    (Waldhausen.ofExactCategory ED).cof (Waldhausen.ofExactCategory ED).weq F.toFunctor where
  zero hZ := F.toFunctor.map_isZero hZ
  cofibration f hf := F.map_inflation f hf
  weak f hf := by
    let : IsIso f := hf
    exact F.toFunctor.map_isIso f
  pushout hi h := F.map_isPushout hi h

end CategoryTheory.ExactCategory.ExactFunctor

attribute [colib_tag "COL-0243",
  colib_ref "quillen" "Quillen/Waldhausen/ExactFunctor.lean"
    "adaptation" "Actual Waldhausen exactness derived from additive conflation preservation"]
  CategoryTheory.ExactCategory.ExactFunctor.waldhausenExact
