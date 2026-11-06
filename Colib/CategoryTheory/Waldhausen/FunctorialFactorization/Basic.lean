/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Basic
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Functorial cofibration factorizations

A middle-object functor with natural inclusion and projection factors every morphism into a
    cofibration followed by a weak equivalence.


Implementation provenance:
`Quillen/Waldhausen/FunctorialFactorization/Basic.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe v u

namespace CategoryTheory.Waldhausen

/-- A coherent cofibration/weak-equivalence factorization of every morphism. -/
structure FunctorialFactorization {C : Type u} [Category.{v} C] (W : Structure C) where
  /-- The functor assigning a middle object to every arrow and a comparison map to every
  commutative square. -/
  middle : Arrow C ⥤ C
  /-- The natural cofibration from an arrow source into its middle object. -/
  inclusion : Arrow.leftFunc ⟶ middle
  /-- The natural weak equivalence from the middle object to the arrow target; its composite
  with `inclusion` is the original arrow. -/
  projection : middle ⟶ Arrow.rightFunc
  factorization (f : Arrow C) : inclusion.app f ≫ projection.app f = f.hom
  cofibration (f : Arrow C) : W.cof (inclusion.app f)
  weak (f : Arrow C) : W.weq (projection.app f)

attribute [reassoc (attr := simp)] FunctorialFactorization.factorization

end CategoryTheory.Waldhausen

end
