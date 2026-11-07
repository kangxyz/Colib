/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectRestriction
public import Colib.KTheory.Waldhausen.CanonicalMap

/-!
# K-theory restriction for native perfect complexes

The ordinary restriction of perfect complexes is Waldhausen-exact. Its K-map is the existing
canonical map induced by that exact functor, with the existing chosen-zero rebasing.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Restriction on the genuine Waldhausen K-groups of native perfect complexes. -/
@[colib_tag "COL-0230",
  colib_ref "Waldhausen1985" "Section 1.3, pp.328-330"
  "background" "The existing canonical K-map of the exact restriction functor"]
def perfectComplexesRestrictKMap (X : Scheme.{u}) (U : X.Opens) (n : ℕ) :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n →*
      (RingedSpace.perfectComplexesWaldhausen U.toScheme.toRingedSpace).K n :=
  Waldhausen.KMap (perfectComplexesRestrictFunctor_isExact X U) n

/-- The restriction map is exactly the canonical K-map of ordinary restriction. -/
theorem perfectComplexesRestrictKMap_eq (X : Scheme.{u}) (U : X.Opens) (n : ℕ) :
    perfectComplexesRestrictKMap X U n =
      Waldhausen.KMap (perfectComplexesRestrictFunctor_isExact X U) n := rfl

end AlgebraicGeometry.Scheme.Modules
