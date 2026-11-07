/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.Regular

/-! Regression tests for actual finite resolutions and the original regular-scheme K-to-G map. -/

universe u

open CategoryTheory CategoryTheory.ExactCategory

noncomputable section

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Tests

variable (X : Scheme.{u}) [CompactSpace X]
  [AlgebraicGeometry.HasResolutionProperty X] (hX : AlgebraicGeometry.IsRegular X)

-- No separate Noetherianity, quasi-separatedness or dimension hypothesis is supplied.
example :
    letI := AlgebraicGeometry.isLocallyNoetherian_of_isRegular hX
    Function.Bijective (KToG X 0) := KToG_regular_bijective X hX 0

example (n : ℕ) :
    letI := AlgebraicGeometry.isLocallyNoetherian_of_isRegular hX
    K X n ≃* G X n := KToGRegularEquiv X hX n

example (n : ℕ) :
    letI := AlgebraicGeometry.isLocallyNoetherian_of_isRegular hX
    (↑(KToGRegularEquiv X hX n) : K X n →* G X n) = KToG X n := rfl

example (n : ℕ) (x : K X n) :
    letI := AlgebraicGeometry.isLocallyNoetherian_of_isRegular hX
    KToGRegularEquiv X hX n x = KToG X n x := rfl

-- The proof constructs actual finite admissible resolution data, object by object.
example (M : X.Modules) [M.IsCoherent] :
    Nonempty ((Modules.sheafExactStructure X).FiniteResolution
      (fun N : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) M) :=
  Modules.nonempty_finiteResolution_of_regular X hX M

end AlgebraicGeometry.Scheme.Tests
