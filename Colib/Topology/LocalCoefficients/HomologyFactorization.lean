/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.HomotopyInvariance

/-!
Adapted from `Quillen/Topology/LocalCoefficients/HomologyFactorization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual original
stage arrows, finite support and coefficient corrections.
 # Actual local-homology preimages from a specified homotopy factorization -/

@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients

/-- An actual homotopy factorization puts every original source class in the
image of the specified final map, with its required coefficient transports. -/
theorem exists_preimage_of_homotopy_factorization {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (g : C(X, Y)) (s : C(X, Z)) (H : s.Homotopy (f.comp g))
    (A : System.{u, u} Z) (n : ℕ) (x : homology (pullback s A) n) :
    ∃ y : homology (pullback f A) n,
      pushforwardHomologyMap f A n y = pushforwardHomologyMap s A n x := by
  refine ⟨pushforwardHomologyMap g (pullback f A) n
    (coefficientHomologyMap (pullbackCompositionIso g f A).hom n
      (coefficientHomologyMap (homotopyPullbackIso H A).hom n x)), ?_⟩
  have he := pushforwardHomologyMap_homotopy H A n
  rw [pushforwardHomologyMap_comp] at he
  exact (congrArg (fun k ↦ k x) he).symm

end FundamentalGroupoid.LocalCoefficients
