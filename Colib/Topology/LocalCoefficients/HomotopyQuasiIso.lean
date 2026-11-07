/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.HomotopyEquivalence
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Quasi-isomorphism of the actual local chain map of a homotopy equivalence

The spatial comparison from `Quillen/Topology/LocalCoefficients/RelativeHomotopyEquivalence.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd` is extracted below relative-chain
excision: it depends only on the proved transported singular-prism homotopy.
-/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original spatial chain map of a homotopy equivalence is a quasi-isomorphism. -/
theorem pushforwardChainMap_quasiIso_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv X Y) (A : System.{u, u} Y) :
    QuasiIso (pushforwardChainMap e.toFun A) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_pushforwardHomologyMap_of_homotopyEquiv e A n

end FundamentalGroupoid.LocalCoefficients
