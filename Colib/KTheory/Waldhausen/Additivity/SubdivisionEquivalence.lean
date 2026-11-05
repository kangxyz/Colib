/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.OrdinalSubdivisionComparison
public import Colib.KTheory.Waldhausen.Additivity.Conditional

/-! # The proved based forward subdivision isomorphism

Source: Quillen/Waldhausen/Additivity/SubdivisionBasepoint.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The global comparison is proved,
not supplied as a hypothesis; the forward map is the original endpoint piMap.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C : Type u} [Category.{v} C] (V : Structure C)

/-- The actual horizontal subdivision endpoint induces its forward group isomorphism. -/
def subdivisionPiEquiv (n : ℕ) :
    HomotopyGroup.Pi (n + 1)
      |SSet.diagonalSSet (SSet.OrdinalSubdivision.horizontal (bisimplicialSSet V))|
      (subdivisionBasepoint V) ≃*
    HomotopyGroup.Pi (n + 1) |SSet.diagonalSSet (bisimplicialSSet V)|
      (SSet.realizationPoint (diagonalZeroVertex V)) :=
  Conditional.subdivisionPiEquiv SSet.OrdinalSubdivision.realizationComparison V n

/-- No basepoint transport is hidden in the actual forward map. -/
@[simp]
theorem subdivisionPiEquiv_coe (n : ℕ) :
    ↑(subdivisionPiEquiv V n) = subdivisionPiMap V n := rfl

/-- The original based forward subdivision map is surjective in every positive degree. -/
theorem subdivisionPiMap_surjective (n : ℕ) :
    Function.Surjective (subdivisionPiMap V n) := (subdivisionPiEquiv V n).surjective

end CategoryTheory.Waldhausen.Additivity
