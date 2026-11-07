/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.UnitInterval
public import Colib.Topology.HomotopyLifting.Stationary
public import Mathlib.Topology.Algebra.Monoid
public import Colib.Topology.HELP.CubeBoundaryHomeomorph

/-! # A literal vanishing duration for the whole finite cube boundary

Implementation provenance:
`Quillen/Topology/HomotopyLifting/CubeDuration.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
open unitInterval
namespace Topology.CubicalTests
universe u

/-- Product of distances to the two endpoints in every original coordinate.
The empty product is one, correctly excluding a boundary in dimension zero. -/
def boundaryDuration (n : ℕ) : C(cube.{u} n,unitInterval) :=
  ⟨fun z ↦ ∏ i : Fin n,z.down i * σ (z.down i),by
    let : ContinuousMul unitInterval := ⟨Topology.continuous_intervalMul⟩
    apply continuous_finsetProd
    intro i _
    fun_prop⟩

@[simp] theorem boundaryDuration_apply (n : ℕ) (z : cube.{u} n) :
    boundaryDuration n z = ∏ i : Fin n,z.down i * σ (z.down i) := rfl

/-- The zero locus is exactly the entire actual cube boundary. -/
theorem boundaryDuration_eq_zero_iff (n : ℕ) (z : cube.{u} n) :
    boundaryDuration n z = 0 ↔ z.down ∈ _root_.Cube.boundary (Fin n) := by
  change (∏ i : Fin n,z.down i * σ (z.down i)) = 0 ↔ ∃ i,z.down i = 0 ∨ z.down i = 1
  simp only [Finset.prod_eq_zero_iff,Finset.mem_univ,true_and,mul_eq_zero,symm_eq_zero]

@[simp] theorem boundaryDuration_boundary (n : ℕ) (z : boundary.{u} n) :
    boundaryDuration n z.val = 0 := (boundaryDuration_eq_zero_iff n z.val).mpr z.2

@[simp] theorem boundaryDuration_zero_dim (z : cube.{u} 0) : boundaryDuration 0 z = 1 := by
  simp [boundaryDuration]

end Topology.CubicalTests
