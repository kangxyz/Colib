/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.OpenCover.TwoSet.Partition
public import Colib.Topology.HomotopyLifting.Collar.Schedule

/-! The concrete partition for the two height collars. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/HeightCover.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and proofs
with native namespace and import ownership. -/
@[expose] public section

noncomputable section
open Topology
open scoped Topology unitInterval
open unitInterval
universe u
namespace TopCat.TwoOpenPartition
variable {X : Type u} [TopologicalSpace X]

/-- The standard overlapping height collars have an explicit subordinate
partition, with open neighborhoods of the zero and one loci. -/
def ofHeight (h : C(X, I)) : TwoOpenPartition X where
  leftSet := {x | (h x : ℝ) < 3 / 4}
  rightSet := {x | 1 / 4 < (h x : ℝ)}
  left_open := isOpen_lt (by fun_prop) continuous_const
  right_open := isOpen_lt continuous_const (by fun_prop)
  cover := by
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    by_cases hx : (h x : ℝ) < 3 / 4
    · exact Or.inl hx
    · exact Or.inr (by linarith)
  cutoff := ⟨fun x ↦ clampInterval (3 * (h x : ℝ) - 1), by fun_prop⟩
  zeroSet := {x | (h x : ℝ) < 1 / 3}
  oneSet := {x | 2 / 3 < (h x : ℝ)}
  zero_open := isOpen_lt (by fun_prop) continuous_const
  one_open := isOpen_lt continuous_const (by fun_prop)
  right_zero_cover := by
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    by_cases hx : 1 / 4 < (h x : ℝ)
    · exact Or.inl hx
    · exact Or.inr (by linarith)
  left_one_cover := by
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    by_cases hx : (h x : ℝ) < 3 / 4
    · exact Or.inl hx
    · exact Or.inr (by linarith)
  cutoff_zero := by intro x hx; exact clampInterval_eq_zero (by dsimp at hx; linarith)
  cutoff_one := by intro x hx; exact clampInterval_eq_one (by dsimp at hx; linarith)

end TopCat.TwoOpenPartition
