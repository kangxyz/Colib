/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Realization.PrismCoordinates

/-!
# Finite prism coordinate regression tests

These tests use the actual finite barycentric simplex, coordinate maps and closed cells.
They do not assert a comparison with a simplicial realization or a cylinder isomorphism.
-/

open Convexity Convexity.StdSimplex
open scoped unitInterval

noncomputable section

variable {n : ℕ}

example (i : Fin (n + 1)) (v : StdSimplex ℝ (Fin (n + 2))) :
    (prismProject i v).1 = v.map i.predAbove := rfl

example (i : Fin (n + 1)) (v : StdSimplex ℝ (Fin (n + 2))) :
    ((prismProject i v).2 : ℝ) = prismHeight i v := rfl

example (i : Fin (n + 1)) (v : StdSimplex ℝ (Fin (n + 2))) :
    prismLift i ⟨prismProject i v, prismProject_mem_cell i v⟩ = v :=
  prismLift_prismProject i v

example (i : Fin (n + 1)) (z : prismCell i) :
    prismProject i (prismLift i z) = z.1 := by
  exact congrArg Subtype.val ((prismCellHomeomorph i).apply_symm_apply z)

example (i : Fin (n + 1)) (z : prismCell i) :
    (prismLift i z).weights i.castSucc = prismSplitAmount i z.1 :=
  prismLift_weights_castSucc i z

example (i : Fin (n + 1)) (z : prismCell i) :
    (prismLift i z).weights i.succ = (z.1.2 : ℝ) - prismTail z.1.1 i :=
  prismLift_weights_succ i z

example (i : Fin (n + 1)) (z : prismCell i) (j : Fin (n + 1)) :
    (prismLift i z).weights (i.castSucc.succAbove j) =
      z.1.1.weights j - if j = i then prismSplitAmount i z.1 else 0 :=
  prismLift_weights_succAbove i z j

example (i : Fin (n + 1)) (v : StdSimplex ℝ (Fin (n + 2))) :
    ((prismCellHomeomorph i) v).1 = prismProject i v := rfl

example (i : Fin (n + 1)) (z : prismCell i) :
    (prismCellHomeomorph i).symm z = prismLift i z := rfl

example (z : StdSimplex ℝ (Fin (n + 1)) × I) : ∃ i, z ∈ prismCell i :=
  exists_mem_prismCell z

example (i : Fin (n + 1)) : Set.range (prismProject i) = prismCell i :=
  range_prismProject i

example (i : Fin (n + 1)) : Function.Injective (prismProject i) :=
  prismProject_injective i

example {z : StdSimplex ℝ (Fin (n + 1)) × I} {i j k : Fin (n + 1)}
    (hi : z ∈ prismCell i) (hj : z ∈ prismCell j) (hik : i ≤ k) (hkj : k ≤ j) :
    z ∈ prismCell k := mem_prismCell_of_between hi hj hik hkj

example (i : Fin (n + 1)) {z : StdSimplex ℝ (Fin (n + 2)) × I}
    (hi : z ∈ prismCell i.castSucc) (hj : z ∈ prismCell i.succ) :
    (z.2 : ℝ) = prismTail z.1 i.castSucc := prism_adjacent_overlap_height i hi hj

example (i : Fin (n + 1)) {z : StdSimplex ℝ (Fin (n + 2)) × I}
    (hi : z ∈ prismCell i.castSucc) (hj : z ∈ prismCell i.succ) :
    (prismLift i.castSucc ⟨z, hi⟩).weights i.castSucc.succ = 0 :=
  prismLift_adjacent_left_zero i hi hj

example (i : Fin (n + 1)) {z : StdSimplex ℝ (Fin (n + 2)) × I}
    (hi : z ∈ prismCell i.castSucc) (hj : z ∈ prismCell i.succ) :
    (prismLift i.succ ⟨z, hj⟩).weights i.succ.castSucc = 0 :=
  prismLift_adjacent_right_zero i hi hj

example (i : Fin (n + 1)) : Continuous (prismLift i) := continuous_prismLift i

example (i : Fin (n + 1)) : Continuous (prismProject i) := continuous_prismProject i

example (i : Fin (n + 1)) : IsClosed (prismCell i) := isClosed_prismCell i

example : CompactSpace (StdSimplex ℝ (Fin (n + 2))) := inferInstance

example {M : Type*} [Finite M] : T2Space (StdSimplex ℝ M) := inferInstance
