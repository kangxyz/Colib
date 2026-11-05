/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.Map

/-!
# Homotopy-group maps of constant continuous maps

Adapted from Quillen/Topology/HomotopyGroups/Map.lean:170–192 at commit
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual generalized-loop quotient,
source/target basepoints, universe parameters and degree shift are retained.
-/
@[expose] public noncomputable section
open scoped Topology unitInterval
universe w v u
variable {N : Type w} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- A constant map sends every generalized loop to the constant loop. -/
@[simp]
theorem GenLoop.postcomp_constant (p : GenLoop N X x) :
    GenLoop.postcomp (ContinuousMap.const X y) rfl p = GenLoop.const := by
  ext t
  rfl

/-- The homomorphism induced by a constant map is trivial. -/
@[simp]
theorem HomotopyGroup.mapHom_const [DecidableEq N] [Nonempty N] :
    HomotopyGroup.mapHom (N := N) (x := x) (ContinuousMap.const X y) rfl = 1 := by
  ext a
  refine Quotient.inductionOn a (fun p => ?_)
  change Quotient.mk' (GenLoop.postcomp (ContinuousMap.const X y) rfl p) =
    Quotient.mk' GenLoop.const
  rw [GenLoop.postcomp_constant]

/-- The induced map on `π_(n+1)` of a constant map is trivial. -/
@[simp]
theorem HomotopyGroup.piMap_const (n : ℕ) :
    HomotopyGroup.piMap n (x := x) (ContinuousMap.const X y) rfl = 1 :=
  HomotopyGroup.mapHom_const
