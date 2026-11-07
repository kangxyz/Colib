/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackSpatial

/-!
# Spatial products of the actual normalized cubes

A spatial coordinate distinct from the normalization coordinate has a branch
condition independent of both normalization time and track time. The original
piecewise concatenation therefore passes through the complete normalization.
The output coordinate is the successor of that same original spatial coordinate.
No multiplication on the ambient space is used.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/GenLoopSelfTrackSpatialProduct.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original cube coordinates,
whole tracks and group laws are retained under native Colib ownership. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology

/-- A distinct coordinate update leaves the original spatial-concatenation branch unchanged. -/
theorem genLoop_transAt_update {N : Type v} [DecidableEq N]
    {X : Type u} [TopologicalSpace X] {x : X} (i j : N) (hij : i ≠ j)
    (p q : GenLoop N X x) (z : N → unitInterval) (s : unitInterval) :
    GenLoop.transAt i p q (Function.update z j s) =
      if (z i : ℝ) ≤ 1 / 2 then
        p (Function.update (Function.update z i
          (Set.projIcc 0 1 zero_le_one (2 * z i))) j s)
      else
        q (Function.update (Function.update z i
          (Set.projIcc 0 1 zero_le_one (2 * z i - 1))) j s) := by
  simp only [GenLoop.transAt, GenLoop.coe_copy, Function.update_of_ne hij]
  split_ifs <;> rw [Function.update_comm hij.symm]

/-- Normalization commutes with concatenation in every other original spatial coordinate. -/
theorem genLoopNormalizedSelfTrackPath_transAt
    {X : Type u} [TopologicalSpace X] {x : X} (m : ℕ)
    (i : Fin (m + 1)) (hi : i ≠ 0)
    (p q : GenLoop (Fin (m + 1)) X x) (α : Path p p) (β : Path q q)
    (t : unitInterval) :
    genLoopNormalizedSelfTrackPath m (GenLoop.transAt i p q) (genLoopTransAtPath i α β) t =
      GenLoop.transAt i (genLoopNormalizedSelfTrackPath m p α t)
        (genLoopNormalizedSelfTrackPath m q β t) := by
  ext z
  change genLoopNormalizedSelfTrackPath m (GenLoop.transAt i p q)
      (genLoopTransAtPath i α β) t z =
    if (z i : ℝ) ≤ 1 / 2 then
      genLoopNormalizedSelfTrackPath m p α t
        (Function.update z i (Set.projIcc 0 1 zero_le_one (2 * z i)))
    else
      genLoopNormalizedSelfTrackPath m q β t
        (Function.update z i (Set.projIcc 0 1 zero_le_one (2 * z i - 1)))
  split_ifs with hz
  · refine genLoopNormalizedSelfTrackPath_congr_eval m _ _ _ _ z _ ?_ ?_ ?_ t
    · exact (Function.update_of_ne hi.symm _ _).symm
    · intro s
      rw [genLoop_transAt_update i 0 hi, ite_eq_left hz]
    · intro r s
      change GenLoop.transAt i (α r) (β r) (Function.update z 0 s) = _
      rw [genLoop_transAt_update i 0 hi, ite_eq_left hz]
  · refine genLoopNormalizedSelfTrackPath_congr_eval m _ _ _ _ z _ ?_ ?_ ?_ t
    · exact (Function.update_of_ne hi.symm _ _).symm
    · intro s
      rw [genLoop_transAt_update i 0 hi, ite_eq_right hz]
    · intro r s
      change GenLoop.transAt i (α r) (β r) (Function.update z 0 s) = _
      rw [genLoop_transAt_update i 0 hi, ite_eq_right hz]

/-- The extra first coordinate shifts the same spatial-concatenation coordinate by one. -/
theorem genLoopNormalizedSelfTrackCube_transAt
    {X : Type u} [TopologicalSpace X] {x : X} (m : ℕ)
    (i : Fin (m + 1)) (hi : i ≠ 0)
    (p q : GenLoop (Fin (m + 1)) X x) (α : Path p p) (β : Path q q) :
    genLoopNormalizedSelfTrackCube m (GenLoop.transAt i p q) (genLoopTransAtPath i α β) =
      GenLoop.transAt i.succ (genLoopNormalizedSelfTrackCube m p α)
        (genLoopNormalizedSelfTrackCube m q β) := by
  ext z
  rw [genLoopNormalizedSelfTrackCube_apply, genLoopNormalizedSelfTrackPath_transAt m i hi]
  simp only [GenLoop.transAt, GenLoop.coe_copy, genLoopNormalizedSelfTrackCube_apply,
    Function.update_of_ne (Fin.succ_ne_zero i).symm, Fin.tail_update_succ]
  rfl

/-- Equal original cubes and pointwise equal actual tracks have the same normalized cube. -/
theorem genLoopNormalizedSelfTrackCube_congr
    {X : Type u} [TopologicalSpace X] {x : X} (m : ℕ)
    (p q : GenLoop (Fin (m + 1)) X x) (hp : p = q)
    (α : Path p p) (β : Path q q) (hα : ∀ t, α t = β t) :
    genLoopNormalizedSelfTrackCube m p α = genLoopNormalizedSelfTrackCube m q β := by
  subst q
  have hpath : α = β := Path.ext (funext hα)
  subst β
  rfl

end Topology
