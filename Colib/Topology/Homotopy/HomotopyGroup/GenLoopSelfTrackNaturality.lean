/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizedSelfTrackNaturality

/-!
# Based naturality of the actual normalized cubes

The complete inverse-prefix representative commutes with based continuous
postcomposition. Both original cancellations, the track parameter, and every
original cube coordinate are retained pointwise.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/GenLoopSelfTrackNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original cube coordinates,
whole tracks and group laws are retained under native Colib ownership. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology

/-- Postcomposition preserves the actual normalized path at each original cube coordinate. -/
theorem genLoopNormalizedSelfTrackPath_naturality
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α : Path p p)
    (t : unitInterval) (z : Fin (m + 1) → unitInterval) :
    f (genLoopNormalizedSelfTrackPath m p α t z) =
      genLoopNormalizedSelfTrackPath m (GenLoop.postcomp f h p)
        (α.map (genLoopPostcompContinuousMap f h).continuous) t z := by
  let L := GenLoop.loopHomeo (X := X) (x := x) (0 : Fin (m + 1))
  let M := GenLoop.loopHomeo (X := Y) (x := y) (0 : Fin (m + 1))
  change f ((loopNormalizedSelfTrack (L.toHomotopyEquiv.toFun p)
      (α.map L.toHomotopyEquiv.toFun.continuous) t (z 0)) ((Cube.splitAt 0 z).2)) =
    (loopNormalizedSelfTrack (M.toHomotopyEquiv.toFun (GenLoop.postcomp f h p))
      ((α.map (genLoopPostcompContinuousMap f h).continuous).map
        M.toHomotopyEquiv.toFun.continuous) t (z 0)) ((Cube.splitAt 0 z).2)
  exact loopNormalizedSelfTrack_pointwise
    (fun r : GenLoop {j : Fin (m + 1) // j ≠ 0} X x ↦ f (r ((Cube.splitAt 0 z).2)))
    (fun r : GenLoop {j : Fin (m + 1) // j ≠ 0} Y y ↦ r ((Cube.splitAt 0 z).2))
    _ _ _ _ (fun _ ↦ rfl) (fun _ _ ↦ rfl) t (z 0)

/-- The one-higher original normalized cube commutes exactly with based postcomposition. -/
theorem genLoopNormalizedSelfTrackCube_naturality
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α : Path p p) :
    GenLoop.postcomp f h (genLoopNormalizedSelfTrackCube m p α) =
      genLoopNormalizedSelfTrackCube m (GenLoop.postcomp f h p)
        (α.map (genLoopPostcompContinuousMap f h).continuous) := by
  ext z
  exact genLoopNormalizedSelfTrackPath_naturality f h m p α (z 0) (Fin.tail z)

/-- The original higher self-track class commutes with the original based homotopy map. -/
theorem genLoopSelfTrackClass_naturality
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α : Path p p) :
    HomotopyGroup.piMap (m + 1) f h (genLoopSelfTrackClass m p α) =
      genLoopSelfTrackClass m (GenLoop.postcomp f h p)
        (α.map (genLoopPostcompContinuousMap f h).continuous) := by
  rw [← genLoopNormalizedSelfTrackCube_class, ← genLoopNormalizedSelfTrackCube_class]
  exact congrArg Quotient.mk' (genLoopNormalizedSelfTrackCube_naturality f h m p α)

end Topology
