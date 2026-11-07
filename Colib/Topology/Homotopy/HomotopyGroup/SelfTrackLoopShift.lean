/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.SelfTrackOperation
public import Colib.Topology.Homotopy.HomotopyGroup.CoordinateTransposition

/-!
# The sign of the original self-track operation under loop shifting

Looping a whole based identity self-homotopy retains its time parameter.
The resulting degree-zero operation and the original degree-one operation
anti-commute with the actual loop-degree shift.

The normalization axes differ: the original operation normalizes the first
spatial coordinate, while the looped operation normalizes the second. A literal
cube equality accounts for this difference by transposing the input cube.
It identifies the entire uncurried looped normalization, including both original
cancellations, with two output-coordinate transpositions of the normalization
of that transposed input. The two output inversions cancel. The original
source homomorphism sends the input transposition to inversion, giving the sign.

Only the actual based self-homotopy is supplied. No simplicity hypothesis,
additional homotopy law, or localization-boundary compatibility is assumed.
-/
/-! Adapted from `Quillen/Topology/HomotopyGroups/SelfTrackLoopShift.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual paths and coordinates. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v w
namespace Topology.IdentityTrack

private theorem normalizedPath_pointwise
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (a : X → Z) (b : Y → Z) (m n : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (q : GenLoop (Fin (n + 1)) Y y)
    (α : Path p p) (β : Path q q)
    (z : Fin (m + 1) → unitInterval) (w : Fin (n + 1) → unitInterval)
    (h₀ : z 0 = w 0)
    (hp : ∀ s, a (p (Function.update z 0 s)) = b (q (Function.update w 0 s)))
    (hα : ∀ t s, a (α t (Function.update z 0 s)) = b (β t (Function.update w 0 s)))
    (t : unitInterval) :
    a (genLoopNormalizedSelfTrackPath m p α t z) =
      b (genLoopNormalizedSelfTrackPath n q β t w) := by
  let LX := GenLoop.loopHomeo (X := X) (x := x) (0 : Fin (m + 1))
  let LY := GenLoop.loopHomeo (X := Y) (x := y) (0 : Fin (n + 1))
  change a ((loopNormalizedSelfTrack (LX.toHomotopyEquiv.toFun p)
      (α.map LX.toHomotopyEquiv.toFun.continuous) t (z 0)) ((Cube.splitAt 0 z).2)) =
    b ((loopNormalizedSelfTrack (LY.toHomotopyEquiv.toFun q)
      (β.map LY.toHomotopyEquiv.toFun.continuous) t (w 0)) ((Cube.splitAt 0 w).2))
  rw [← h₀]
  refine loopNormalizedSelfTrack_pointwise
    (fun r : GenLoop {j : Fin (m + 1) // j ≠ 0} X x => a (r ((Cube.splitAt 0 z).2)))
    (fun r : GenLoop {j : Fin (n + 1) // j ≠ 0} Y y => b (r ((Cube.splitAt 0 w).2)))
    (LX.toHomotopyEquiv.toFun p) (LY.toHomotopyEquiv.toFun q)
    (α.map LX.toHomotopyEquiv.toFun.continuous)
    (β.map LY.toHomotopyEquiv.toFun.continuous) ?_ ?_ t (z 0)
  · intro s
    change a (p (Cube.insertAt 0 (s, (Cube.splitAt 0 z).2))) =
      b (q (Cube.insertAt 0 (s, (Cube.splitAt 0 w).2)))
    simpa only [cube_insertAt_splitAt] using hp s
  · intro r s
    change a (α r (Cube.insertAt 0 (s, (Cube.splitAt 0 z).2))) =
      b (β r (Cube.insertAt 0 (s, (Cube.splitAt 0 w).2)))
    simpa only [cube_insertAt_splitAt] using hα r s

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Loop a whole self-homotopy while retaining its original time parameter. -/
def loopedHomotopy (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (hH : ∀ t, H (t, x) = x) :
    (ContinuousMap.id (Path x x)).Homotopy (ContinuousMap.id (Path x x)) where
  toFun z :=
    { toFun := fun s => H (z.1, z.2 s)
      continuous_toFun := H.continuous.comp (continuous_const.prodMk z.2.continuous)
      source' := by rw [z.2.source]; exact hH z.1
      target' := by rw [z.2.target]; exact hH z.1 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval × Path x x) × unitInterval =>
      H (z.1.1, z.1.2 z.2))
    fun_prop
  map_zero_left γ := by
    ext s
    exact H.apply_zero (γ s)
  map_one_left γ := by
    ext s
    exact H.apply_one (γ s)

/-- The looped homotopy fixes the actual constant loop at every original time. -/
theorem loopedHomotopy_based (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (hH : ∀ t, H (t, x) = x) (t : unitInterval) :
    loopedHomotopy H hH (t, Path.refl x) = Path.refl x := by
  ext s
  exact hH t


variable (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
  (hH : ∀ t, H (t, x) = x)

private theorem curry_coordinate (z : Fin 1 → unitInterval) (r s : unitInterval) :
    Fin.cons r (Function.update z 0 s) =
      cubeCoordinateSwap (0 : Fin 2) 1 (Function.update (Fin.cons (z 0) (fun _ => r)) 0 s) := by
  funext i
  fin_cases i <;> simp [cubeCoordinateSwap]

private theorem normalization_curry_transpose
    (p : GenLoop (Fin 2) X x) (t r : unitInterval) (z : Fin 1 → unitInterval) :
    genLoopNormalizedSelfTrackPath 0 (loopCurry p)
        (IdentityTrack.track (loopedHomotopy H hH) (loopedHomotopy_based H hH) 0
          (loopCurry p)) t z r =
      genLoopNormalizedSelfTrackPath 1 (transposeGenLoop 0 1 Fin.zero_ne_one p)
        (IdentityTrack.track H hH 1 (transposeGenLoop 0 1 Fin.zero_ne_one p)) t
          (Fin.cons (z 0) (fun _ => r)) := by
  refine normalizedPath_pointwise (fun γ : Path x x => γ r) id 0 1
    (loopCurry p) (transposeGenLoop 0 1 Fin.zero_ne_one p) _ _ z
      (Fin.cons (z 0) (fun _ => r)) rfl ?_ ?_ t
  · intro s
    exact congrArg p (curry_coordinate z r s)
  · intro a s
    change H (a, p (Fin.cons r (Function.update z 0 s))) =
      H (a, p (cubeCoordinateSwap 0 1 (Function.update (Fin.cons (z 0) (fun _ => r)) 0 s)))
    exact congrArg (fun w => H (a, p w)) (curry_coordinate z r s)

private theorem cycle_zero (z : Fin 3 → unitInterval) :
    cubeCoordinateSwap (1 : Fin 3) 2 (cubeCoordinateSwap 0 1 z) 0 = z 1 := by
  simp [cubeCoordinateSwap]

private theorem cycle_tail (z : Fin 3 → unitInterval) :
    Fin.tail (cubeCoordinateSwap (1 : Fin 3) 2 (cubeCoordinateSwap 0 1 z)) =
      Fin.cons (z 2) (fun _ => z 0) := by
  funext i
  fin_cases i <;> simp [Fin.tail, cubeCoordinateSwap]

/-- The original looped normalization is literally the even cyclic coordinate
permutation of the normalization of the transposed original input cube. -/
theorem normalizedCube_loopUncurry (p : GenLoop (Fin 2) X x) :
    loopUncurry (genLoopNormalizedSelfTrackCube 0 (loopCurry p)
      (IdentityTrack.track (loopedHomotopy H hH) (loopedHomotopy_based H hH) 0
        (loopCurry p))) =
      transposeGenLoop (0 : Fin 3) 1 (by decide)
        (transposeGenLoop (1 : Fin 3) 2 (by decide)
          (genLoopNormalizedSelfTrackCube 1 (transposeGenLoop 0 1 Fin.zero_ne_one p)
            (IdentityTrack.track H hH 1 (transposeGenLoop 0 1 Fin.zero_ne_one p)))) := by
  ext z
  change genLoopNormalizedSelfTrackPath 0 (loopCurry p)
      (IdentityTrack.track (loopedHomotopy H hH) (loopedHomotopy_based H hH) 0
        (loopCurry p)) (z 1) (Fin.tail (Fin.tail z)) (z 0) =
    genLoopNormalizedSelfTrackPath 1 (transposeGenLoop 0 1 Fin.zero_ne_one p)
      (IdentityTrack.track H hH 1 (transposeGenLoop 0 1 Fin.zero_ne_one p))
      (cubeCoordinateSwap 1 2 (cubeCoordinateSwap 0 1 z) 0)
      (Fin.tail (cubeCoordinateSwap 1 2 (cubeCoordinateSwap 0 1 z)))
  rw [cycle_zero, cycle_tail]
  exact normalization_curry_transpose H hH p (z 1) (z 0) (Fin.tail (Fin.tail z))

private theorem normalizedCube_loopUncurry_class (p : GenLoop (Fin 2) X x) :
    (⟦loopUncurry (genLoopNormalizedSelfTrackCube 0 (loopCurry p)
      (IdentityTrack.track (loopedHomotopy H hH) (loopedHomotopy_based H hH) 0
        (loopCurry p)))⟧ : HomotopyGroup.Pi 3 X x) =
      genLoopSelfTrackClass 1 (transposeGenLoop 0 1 Fin.zero_ne_one p)
        (IdentityTrack.track H hH 1 (transposeGenLoop 0 1 Fin.zero_ne_one p)) := by
  let q := genLoopNormalizedSelfTrackCube 1 (transposeGenLoop 0 1 Fin.zero_ne_one p)
    (IdentityTrack.track H hH 1 (transposeGenLoop 0 1 Fin.zero_ne_one p))
  have ht : (⟦transposeGenLoop (0 : Fin 3) 1 (by decide)
      (transposeGenLoop (1 : Fin 3) 2 (by decide) q)⟧ : HomotopyGroup.Pi 3 X x) =
      (⟦q⟧ : HomotopyGroup.Pi 3 X x) :=
    (transposeGenLoop_class (0 : Fin 3) 1 (by decide) _).trans
      ((congrArg (fun a : HomotopyGroup.Pi 3 X x => a⁻¹)
        (transposeGenLoop_class (1 : Fin 3) 2 (by decide) q)).trans
        (@inv_inv (HomotopyGroup.Pi 3 X x) inferInstance ⟦q⟧))
  exact (congrArg (fun q : GenLoop (Fin 3) X x => (⟦q⟧ : HomotopyGroup.Pi 3 X x))
    (normalizedCube_loopUncurry H hH p)).trans
      (ht.trans (genLoopNormalizedSelfTrackCube_class 1 _ _))

/-- The inverse original loop-degree shift retains the input-transposition sign. -/
theorem operation_loopShift_symm (a : HomotopyGroup.Pi 2 X x) :
    (loopShiftMulEquiv (x := x) 1).symm
      (IdentityTrack.operation (loopedHomotopy H hH) (loopedHomotopy_based H hH) 0
        (loopShiftMulEquiv 0 a)) =
      (IdentityTrack.operation H hH 1 a)⁻¹ := by
  refine Quotient.inductionOn a ?_
  intro p
  change (loopShiftMulEquiv (x := x) 1).symm
      (genLoopSelfTrackClass 0 (loopCurry p)
        (IdentityTrack.track (loopedHomotopy H hH) (loopedHomotopy_based H hH) 0
          (loopCurry p))) = _
  rw [← genLoopNormalizedSelfTrackCube_class]
  change (⟦loopUncurry (genLoopNormalizedSelfTrackCube 0 (loopCurry p)
    (IdentityTrack.track (loopedHomotopy H hH) (loopedHomotopy_based H hH) 0
      (loopCurry p)))⟧ : HomotopyGroup.Pi 3 X x) = _
  rw [normalizedCube_loopUncurry_class]
  change IdentityTrack.hom H hH 0 (⟦transposeGenLoop 0 1 Fin.zero_ne_one p⟧) = _
  exact (congrArg (IdentityTrack.hom H hH 0)
    (transposeGenLoop_class (0 : Fin 2) 1 Fin.zero_ne_one p)).trans
      ((IdentityTrack.hom H hH 0).map_inv (⟦p⟧ : HomotopyGroup.Pi 2 X x))

/-- The actual loop-degree shift anti-commutes with the original self-track
operation. The sign follows from the literal normalized cubes. -/
theorem operation_loopShift (a : HomotopyGroup.Pi 2 X x) :
    loopShiftMulEquiv 1 (IdentityTrack.operation H hH 1 a) =
      (IdentityTrack.operation (loopedHomotopy H hH) (loopedHomotopy_based H hH) 0
        (loopShiftMulEquiv 0 a))⁻¹ := by
  apply (loopShiftMulEquiv (x := x) 1).symm.injective
  rw [MulEquiv.symm_apply_apply, map_inv, operation_loopShift_symm, inv_inv]

end Topology.IdentityTrack
