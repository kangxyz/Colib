/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.Cube.Rotation
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
A genuine boundary-relative cube rotation identifies an original coordinate transposition with
homotopy-group inversion.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/CoordinateTransposition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology
variable {N : Type v} [DecidableEq N]

/-- Swap the two displayed original cube coordinates. -/
def cubeCoordinateSwap (i j : N) (z : N → unitInterval) : N → unitInterval :=
  fun k ↦ if k = i then z j else if k = j then z i else z k

/-- Rotate after swapping the selected square, retaining every other cube coordinate. -/
def cubeCoordinateRotation (i j : N) (s : unitInterval) (z : N → unitInterval) : N → unitInterval :=
  fun k ↦ if k = i then (squareRotationHomotopy (s,(z j,z i))).1
    else if k = j then (squareRotationHomotopy (s,(z j,z i))).2 else z k

lemma continuous_cubeCoordinateRotation (i j : N) :
    Continuous (fun z : unitInterval × (N → unitInterval) ↦ cubeCoordinateRotation i j z.1 z.2) :=
      by
  have h : Continuous (fun z : unitInterval × (N → unitInterval) ↦
      squareRotationHomotopy (z.1,(z.2 j,z.2 i))) :=
    squareRotationHomotopy.continuous.comp
      (continuous_fst.prodMk (((continuous_apply j).comp continuous_snd).prodMk
        ((continuous_apply i).comp continuous_snd)))
  apply continuous_pi
  intro k
  dsimp only [cubeCoordinateRotation]
  split_ifs
  · exact h.fst
  · exact h.snd
  · exact (continuous_apply k).comp continuous_snd

lemma cubeCoordinateRotation_zero (i j : N) (z : N → unitInterval) :
    cubeCoordinateRotation i j 0 z = cubeCoordinateSwap i j z := by
  funext k
  simp only [cubeCoordinateRotation, cubeCoordinateSwap, ContinuousMap.Homotopy.apply_zero,
    ContinuousMap.id_apply]

lemma cubeCoordinateRotation_one (i j : N) (z : N → unitInterval) :
    cubeCoordinateRotation i j 1 z = fun k ↦ if k = i then unitInterval.symm (z i) else z k := by
  funext k
  by_cases hi : k = i
  · simp [cubeCoordinateRotation, hi, squareRotationHomotopy.apply_one]
  · by_cases hj : k = j
    · simp [cubeCoordinateRotation, hj, squareRotationHomotopy.apply_one]
    · simp [cubeCoordinateRotation, hi, hj]

lemma cubeCoordinateRotation_boundary (i j : N) (hij : i ≠ j)
    (s : unitInterval) (z : N → unitInterval) (hz : z ∈ Cube.boundary N) :
    cubeCoordinateRotation i j s z ∈ Cube.boundary N := by
  obtain ⟨k,hk⟩ := hz
  by_cases hi : k = i
  · subst k
    have hs := squareRotationHomotopy_boundary s (z j,z i)
      (hk.elim (fun h ↦ Or.inr (Or.inr (Or.inl h))) (fun h ↦ Or.inr (Or.inr (Or.inr h))))
    rcases hs with h | h | h | h
    · exact ⟨i, Or.inl (by simpa [cubeCoordinateRotation] using h)⟩
    · exact ⟨i, Or.inr (by simpa [cubeCoordinateRotation] using h)⟩
    · exact ⟨j, Or.inl (by simpa [cubeCoordinateRotation, Ne.symm hij] using h)⟩
    · exact ⟨j, Or.inr (by simpa [cubeCoordinateRotation, Ne.symm hij] using h)⟩
  · by_cases hj : k = j
    · subst k
      have hs := squareRotationHomotopy_boundary s (z j,z i)
        (hk.elim (fun h ↦ Or.inl h) (fun h ↦ Or.inr (Or.inl h)))
      rcases hs with h | h | h | h
      · exact ⟨i, Or.inl (by simpa [cubeCoordinateRotation] using h)⟩
      · exact ⟨i, Or.inr (by simpa [cubeCoordinateRotation] using h)⟩
      · exact ⟨j, Or.inl (by simpa [cubeCoordinateRotation, Ne.symm hij] using h)⟩
      · exact ⟨j, Or.inr (by simpa [cubeCoordinateRotation, Ne.symm hij] using h)⟩
    · exact ⟨k, by simpa [cubeCoordinateRotation, hi, hj] using hk⟩

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The actual coordinate-transposed original based cube. -/
def transposeGenLoop (i j : N) (hij : i ≠ j) (p : GenLoop N X x) : GenLoop N X x :=
  ⟨⟨fun z ↦ p (cubeCoordinateSwap i j z), by
    have h : Continuous (cubeCoordinateSwap i j) := by
      apply continuous_pi
      intro k
      dsimp only [cubeCoordinateSwap]
      split_ifs
      · exact continuous_apply j
      · exact continuous_apply i
      · exact continuous_apply k
    exact p.val.continuous.comp h⟩, by
    intro z hz
    apply p.property
    rw [← cubeCoordinateRotation_zero]
    exact cubeCoordinateRotation_boundary i j hij 0 z hz⟩

/-- Actual square rotation gives a boundary-relative homotopy from swap to reflection. -/
def transposeGenLoopHomotopy (i j : N) (hij : i ≠ j) (p : GenLoop N X x) :
    (transposeGenLoop i j hij p).val.HomotopyRel (GenLoop.symmAt i p).val (Cube.boundary N) where
  toFun z := p (cubeCoordinateRotation i j z.1 z.2)
  continuous_toFun := p.val.continuous.comp (continuous_cubeCoordinateRotation i j)
  map_zero_left z := congrArg p (cubeCoordinateRotation_zero i j z)
  map_one_left z := by
    change p (cubeCoordinateRotation i j 1 z) = p (fun k ↦ if k = i then unitInterval.symm (z i)
      else z k)
    exact congrArg p (cubeCoordinateRotation_one i j z)
  prop' s z hz := (p.property _ (cubeCoordinateRotation_boundary i j hij s z hz)).trans
    ((transposeGenLoop i j hij p).property z hz).symm

/-- Transposition acts by the original group inversion, rather than an assumed orientation sign. -/
theorem transposeGenLoop_class [Nonempty N] (i j : N) (hij : i ≠ j) (p : GenLoop N X x) :
    (Quotient.mk' (transposeGenLoop i j hij p) : HomotopyGroup N X x) = ((Quotient.mk' p)⁻¹ :
      HomotopyGroup N X x) := by
  exact (show (Quotient.mk' (transposeGenLoop i j hij p) : HomotopyGroup N X x) =
      Quotient.mk' (GenLoop.symmAt i p) from
    Quotient.sound ⟨transposeGenLoopHomotopy i j hij p⟩).trans
      (HomotopyGroup.inv_spec (i := i) (p := p)).symm

end Topology
