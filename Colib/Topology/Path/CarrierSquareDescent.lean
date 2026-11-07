/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.ThreeSideSquareLift
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-! Exact carrier square descent from an already supplied whole boundary comparison. -/
/-! Implementation source: `Quillen/Topology/Path/CarrierSquareDescent.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, coordinates,
whole boundary traces and universe parameters are retained with native owners.
The literal square data are extracted from `CarrierSquareBoundary.lean`, lines 27–36,
at the same revision; unrelated terminal-pause results are not imported.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Topology.CarrierPathSquare
variable {X : Type u} [TopologicalSpace X] {a₀ b₀ a₁ b₁ : X}
  {p₀ : Path a₀ b₀} {p₁ : Path a₁ b₁} {l : Path a₀ a₁} {m : Path b₀ b₁}

/-- A continuous carrier square with all four literal path boundaries. -/
structure Square (p₀ : Path a₀ b₀) (p₁ : Path a₁ b₁)
    (l : Path a₀ a₁) (m : Path b₀ b₁) where
  /-- The original continuous square, with its two coordinates unchanged. -/
  parameter : C(unitInterval × unitInterval, X)
  at_zero (s : unitInterval) : parameter (0, s) = p₀ s
  at_one (s : unitInterval) : parameter (1, s) = p₁ s
  left (r : unitInterval) : parameter (r, 0) = l r
  right (r : unitInterval) : parameter (r, 1) = m r

private theorem path_pasted_left (p : Path a₁ b₁) (l : Path a₀ a₁) (m : Path b₀ b₁)
    (r : unitInterval) :
    ((l.trans p).trans m.symm) (Topology.ThreeSideSquare.leftTime r) = l r := by
  rw [Path.trans_apply]
  split
  · rw [Path.trans_apply]
    split
    · congr 1
      apply Subtype.ext
      dsimp [Topology.ThreeSideSquare.leftTime]
      ring
    · rename_i h
      dsimp [Topology.ThreeSideSquare.leftTime] at h
      linarith [r.2.2]
  · rename_i h
    dsimp [Topology.ThreeSideSquare.leftTime] at h
    linarith [r.2.2]

private theorem path_pasted_top (p : Path a₁ b₁) (l : Path a₀ a₁) (m : Path b₀ b₁)
    (s : unitInterval) :
    ((l.trans p).trans m.symm) (Topology.ThreeSideSquare.topTime s) = p s := by
  rw [Path.trans_apply]
  split
  · rw [Path.trans_apply]
    split
    · rename_i h
      have hs : s = 0 := by
        apply Subtype.ext
        change (s : ℝ) = 0
        dsimp [Topology.ThreeSideSquare.topTime] at h
        linarith [s.2.1]
      subst s
      trans l 1
      · congr 1
        apply Subtype.ext
        norm_num [Topology.ThreeSideSquare.topTime]
      · exact l.target.trans p.source.symm
    · congr 1
      apply Subtype.ext
      dsimp [Topology.ThreeSideSquare.topTime]
      ring
  · rename_i h
    dsimp [Topology.ThreeSideSquare.topTime] at h
    linarith [s.2.2]

private theorem path_pasted_right (p : Path a₁ b₁) (l : Path a₀ a₁) (m : Path b₀ b₁)
    (r : unitInterval) :
    ((l.trans p).trans m.symm) (Topology.ThreeSideSquare.rightTime r) = m r := by
  rw [Path.trans_apply]
  split
  · rename_i h
    have hr : r = 1 := by
      apply Subtype.ext
      change (r : ℝ) = 1
      dsimp [Topology.ThreeSideSquare.rightTime] at h
      linarith [r.2.2]
    subst r
    trans (l.trans p) 1
    · congr 1
      apply Subtype.ext
      norm_num [Topology.ThreeSideSquare.rightTime]
    · exact (l.trans p).target.trans m.target.symm
  · change m (unitInterval.symm _) = _
    congr 1
    apply Subtype.ext
    dsimp [Topology.ThreeSideSquare.rightTime, unitInterval.symm]
    ring

/-- The supplied boundary comparison as a family with a trivial extra parameter. -/
def boundaryFamily (J : p₀.Homotopy ((l.trans p₁).trans m.symm)) :
    C((unitInterval × unitInterval) × Unit, X) :=
  ⟨fun z ↦ J z.1, by fun_prop⟩

/-- The whole source endpoint is constant along the collapsed left edge. -/
theorem boundaryFamily_left (J : p₀.Homotopy ((l.trans p₁).trans m.symm))
    (r : unitInterval) (x : Unit) :
    boundaryFamily J ((r, 0), x) = boundaryFamily J ((0, 0), x) :=
  (J.source r).trans (J.source 0).symm

/-- The whole target endpoint is constant along the collapsed right edge. -/
theorem boundaryFamily_right (J : p₀.Homotopy ((l.trans p₁).trans m.symm))
    (r : unitInterval) (x : Unit) :
    boundaryFamily J ((r, 1), x) = boundaryFamily J ((0, 1), x) :=
  (J.target r).trans (J.target 0).symm

/-- Descent is jointly continuous by the original compact quotient, without a continuous inverse. -/
def boundaryParameter (J : p₀.Homotopy ((l.trans p₁).trans m.symm)) :
    C(unitInterval × unitInterval, X) :=
  (ThreeSideSquare.liftFamily (boundaryFamily J)
    (boundaryFamily_left J) (boundaryFamily_right J)).comp
      ⟨fun z ↦ (z, ()), by fun_prop⟩

/-- Every original comparison value is recovered under the literal collapse. -/
theorem boundaryParameter_collapse (J : p₀.Homotopy ((l.trans p₁).trans m.symm))
    (z : unitInterval × unitInterval) :
    boundaryParameter J (ThreeSideSquare.collapse z) = J z :=
  ThreeSideSquare.liftFamily_collapse (boundaryFamily J)
    (boundaryFamily_left J) (boundaryFamily_right J) z ()

/-- The supplied comparison determines all four whole edges and the entire descended interior. -/
def boundarySquare (J : p₀.Homotopy ((l.trans p₁).trans m.symm)) : Square p₀ p₁ l m where
  parameter := boundaryParameter J
  at_zero s := by
    have h := boundaryParameter_collapse J (0, s)
    rw [ThreeSideSquare.collapse_zero] at h
    exact h.trans (J.toHomotopy.map_zero_left s)
  at_one s := by
    have h := boundaryParameter_collapse J (1, ThreeSideSquare.topTime s)
    rw [ThreeSideSquare.collapse_topTime] at h
    exact h.trans ((J.toHomotopy.map_one_left _).trans (path_pasted_top p₁ l m s))
  left r := by
    have h := boundaryParameter_collapse J (1, ThreeSideSquare.leftTime r)
    rw [ThreeSideSquare.collapse_leftTime] at h
    exact h.trans ((J.toHomotopy.map_one_left _).trans (path_pasted_left p₁ l m r))
  right r := by
    have h := boundaryParameter_collapse J (1, ThreeSideSquare.rightTime r)
    rw [ThreeSideSquare.collapse_rightTime] at h
    exact h.trans ((J.toHomotopy.map_one_left _).trans (path_pasted_right p₁ l m r))

end Topology.CarrierPathSquare
