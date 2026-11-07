/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.ComponentTranslation
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Bounded self-tracks of original based cubes

A boundary-relative cube homotopy is an actual path in the existing generalized-loop
space. Vanishing of the next homotopy group makes every self-track null, including
self-tracks based at a nonconstant cube. The original loop-space component translation
handles that component; no nullhomotopy of the cube itself is assumed. The final
evaluation helper keeps both track endpoints and the whole spatial boundary fixed.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/GenLoopSelfTrack.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, basepoints,
coordinate order and signs are retained under native Colib ownership. -/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u v w

namespace Topology

variable {N : Type w} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- Original postcomposition, with its existing generalized-loop-space topology. -/
def genLoopPostcompContinuousMap (f : C(X, Y)) (hf : f x = y) :
    C(GenLoop N X x, GenLoop N Y y) where
  toFun := GenLoop.postcomp f hf
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _

@[simp] theorem genLoopPostcompContinuousMap_apply (f : C(X, Y)) (hf : f x = y)
    (p : GenLoop N X x) (z : N → unitInterval) :
    genLoopPostcompContinuousMap f hf p z = f (p z) := rfl

/-- A relative homotopy is a genuine path in the original generalized-loop space. -/
def genLoopPathOfHomotopyRel {p q : GenLoop N X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary N)) : Path p q where
  toFun r := ⟨H.toHomotopy.curry r,
    fun z hz ↦ (H.eq_fst r hz).trans (p.property z hz)⟩
  continuous_toFun := H.toHomotopy.curry.continuous.subtype_mk _
  source' := by ext z; exact H.apply_zero z
  target' := by ext z; exact H.apply_one z

/-- Neither the homotopy time nor any cube coordinate is reparametrized. -/
@[simp] theorem genLoopPathOfHomotopyRel_apply {p q : GenLoop N X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary N))
    (r : unitInterval) (z : N → unitInterval) :
    genLoopPathOfHomotopyRel H r z = H (r, z) := rfl

theorem genLoopPathOfHomotopyRel_apply_zero {p q : GenLoop N X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary N)) (z : N → unitInterval) :
    genLoopPathOfHomotopyRel H 0 z = p z := H.apply_zero z

theorem genLoopPathOfHomotopyRel_apply_one {p q : GenLoop N X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary N)) (z : N → unitInterval) :
    genLoopPathOfHomotopyRel H 1 z = q z := H.apply_one z

theorem genLoopPathOfHomotopyRel_boundary {p q : GenLoop N X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary N)) (r : unitInterval)
    (z : N → unitInterval) (hz : z ∈ Cube.boundary N) :
    genLoopPathOfHomotopyRel H r z = x :=
  (genLoopPathOfHomotopyRel H r).property z hz

/-- Swap a based path of cubes into a cube of based paths, keeping both parameters literal. -/
def genLoopOfBasedPath
    (P : Path (GenLoop.const : GenLoop N X x) GenLoop.const) :
    GenLoop N (Path x x) (Path.refl x) :=
  ⟨⟨fun z ↦
    { toFun s := P s z
      continuous_toFun := Continuous.eval P.continuous continuous_const
      source' := congrArg (fun q : GenLoop N X x ↦ q z) P.source
      target' := congrArg (fun q : GenLoop N X x ↦ q z) P.target }, by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (N → unitInterval) × unitInterval ↦ P z.2 z.1)
    fun_prop⟩, by
    intro z hz
    ext s
    exact (P s).property z hz⟩

@[simp] theorem genLoopOfBasedPath_apply
    (P : Path (GenLoop.const : GenLoop N X x) GenLoop.const)
    (z : N → unitInterval) (s : unitInterval) :
    genLoopOfBasedPath P z s = P s z := rfl

@[simp] theorem genLoopOfBasedPath_refl :
    genLoopOfBasedPath (Path.refl (GenLoop.const : GenLoop N X x)) = GenLoop.const := by
  ext z s
  rfl

/-- Endpoint-fixed homotopies of paths give whole-boundary-fixed homotopies after the swap. -/
def genLoopOfBasedPathHomotopy
    {P Q : Path (GenLoop.const : GenLoop N X x) GenLoop.const}
    (K : P.Homotopy Q) :
    (genLoopOfBasedPath P).val.HomotopyRel (genLoopOfBasedPath Q).val (Cube.boundary N) where
  toFun rz :=
    { toFun s := K (rz.1, s) rz.2
      continuous_toFun := Continuous.eval
        (K.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const
      source' := congrArg (fun q : GenLoop N X x ↦ q rz.2) (K.source rz.1)
      target' := congrArg (fun q : GenLoop N X x ↦ q rz.2) (K.target rz.1) }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval × (N → unitInterval)) × unitInterval ↦
      K (z.1.1, z.2) z.1.2)
    fun_prop
  map_zero_left z := by
    ext s
    exact congrArg (fun q : GenLoop N X x ↦ q z) (K.apply_zero s)
  map_one_left z := by
    ext s
    exact congrArg (fun q : GenLoop N X x ↦ q z) (K.apply_one s)
  prop' r z hz := by
    ext s
    exact ((K (r, s)).property z hz).trans ((P s).property z hz).symm

theorem genLoopOfBasedPath_homotopic
    {P Q : Path (GenLoop.const : GenLoop N X x) GenLoop.const}
    (h : P.Homotopic Q) : GenLoop.Homotopic (genLoopOfBasedPath P) (genLoopOfBasedPath Q) := by
  obtain ⟨K⟩ := h
  exact ⟨genLoopOfBasedPathHomotopy K⟩

/-- Vanishing of the next homotopy group controls the actual fundamental group at every
positive-dimensional based cube, even in a nonconstant component of the cube space. -/
theorem fundamentalGroup_genLoop_subsingleton (m : ℕ)
    (h : Subsingleton (HomotopyGroup.Pi (m + 2) X x))
    (p : GenLoop (Fin (m + 1)) X x) :
    Subsingleton (FundamentalGroup (GenLoop (Fin (m + 1)) X x) p) := by
  let G := GenLoop (Fin (m + 1)) X x
  let c : G := GenLoop.const
  let M := {j : Fin (m + 2) // j ≠ (0 : Fin (m + 2))}
  let e : GenLoop M X x ≃ₜ G :=
    GenLoop.congr x (finSuccAboveEquiv (0 : Fin (m + 2))).symm
  have he : e GenLoop.const = c := by ext z; rfl
  let : Subsingleton (HomotopyGroup.Pi (m + 2) X x) := h
  let : Subsingleton (FundamentalGroup (GenLoop M X x) GenLoop.const) :=
    (homotopyGroupEquivFundamentalGroup (X := X) (x := x)
      (0 : Fin (m + 2))).symm.injective.subsingleton
  let : Subsingleton (HomotopyGroup.Pi 1 (GenLoop M X x) GenLoop.const) :=
    (HomotopyGroup.pi1EquivFundamentalGroup
      (X := GenLoop M X x) (x := GenLoop.const)).injective.subsingleton
  let : Subsingleton (HomotopyGroup.Pi 1 G c) :=
    (homotopyEquivPiEquiv e.toHomotopyEquiv he 0).symm.injective.subsingleton
  let B := GenLoop {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x
  let b : B := GenLoop.const
  let L : G ≃ₜ Path b b := GenLoop.loopHomeo (X := X) (x := x) (0 : Fin (m + 1))
  have hL : L c = Path.refl b := by ext s z; rfl
  let : Subsingleton (HomotopyGroup.Pi 1 (Path b b) (Path.refl b)) :=
    (homotopyEquivPiEquiv L.toHomotopyEquiv hL 0).symm.injective.subsingleton
  let : Subsingleton (HomotopyGroup.Pi 1 (Path b b) (L p)) :=
    (loopComponentHomotopyEquiv (L p) 1).symm.injective.subsingleton
  let : Subsingleton (HomotopyGroup.Pi 1 G p) :=
    (homotopyEquivPiEquiv L.toHomotopyEquiv (x := p) (y := L p) rfl 0).injective.subsingleton
  exact (HomotopyGroup.pi1EquivFundamentalGroup (X := G) (x := p)).symm.injective.subsingleton

/-- A self-track of an original positive-dimensional based cube contracts relative to its
two track endpoints. No nullhomotopy of the cube itself is required. -/
theorem genLoop_selfTrack_homotopic_refl (m : ℕ)
    (h : Subsingleton (HomotopyGroup.Pi (m + 2) X x))
    (p : GenLoop (Fin (m + 1)) X x)
    (H : p.val.HomotopyRel p.val (Cube.boundary (Fin (m + 1)))) :
    (genLoopPathOfHomotopyRel H).Homotopic (Path.refl p) := by
  apply Path.Homotopic.Quotient.exact
  exact (fundamentalGroup_genLoop_subsingleton m h p).elim _ _

/-- Evaluate a contracted self-track on its original cube. The result is relative to both
time endpoints and every spatial boundary point, suitable for compact relative descent. -/
def genLoopSelfTrackContraction {p : GenLoop N X x}
    (H : p.val.HomotopyRel p.val (Cube.boundary N))
    (K : (genLoopPathOfHomotopyRel H).Homotopy (Path.refl p)) :
    H.toHomotopy.toContinuousMap.HomotopyRel
      (p.val.comp ⟨Prod.snd, continuous_snd⟩)
      {z : unitInterval × (N → unitInterval) |
        z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ Cube.boundary N} where
  toFun z := K (z.1, z.2.1) z.2.2
  continuous_toFun := Continuous.eval
    (K.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
    (continuous_snd.comp continuous_snd)
  map_zero_left z :=
    congrArg (fun q : GenLoop N X x ↦ q z.2) (K.apply_zero z.1)
  map_one_left z :=
    congrArg (fun q : GenLoop N X x ↦ q z.2) (K.apply_one z.1)
  prop' s z hz := by
    rcases hz with hz | hz | hz
    · change K (s, z.1) z.2 = H (z.1, z.2)
      rw [hz, K.source, H.apply_zero]
      rfl
    · change K (s, z.1) z.2 = H (z.1, z.2)
      rw [hz, K.target, H.apply_one]
      rfl
    · exact ((K (s, z.1)).property z.2 hz).trans
        ((H.eq_fst z.1 hz).trans (p.property z.2 hz)).symm

@[simp] theorem genLoopSelfTrackContraction_apply {p : GenLoop N X x}
    (H : p.val.HomotopyRel p.val (Cube.boundary N))
    (K : (genLoopPathOfHomotopyRel H).Homotopy (Path.refl p))
    (s t : unitInterval) (z : N → unitInterval) :
    genLoopSelfTrackContraction H K (s, (t, z)) = K (s, t) z := rfl

end Topology
