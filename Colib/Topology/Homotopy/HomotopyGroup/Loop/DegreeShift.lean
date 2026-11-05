/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.Nullhomotopy

/-!
# The loop-space degree shift

Currying the first coordinate of a based cube gives the actual equivalence
between `π_(n+1) X` and `π_n (ΩX)`. Homotopies are curried and uncurried
relative to the whole cube boundary. In positive outer degree the equivalence
preserves the existing homotopy-group multiplication.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/Loop/DegreeShift.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space models,
basepoint tracks, maps and universe parameters are retained. -/
@[expose] public section


noncomputable section
open scoped Topology unitInterval
open unitInterval

universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem continuous_finCons {Z : Type*} [TopologicalSpace Z] {n : ℕ}
    {a : Z → I} {b : Z → (Fin n → I)} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun z => (Fin.cons (a z) (b z) : Fin (n + 1) → I)) := by
  apply continuous_pi
  intro i
  cases i using Fin.cases with
  | zero => simpa using ha
  | succ i =>
    change Continuous (fun z => b z i)
    exact (continuous_apply i).comp hb

/-- Turn the first coordinate of a based cube into the loop parameter. -/
def loopCurry {n : ℕ} (p : GenLoop (Fin (n + 1)) X x) :
    GenLoop (Fin n) (Path x x) (Path.refl x) :=
  ⟨⟨fun z =>
    { toFun t := p (Fin.cons t z)
      continuous_toFun := p.val.continuous.comp
        (continuous_finCons continuous_id continuous_const)
      source' := p.property _ ⟨0, Or.inl (Fin.cons_zero _ _)⟩
      target' := p.property _ ⟨0, Or.inr (Fin.cons_zero _ _)⟩ }, by
    apply Path.continuous_uncurry_iff.mp
    exact p.val.continuous.comp (continuous_finCons continuous_snd continuous_fst)⟩, by
    rintro z ⟨i, hi⟩
    ext t
    exact p.property _ ⟨i.succ, hi⟩⟩

/-- Evaluate a cube of loops using the first coordinate as its loop parameter. -/
def loopUncurry {n : ℕ} (p : GenLoop (Fin n) (Path x x) (Path.refl x)) :
    GenLoop (Fin (n + 1)) X x :=
  ⟨⟨fun z => p (Fin.tail z) (z 0), by
    apply Continuous.eval
    · exact p.val.continuous.comp (by fun_prop)
    · fun_prop⟩, by
    rintro z ⟨i, hi⟩
    change p (Fin.tail z) (z 0) = x
    cases i using Fin.cases with
    | zero =>
      rcases hi with hi | hi
      · rw [hi]; exact (p (Fin.tail z)).source
      · rw [hi]; exact (p (Fin.tail z)).target
    | succ i =>
      have hz : Fin.tail z ∈ Cube.boundary (Fin n) := ⟨i, hi⟩
      have hp : p (Fin.tail z) = Path.refl x := p.property _ hz
      rw [hp]
      rfl⟩

@[simp]
theorem loopUncurry_loopCurry {n : ℕ} (p : GenLoop (Fin (n + 1)) X x) :
    loopUncurry (loopCurry p) = p := by
  ext z
  change p (Fin.cons (z 0) (Fin.tail z)) = p z
  rw [Fin.cons_self_tail]

@[simp]
theorem loopCurry_loopUncurry {n : ℕ} (p : GenLoop (Fin n) (Path x x) (Path.refl x)) :
    loopCurry (loopUncurry p) = p := by
  ext z t
  change p (Fin.tail (Fin.cons t z : Fin (n + 1) → I)) ((Fin.cons t z : Fin (n + 1) → I) 0) = p z t
  simp

/-- The coordinate-currying equivalence before passing to homotopy classes. -/
def loopCurryEquiv (n : ℕ) :
    GenLoop (Fin (n + 1)) X x ≃ GenLoop (Fin n) (Path x x) (Path.refl x) where
  toFun := loopCurry
  invFun := loopUncurry
  left_inv := loopUncurry_loopCurry
  right_inv := loopCurry_loopUncurry

/-- Curry a boundary-relative cube homotopy into a boundary-relative homotopy
of cubes in the based loop space. -/
def loopCurryHomotopy {n : ℕ} {p q : GenLoop (Fin (n + 1)) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin (n + 1)))) :
    (loopCurry p).val.HomotopyRel (loopCurry q).val (Cube.boundary (Fin n)) where
  toFun z :=
    { toFun t := H (z.1, Fin.cons t z.2)
      continuous_toFun := H.continuous.comp (continuous_const.prodMk
        (continuous_finCons continuous_id continuous_const))
      source' := (H.eq_fst z.1 ⟨0, Or.inl (Fin.cons_zero _ _)⟩).trans
        (p.property _ ⟨0, Or.inl (Fin.cons_zero _ _)⟩)
      target' := (H.eq_fst z.1 ⟨0, Or.inr (Fin.cons_zero _ _)⟩).trans
        (p.property _ ⟨0, Or.inr (Fin.cons_zero _ _)⟩) }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact H.continuous.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_finCons continuous_snd (continuous_snd.comp continuous_fst)))
  map_zero_left z := by
    ext t
    exact H.apply_zero (Fin.cons t z)
  map_one_left z := by
    ext t
    exact H.apply_one (Fin.cons t z)
  prop' s z hz := by
    ext t
    obtain ⟨i, hi⟩ := hz
    exact H.eq_fst s ⟨i.succ, hi⟩

/-- Uncurry a loop-space cube homotopy, retaining the relative boundary condition. -/
def loopUncurryHomotopy {n : ℕ}
    {p q : GenLoop (Fin n) (Path x x) (Path.refl x)}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) :
    (loopUncurry p).val.HomotopyRel (loopUncurry q).val (Cube.boundary (Fin (n + 1))) where
  toFun z := H (z.1, Fin.tail z.2) (z.2 0)
  continuous_toFun := by
    apply Continuous.eval
    · exact H.continuous.comp (by fun_prop)
    · fun_prop
  map_zero_left z := by
    rw [H.apply_zero]
    rfl
  map_one_left z := by
    rw [H.apply_one]
    rfl
  prop' s z hz := by
    rcases hz with ⟨i, hi⟩
    cases i using Fin.cases with
    | zero =>
      rcases hi with hi | hi
      · change H (s, Fin.tail z) (z 0) = p (Fin.tail z) (z 0)
        rw [hi, Path.source, Path.source]
      · change H (s, Fin.tail z) (z 0) = p (Fin.tail z) (z 0)
        rw [hi, Path.target, Path.target]
    | succ i =>
      change H (s, Fin.tail z) (z 0) = p (Fin.tail z) (z 0)
      rw [H.eq_fst s (show Fin.tail z ∈ Cube.boundary (Fin n) from ⟨i, hi⟩)]
      rfl

/-- Genuine loop-space degree shift, including the zeroth homotopy set. -/
def loopShiftEquiv (n : ℕ) :
    HomotopyGroup.Pi (n + 1) X x ≃ HomotopyGroup.Pi n (Path x x) (Path.refl x) :=
  Quotient.congr (loopCurryEquiv n) (by
    intro p q
    constructor
    · rintro ⟨H⟩
      exact ⟨loopCurryHomotopy H⟩
    · rintro ⟨H⟩
      have hh := loopUncurryHomotopy H
      change GenLoop.Homotopic p q
      simpa using (show GenLoop.Homotopic (loopUncurry (loopCurry p))
        (loopUncurry (loopCurry q)) from ⟨hh⟩))

@[simp]
theorem loopShiftEquiv_mk (n : ℕ) (p : GenLoop (Fin (n + 1)) X x) :
    loopShiftEquiv n (Quotient.mk' p) = Quotient.mk' (loopCurry p) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Currying respects concatenation in each of the remaining cube coordinates. -/
theorem loopCurry_transAt {n : ℕ} (i : Fin n) (p q : GenLoop (Fin (n + 1)) X x) :
    loopCurry (GenLoop.transAt i.succ p q) =
      GenLoop.transAt i (loopCurry p) (loopCurry q) := by
  ext z t
  simp only [loopCurry, GenLoop.transAt, GenLoop.coe_copy, GenLoop.mk_apply,
    ContinuousMap.coe_mk, Path.coe_mk_mk, Fin.cons_succ]
  split_ifs <;> simp only [Fin.cons_update] <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-shift equivalence preserves the genuine homotopy-group product. -/
theorem loopShiftEquiv_mul (n : ℕ) (a b : HomotopyGroup.Pi (n + 2) X x) :
    loopShiftEquiv (n + 1) (a * b) = loopShiftEquiv (n + 1) a * loopShiftEquiv (n + 1) b := by
  refine Quotient.inductionOn₂ a b (fun p q => ?_)
  exact (congrArg (loopShiftEquiv (n + 1))
    (HomotopyGroup.mul_spec (i := (0 : Fin (n + 1)).succ) (p := p) (q := q))).trans
      ((congrArg Quotient.mk' (loopCurry_transAt (0 : Fin (n + 1)) q p)).trans
        (HomotopyGroup.mul_spec (i := (0 : Fin (n + 1)))
          (p := loopCurry p) (q := loopCurry q)).symm)

/-- The actual loop-degree shift as a group isomorphism in positive outer degree. -/
def loopShiftMulEquiv (n : ℕ) :
    HomotopyGroup.Pi (n + 2) X x ≃* HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x) where
  toEquiv := loopShiftEquiv (n + 1)
  map_mul' := loopShiftEquiv_mul n

section Naturality
variable {Y : Type*} [TopologicalSpace Y] {y : Y}

/-- A based continuous map acts continuously on the based loop spaces. -/
def basedLoopMap (f : C(X, Y)) (h : f x = y) : C(Path x x, Path y y) where
  toFun γ := (γ.map f.continuous).cast h.symm h.symm
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : Path x x × I => f (z.1 z.2))
    fun_prop

@[simp]
theorem basedLoopMap_refl (f : C(X, Y)) (h : f x = y) :
    basedLoopMap f h (Path.refl x) = Path.refl y := by
  ext t
  exact h

/-- Coordinate currying commutes strictly with postcomposition. -/
@[simp]
theorem loopCurry_postcomp {n : ℕ} (f : C(X, Y)) (h : f x = y)
    (p : GenLoop (Fin (n + 1)) X x) :
    loopCurry (GenLoop.postcomp f h p) =
      GenLoop.postcomp (basedLoopMap f h) (basedLoopMap_refl f h) (loopCurry p) := by
  ext z t
  rfl

/-- Naturality of the loop-space degree shift on the actual homotopy quotients. -/
theorem loopShiftEquiv_natural (n : ℕ) (f : C(X, Y)) (h : f x = y)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    loopShiftEquiv n (HomotopyGroup.map f h a) =
      HomotopyGroup.map (basedLoopMap f h) (basedLoopMap_refl f h) (loopShiftEquiv n a) := by
  refine Quotient.inductionOn a (fun p => ?_)
  exact congrArg Quotient.mk' (loopCurry_postcomp f h p)

/-- The group-valued degree shift identifies the map induced on loop spaces
with the map induced on the next homotopy degree. -/
theorem loopShiftMulEquiv_natural (n : ℕ) (f : C(X, Y)) (h : f x = y) :
    (HomotopyGroup.piMap n (basedLoopMap f h) (basedLoopMap_refl f h)).comp
      (loopShiftMulEquiv (x := x) n).toMonoidHom =
    (loopShiftMulEquiv (x := y) n).toMonoidHom.comp (HomotopyGroup.piMap (n + 1) f h) := by
  ext a
  exact (loopShiftEquiv_natural (n + 1) f h a).symm

end Naturality
end Topology
