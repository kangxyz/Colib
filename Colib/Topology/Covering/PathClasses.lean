/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# Path classes and fibers of a simply connected covering space

Given an actual covering map with simply connected total space and a point
in that space, lifting identifies base path classes from the projected point
with points in each fiber. The forward map is actual covering monodromy.
The inverse projects a path in the total space, and the proof uses the
uniqueness of its endpoint-fixed homotopy class.

This does not construct a universal cover or assume that a space of CW type
admits one. Total and base spaces have independent universes.
-/

/-! Implementation source: `Quillen/Topology/Covering/PathClasses.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual topologies,
path classes, dependent endpoint equalities and covering maps are retained. -/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w z

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p)

/-- Changing equal path endpoints preserves the actual lifted endpoint. -/
theorem monodromy_cast_val {x y x' y' : B} (q : Path.Homotopic.Quotient x y)
    (hx : x' = x) (hy : y' = y) (e : E) (he : p e = x') :
    (hp.monodromy (q.cast hx hy) ⟨e, he⟩).1 =
      (hp.monodromy q ⟨e, he.trans hx⟩).1 := by
  cases hx
  cases hy
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]

/-- A continuous commuting square preserves actual covering monodromy. -/
theorem monodromy_naturality {E' : Type w} {B' : Type z}
    [TopologicalSpace E'] [TopologicalSpace B'] {p' : E' → B'}
    (hp' : IsCoveringMap p') (k : C(E, E')) (f : C(B, B'))
    (h : ∀ e, p' (k e) = f (p e)) {x y : B}
    (q : Path.Homotopic.Quotient x y) (e : {e : E // p e = x}) :
    hp'.monodromy (q.map f) ⟨k e.1, (h e.1).trans (congrArg f e.2)⟩ =
      ⟨k (hp.monodromy q e).1,
        (h _).trans (congrArg f (hp.monodromy q e).2)⟩ := by
  obtain ⟨q⟩ := q
  let F := hp.liftPath q e.1 (q.source.trans e.2.symm)
  have hstart : (q.map f.continuous) 0 = p' (k e.1) := by
    change f (q 0) = p' (k e.1)
    rw [q.source, h]
    exact congrArg f e.2.symm
  have hF : k.comp F = hp'.liftPath (q.map f.continuous) (k e.1) hstart := by
    apply (hp'.eq_liftPath_iff' hstart).mpr
    constructor
    · ext t
      change p' (k (F t)) = f (q t)
      rw [h]
      exact congrArg f (congr_fun (hp.liftPath_lifts q e.1 _) t)
    · change k (F 0) = k e.1
      rw [show F 0 = e.1 from hp.liftPath_zero q e.1 _]
  apply Subtype.ext
  exact (ContinuousMap.congr_fun hF 1).symm

/-- Based monodromy naturality retains the actual projection square at the source. -/
theorem monodromy_naturality_basepoint {E' : Type w} {B' : Type z}
    [TopologicalSpace E'] [TopologicalSpace B'] {p' : E' → B'}
    (hp' : IsCoveringMap p') (k : C(E, E')) (f : C(B, B'))
    (h : ∀ e, p' (k e) = f (p e)) (e₀ : E) {x : B}
    (q : Path.Homotopic.Quotient (p e₀) x) :
    (hp'.monodromy ((q.map f).cast (h e₀) rfl) ⟨k e₀, rfl⟩).1 =
      k (hp.monodromy q ⟨e₀, rfl⟩).1 := by
  rw [monodromy_cast_val]
  exact congrArg Subtype.val (monodromy_naturality hp hp' k f h q ⟨e₀, rfl⟩)

variable [SimplyConnectedSpace E]

/-- Lifted endpoints identify base path classes with the actual covering fiber. -/
def pathClassEquiv (e₀ : E) (x : B) :
    Path.Homotopic.Quotient (p e₀) x ≃ {e : E // p e = x} where
  toFun q := hp.monodromy q ⟨e₀, rfl⟩
  invFun e :=
    ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e₀ e.1)).map
      ⟨p, hp.continuous⟩).cast rfl e.2.symm
  left_inv q := by
    have h : Path.Homotopic.Quotient.mk
        (PathConnectedSpace.somePath e₀ (hp.monodromy q ⟨e₀, rfl⟩).1) =
        hp.liftPathQuotient q ⟨e₀, rfl⟩ := Subsingleton.elim _ _
    dsimp only
    rw [h, hp.map_liftPathQuotient]
    simp only [Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]
  right_inv e := by
    apply hp.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e₀ e.1))
    simp only [Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]

/-- The displayed equivalence uses genuine monodromy, without relabeling the fiber. -/
@[simp]
theorem pathClassEquiv_apply (e₀ : E) (x : B)
    (q : Path.Homotopic.Quotient (p e₀) x) :
    pathClassEquiv hp e₀ x q = hp.monodromy q ⟨e₀, rfl⟩ := rfl

/-- Postcomposition of path classes is exactly transport in the covering fiber. -/
theorem pathClassEquiv_trans (e₀ : E) {x y : B}
    (q : Path.Homotopic.Quotient (p e₀) x) (r : Path.Homotopic.Quotient x y) :
    pathClassEquiv hp e₀ y (q.trans r) =
      hp.monodromy r (pathClassEquiv hp e₀ x q) :=
  hp.monodromy_trans_apply q r ⟨e₀, rfl⟩

/-- In a simply connected covering, the endpoint of the lift detects the path class. -/
theorem monodromy_basepoint_injective (e₀ : E) (x : B) :
    Function.Injective (fun q : Path.Homotopic.Quotient (p e₀) x ↦
      hp.monodromy q ⟨e₀, rfl⟩) :=
  (pathClassEquiv hp e₀ x).injective

end IsCoveringMap
