/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.FiberDetection
public import Colib.Topology.HomotopyFiber.Connected

/-! # Detecting the canonical homotopy-pullback comparison on actual fibers

The fiber of the canonical comparison is related to the original square's
fiber map by an explicit path-prefix/suffix homotopy. This is the missing
map identification needed to apply the genuine long exact sequence.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/CartesianDetection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
open unitInterval
universe u

namespace Topology.HomotopyPullback
variable {X Y B C : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B] [TopologicalSpace C]
  (f : C(X, B)) (g : C(Y, C)) (a : C(X, Y)) (b : C(B, C))
  (sq : g.comp a = b.comp f) (z : B)

/-- The original square map on actual homotopy fibers. -/
def transitionFiber : C(HomotopyFiber f z, HomotopyFiber g (b z)) :=
  HomotopyFiber.map a b sq.symm z

/-- The original canonical comparison, viewed as a map over the unchanged base. -/
def comparisonFiber : C(HomotopyFiber f z,
    HomotopyFiber (baseProjection g b) z) :=
  HomotopyFiber.mapOver f (baseProjection g b) (comparison g b f a sq) rfl z

/-- Slide the intermediate parameter along its original path. The inner
path acquires its prefix while the outer path retains precisely its suffix. -/
def comparisonFiberHomotopy :
    (comparisonFiber f g a b sq z).Homotopy
      ((baseFiberComparison g b z).comp (transitionFiber f g a b sq z)) where
  toFun w :=
    ⟨(⟨(w.2.1.2 w.1, a w.2.1.1,
      ⟨fun t ↦ b (w.2.1.2 (w.1 * t)), by fun_prop⟩),
        by simpa using (congrArg b w.2.2.1).trans (ContinuousMap.congr_fun sq w.2.1.1).symm,
        by simp⟩,
      ⟨fun t ↦ w.2.1.2 (σ (σ w.1 * σ t)), by fun_prop⟩),
        by simp [baseProjection], by simpa using w.2.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply Continuous.prodMk (by fun_prop)
      apply Continuous.prodMk (by fun_prop)
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun w : (I × HomotopyFiber f z) × I ↦
        b (w.1.2.1.2 (w.1.1 * w.2)))
      fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun w : (I × HomotopyFiber f z) × I ↦
        w.1.2.1.2 (σ (σ w.1.1 * σ w.2)))
      fun_prop
  map_zero_left p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact p.2.1
      · refine Prod.ext (by rfl) ?_
        apply ContinuousMap.ext
        intro t
        change b (p.1.2 (0 * t)) = b (f p.1.1)
        simpa using congrArg b p.2.1
    · apply ContinuousMap.ext
      intro t
      change p.1.2 (σ (σ 0 * σ t)) = p.1.2 t
      simp
  map_one_left p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact p.2.2
      · refine Prod.ext (by rfl) ?_
        apply ContinuousMap.ext
        intro t
        change b (p.1.2 (1 * t)) = b (p.1.2 t)
        simp
    · apply ContinuousMap.ext
      intro t
      change p.1.2 (σ (σ 1 * σ t)) = z
      simpa using p.2.2

/-- The preceding homotopy is genuinely fixed on every constant-path
source point. Its target is the original canonical comparison fiber point. -/
theorem comparisonFiberHomotopy_fixed (x : X) (hx : f x = z) (t : I) :
    comparisonFiberHomotopy f g a b sq z (t, HomotopyFiber.basepoint f z x hx) =
      comparisonFiber f g a b sq z (HomotopyFiber.basepoint f z x hx) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · exact hx.symm
    · change (a x, (ContinuousMap.const I (b z))) =
        (a x, (ContinuousMap.const I (b (f x))))
      refine Prod.ext (by rfl) ?_
      apply ContinuousMap.ext
      intro s
      exact congrArg b hx.symm
  · rfl

/-- The square's original fiber transition controls the actual fiber map of
its canonical homotopy-pullback comparison, in every finite degree. -/
theorem comparisonFiber_bijective (x : X) (hx : f x = z) (n : ℕ)
    (h : Function.Bijective (HomotopyGroup.map (N := Fin n)
      (transitionFiber f g a b sq z) (x := HomotopyFiber.basepoint f z x hx) rfl)) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (comparisonFiber f g a b sq z) (x := HomotopyFiber.basepoint f z x hx) rfl) := by
  let p := HomotopyFiber.basepoint f z x hx
  let H := comparisonFiberHomotopy f g a b sq z
  have hp : baseFiberComparison g b z (transitionFiber f g a b sq z p) =
      comparisonFiber f g a b sq z p :=
    (H.map_one_left p).symm.trans (comparisonFiberHomotopy_fixed f g a b sq z x hx 1)
  have hc := homotopyGroupMap_bijective_comp (transitionFiber f g a b sq z)
    (baseFiberComparison g b z) rfl hp n h
    (homotopyGroupMap_bijective_of_homotopyEquiv (baseFiberHomotopyEquiv g b z) hp n)
  exact homotopyGroupMap_bijective_of_based_homotopy
    (f := (baseFiberComparison g b z).comp (transitionFiber f g a b sq z))
    (g := comparisonFiber f g a b sq z) (x := p) hp rfl H.symm
    (fun t ↦ comparisonFiberHomotopy_fixed f g a b sq z x hx (σ t)) n hc

private theorem bijective_target_congr {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]
    (f : C(S, T)) (s : S) (t : T) (ht : f s = t) (n : ℕ)
    (h : Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := s) rfl)) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := s) ht) := by
  subst t
  exact h

/-- A square over connected original rows is weakly homotopy cartesian when
its prescribed actual fiber transition is bijective at the supplied point.
This is a local square theorem, not the global realization fiber theorem. -/
theorem comparison_bijective_of_fiberMap
    [PathConnectedSpace X] [PathConnectedSpace B]
    [PathConnectedSpace (HomotopyFiber g (b z))]
    (x : X) (hx : f x = z)
    (h : ∀ n : ℕ, Function.Bijective (HomotopyGroup.map (N := Fin n)
      (transitionFiber f g a b sq z) (x := HomotopyFiber.basepoint f z x hx) rfl))
    (x' : X) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (comparison g b f a sq) (x := x') rfl) := by
  let : PathConnectedSpace (HomotopyPullback g b) := pathConnectedSpace g b z
  apply HomotopyFiber.homotopyGroupMap_bijective_at_all_points_of_fiberMap
    f (baseProjection g b) (comparison g b f a sq) rfl x z hx _ x' n
  intro k
  exact bijective_target_congr (comparisonFiber f g a b sq z)
    (HomotopyFiber.basepoint f z x hx) _
    (HomotopyFiber.mapOver_basepoint f (baseProjection g b) (comparison g b f a sq) rfl x z hx)
    k (comparisonFiber_bijective f g a b sq z x hx k (h k))

end Topology.HomotopyPullback
