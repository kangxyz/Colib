/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.CartesianTransport
public import Colib.Topology.HomotopyFiber.WeakSquareTransport

/-! Exact maps of homotopy fibers with a specified target-basepoint equality.
The original source coordinate and full postcomposed path are retained.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/BasedSquareMap.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open scoped Topology
universe u v w z
namespace Topology.HomotopyFiber
section Maps
variable {X : Type u} {Y : Type v} {A : Type w} {B : Type z}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B] {p : C(X, A)} {q : C(Y, B)}

/-- The exact fiber map with a displayed equality of target basepoints. -/
def mapAt (u : C(X, Y)) (v : C(A, B)) (sq : v.comp p = q.comp u)
    (a : A) (b : B) (hb : v a = b) : C(HomotopyFiber p a, HomotopyFiber q b) where
  toFun z := ⟨(u z.1.1, v.comp z.1.2),
    (congrArg v z.2.1).trans (ContinuousMap.congr_fun sq z.1.1),
    (congrArg v z.2.2).trans hb⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact (ContinuousMap.continuous_postcomp v).comp (by fun_prop)

end Maps

variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B] {p : C(X, A)} {q : C(Y, B)}

theorem mapAt_weak (u : C(X, Y)) (v : C(A, B)) (sq : v.comp p = q.comp u)
    (hu : IsWeakHomotopyEquivalence u) (hv : IsWeakHomotopyEquivalence v)
    (a : A) (b : B) (hb : v a = b) : IsWeakHomotopyEquivalence (mapAt u v sq a b hb) := by
  subst b
  exact map_isWeakHomotopyEquivalence u v sq hu hv a

/-- Weak cartesianness gives the identical map with prescribed target point. -/
theorem mapAt_weak_of_comparison (u : C(X, Y)) (v : C(A, B)) (sq : v.comp p = q.comp u)
    (h : IsWeakHomotopyEquivalence (HomotopyPullback.comparison q v p u sq.symm))
    (a : A) (b : B) (hb : v a = b) : IsWeakHomotopyEquivalence (mapAt u v sq a b hb) := by
  subst b
  exact map_isWeakHomotopyEquivalence_of_comparison u v sq h a
end Topology.HomotopyFiber
