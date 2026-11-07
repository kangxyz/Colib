/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.WeakPullback
public import Colib.Topology.HomotopyFiber.ProjectionFibration
public import Colib.Topology.HomotopyFiber.GroupDetection

/-! # Weak source equivalence for the original homotopy-fiber map

The original source-change map retains the given path. It is the strict
pullback of the weak source map along the genuine fiber projection fibration.
Actual strict/homotopy pullback comparison and weakly contractible fibers
prove its full weak equivalence, including π₀ and empty-space cases.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/WeakSourceEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Topology
namespace HomotopyPullback
variable {E A B : Type u} [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]

/-- The original second projection of the actual strict pullback. -/
def strictSourceProjection (f : C(E, B)) (g : C(A, B)) :
    C({z : A × E // f z.2 = g z.1}, E) where
  toFun z := z.1.2
  continuous_toFun := by fun_prop

/-- Pullback of an actual weak equivalence along a genuine fibration is weak,
with the original strict projection as its forward map. -/
theorem strictSourceProjection_isWeakHomotopyEquivalence
    (f : C(E, B)) (g : C(A, B)) (hf : HomotopyLiftingProperty f)
    (hg : IsWeakHomotopyEquivalence g) :
    IsWeakHomotopyEquivalence (strictSourceProjection f g) :=
  ((baseProjection_isWeakHomotopyEquivalence g f hg).comp
    (isWeakHomotopyEquivalence_of_homotopyEquiv (symmetryHomeomorph f g).toHomotopyEquiv)).comp
      (isWeakHomotopyEquivalence_of_homotopyEquiv (strictPullbackHomotopyEquivOfLifting f g hf))

end HomotopyPullback
namespace HomotopyFiber
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (f : C(X, B)) (g : C(Y, B)) (u : C(X, Y)) (sq : g.comp u = f) (b : B)

/-- The original source fiber is exactly the strict pullback of the original
source map along the genuine target-fiber projection. -/
def sourcePullbackHomeomorph : HomotopyFiber f b ≃ₜ
    {z : X × HomotopyFiber g b // projection g b z.2 = u z.1} where
  toFun z := ⟨(z.1.1, mapOver f g u sq b z), rfl⟩
  invFun z := ⟨(z.1.1, z.1.2.1.2),
    z.1.2.2.1.trans ((congrArg g z.2).trans (ContinuousMap.congr_fun sq z.1.1)),
    z.1.2.2.2⟩
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · exact z.2.symm
      · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The original path-retaining map on actual homotopy fibers is a full weak
homotopy equivalence whenever the original source map is one. -/
theorem mapOver_isWeakHomotopyEquivalence (hu : IsWeakHomotopyEquivalence u) :
    IsWeakHomotopyEquivalence (mapOver f g u sq b) :=
  (HomotopyPullback.strictSourceProjection_isWeakHomotopyEquivalence
    (projection g b) u (projection_homotopyLiftingProperty g b) hu).comp
      (isWeakHomotopyEquivalence_of_homotopyEquiv
        (sourcePullbackHomeomorph f g u sq b).toHomotopyEquiv)

/-- All original finite homotopy-set maps, including dimension zero, are
bijective at every actual source-fiber point. -/
theorem homotopyGroupMap_mapOver_bijective (hu : IsWeakHomotopyEquivalence u)
    (z : HomotopyFiber f b) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (mapOver f g u sq b) (x := z) rfl) :=
  (mapOver_isWeakHomotopyEquivalence f g u sq b hu).homotopy_bijective z n

end HomotopyFiber
end Topology
