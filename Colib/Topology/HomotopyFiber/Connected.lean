/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Fibration

/-! # Actual path connectedness for fibrations and homotopy pullbacks

Only pointwise paths are chosen. Covering-homotopy lifting turns each base
path into an actual path from a total-space point to the chosen fiber.
No continuous choice of paths or fiber inverses is assumed.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/Connected.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u

namespace Topology
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]

/-- A genuine fibration over a path-connected base is path connected if one
actual strict fiber is path connected. -/
theorem pathConnectedSpace_of_fibration (p : C(E, B))
    (hp : HomotopyLiftingProperty p) (b : B)
    [PathConnectedSpace B] [PathConnectedSpace {e : E // p e = b}] :
    PathConnectedSpace E := by
  let c : {e : E // p e = b} := Classical.choice inferInstance
  have hj (e : E) : Joined e c.1 := by
    let γ := (PathConnectedSpace.joined (p e) b).somePath
    let a : C(ULift.{u} Unit, E) := ContinuousMap.const _ e
    let H : C(unitInterval × ULift.{u} Unit, B) := ⟨fun z ↦ γ z.1, by fun_prop⟩
    obtain ⟨L, hL₀, hL⟩ := hp _ a H (fun _ ↦ γ.source)
    let d : {e : E // p e = b} := ⟨L (1, ⟨()⟩), (hL 1 ⟨()⟩).trans γ.target⟩
    have h₁ : Joined e d.1 := ⟨{
      toFun t := L (t, ⟨()⟩)
      continuous_toFun := by fun_prop
      source' := hL₀ ⟨()⟩
      target' := rfl }⟩
    exact h₁.trans ((PathConnectedSpace.joined d c).map continuous_subtype_val)
  exact ⟨⟨c.1⟩, fun e e' ↦ (hj e).trans (hj e').symm⟩

namespace HomotopyPullback
variable {X A Y : Type u} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace Y]
  (f : C(X, Y)) (g : C(A, Y))

/-- A homotopy pullback over a connected parameter space is connected when
its actual fiber over one supplied parameter is connected. -/
theorem pathConnectedSpace (a : A) [PathConnectedSpace A]
    [PathConnectedSpace (HomotopyFiber f (g a))] :
    PathConnectedSpace (HomotopyPullback f g) := by
  let : PathConnectedSpace {z : HomotopyPullback f g // baseProjection f g z = a} :=
    (strictBaseFiberHomeomorph f g a).symm.pathConnectedSpace
  exact pathConnectedSpace_of_fibration (baseProjection f g)
    (baseProjection_homotopyLiftingProperty f g) a

end HomotopyPullback
end Topology
