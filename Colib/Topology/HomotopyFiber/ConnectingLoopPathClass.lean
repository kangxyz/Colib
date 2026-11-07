/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LoopComponentTransport
public import Colib.Topology.HomotopyFiber.ConnectingLoopTranspose

/-! # Original double-loop representatives of the connecting map

The coordinate interchange is literal. Its proved inversion sign is retained
when the original fiber loop is compared with an actual path representative.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/ConnectingLoopPathClass.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology HomotopyGroup
open scoped Topology
universe u
namespace Topology.HomotopyFiber.LoopComponentTransport
variable {X : Type u} [TopologicalSpace X]

/-- Curry an actual endpoint-fixed homotopy into its original path-space path. -/
def pathOfPathHomotopy {x y : X} {p q : Path x y} (H : p.Homotopy q) : Path p q where
  toFun := H.eval
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact H.continuous
  source' := H.eval_zero
  target' := H.eval_one

/-- Uncurry an actual path in the endpoint-fixed path space. -/
def pathHomotopyOfPath {x y : X} {p q : Path x y} (H : Path p q) : p.Homotopy q where
  toFun := fun a : unitInterval × unitInterval ↦ H a.1 a.2
  continuous_toFun := by
    exact Path.continuous_uncurry_iff.mpr H.continuous
  map_zero_left t := by change H 0 t = p t; rw [H.source]
  map_one_left t := by change H 1 t = q t; rw [H.target]
  prop' := fun (s t : unitInterval) (ht : t ∈ ({0, 1} : Set unitInterval)) ↦ by
    change H s t = p t
    rcases ht with ht | ht
    · subst t
      exact (H s).source.trans p.source.symm
    · have ht' : t = 1 := Set.mem_singleton_iff.mp ht
      subst t
      exact (H s).target.trans p.target.symm

/-- A genuine homotopy equivalence reflects actual connected components. -/
theorem joined_of_equiv {Y : Type u} [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) {z w : X} (p : Joined (e z) (e w)) :
    Joined z w := by
  obtain ⟨H⟩ := e.left_inv
  obtain ⟨q⟩ := p
  exact ⟨(H.evalAt z).symm.trans ((q.map e.invFun.continuous).trans (H.evalAt w))⟩

/-- The two original loop parameters are interchanged, with all boundary values retained. -/
def doubleLoopTranspose (x : X) :
    C(Path (Path.refl x) (Path.refl x), Path (Path.refl x) (Path.refl x)) where
  toFun β := {
    toFun s := {
      toFun t := β t s
      continuous_toFun := by fun_prop
      source' := by rw [β.source]; rfl
      target' := by rw [β.target]; rfl }
    continuous_toFun := by
      apply Path.continuous_uncurry_iff.mp
      change Continuous (fun a : unitInterval × unitInterval ↦ β a.2 a.1)
      fun_prop
    source' := by ext t; exact (β t).source
    target' := by ext t; exact (β t).target }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun a : ((Path (Path.refl x) (Path.refl x) × unitInterval) ×
      unitInterval) ↦ a.1.1 a.2 a.1.2)
    fun_prop

/-- The original transpose preserves the specified constant double loop. -/
theorem doubleLoopTranspose_refl (x : X) :
    doubleLoopTranspose x (Path.refl (Path.refl x)) = Path.refl (Path.refl x) := by
  ext s t
  rfl

/-- The original connecting map has the proved negative transpose sign on each displayed loop. -/
theorem connectingHom_loop_path {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (β : Path (Path.refl y) (Path.refl y)) :
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (⟦HomotopyFiber.loopConnectingMap f h β⟧ :
          FundamentalGroup _ (HomotopyFiber.basepoint f y x h)) =
      HomotopyFiber.connectingHom f y x h 0
        (((loopShiftMulEquiv 0).symm
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm ⟦β⟧))⁻¹) := by
  exact HomotopyFiber.connectingHom_loopConnectingMap_sign f h
    (doubleLoopTranspose y) (doubleLoopTranspose_refl y) (fun _ _ _ ↦ rfl)
    (zeroPointClass (Path.refl (Path.refl y)) β)

end Topology.HomotopyFiber.LoopComponentTransport
