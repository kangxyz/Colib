/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.ContractibleSource

/-! # Contractible-source loop comparison with a specified endpoint path -/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/ContractibleSourcePath.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies. -/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (x : X) (y : Y) (γ : Path (f x) y)

/-- Correct the constant point map by the displayed path, in its actual direction. -/
def pointSourcePathHomotopy [ContractibleSpace X] :
    (ContinuousMap.const Unit y).Homotopy (f.comp (sourcePointEquiv x).toFun) :=
  γ.symm.toHomotopyConst

/-- An explicit endpoint path identifies loops with the fiber of a map whose source
is contractible. The forward map retains the specified source point. -/
def loopEquivOfContractibleSourcePath [ContractibleSpace X] :
    ContinuousMap.HomotopyEquiv (Path y y) (HomotopyFiber f y) :=
  (pointSourceFiberHomeomorph (ContinuousMap.const Unit y) y () rfl).symm.toHomotopyEquiv.trans
    (sourceEquivOfHomotopy f (ContinuousMap.const Unit y) (sourcePointEquiv x)
      (pointSourcePathHomotopy f x y γ) y)

@[simp]
theorem loopEquivOfContractibleSourcePath_source [ContractibleSpace X] (δ : Path y y) :
    ((loopEquivOfContractibleSourcePath f x y γ) δ).1.1 = x := rfl

/-- The path correction is exactly the specified path followed by the original loop. -/
@[simp]
theorem loopEquivOfContractibleSourcePath_path [ContractibleSpace X] (δ : Path y y) :
    ((loopEquivOfContractibleSourcePath f x y γ) δ).1.2 =
      (γ.trans δ).toContinuousMap := by
  change (((γ.symm.toHomotopyConst).evalAt ()).symm.trans δ).toContinuousMap = _
  rw [show γ.symm.toHomotopyConst.evalAt () = γ.symm from rfl]
  exact congrArg (fun p : Path (f x) y ↦ (p.trans δ).toContinuousMap)
    (Path.symm_symm γ)

/-- The displayed source point equipped with precisely the specified path. -/
def pointWithPath : HomotopyFiber f y :=
  ⟨(x, γ.toContinuousMap), γ.source, γ.target⟩

/-- Remove the constant suffix introduced by the loop unit, keeping the source fixed. -/
def loopEquivOfContractibleSourcePathUnitPath [ContractibleSpace X] :
    Path (loopEquivOfContractibleSourcePath f x y γ (Path.refl y))
      (pointWithPath f x y γ) where
  toFun t := ⟨(x, (Path.delayReflRight t γ).toContinuousMap),
    (Path.delayReflRight t γ).source, (Path.delayReflRight t γ).target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_const
    exact continuous_induced_dom.comp
      (Path.continuous_delayReflRight.comp (continuous_id.prodMk continuous_const))
  source' := by
    apply Subtype.ext
    refine _root_.Prod.ext ?_ ?_
    · exact (loopEquivOfContractibleSourcePath_source f x y γ _).symm
    · change (Path.delayReflRight 0 γ).toContinuousMap = _
      rw [Path.delayReflRight_zero, loopEquivOfContractibleSourcePath_path]
  target' := by
    apply Subtype.ext
    change (x, (Path.delayReflRight 1 γ).toContinuousMap) = (x, γ.toContinuousMap)
    exact congrArg (fun p : Path (f x) y ↦ (x, p.toContinuousMap))
      (Path.delayReflRight_one γ)

/-- The chosen inverse is based by the actual unit-removal track and its own
left-inverse homotopy, without silently assuming a fixed-point contraction. -/
def loopEquivOfContractibleSourcePathInverseBasepointPath [ContractibleSpace X] :
    Path ((loopEquivOfContractibleSourcePath f x y γ).invFun (pointWithPath f x y γ))
      (Path.refl y) :=
  ((loopEquivOfContractibleSourcePathUnitPath f x y γ).symm.map
    (loopEquivOfContractibleSourcePath f x y γ).invFun.continuous).trans
      ((Classical.choice (loopEquivOfContractibleSourcePath f x y γ).left_inv).evalAt
        (Path.refl y))

end Topology.HomotopyFiber
