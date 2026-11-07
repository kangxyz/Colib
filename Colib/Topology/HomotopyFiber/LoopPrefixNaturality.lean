/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.ContractibleSourcePath
public import Colib.Topology.HomotopyFiber.Loop

/-!
Implementation provenance:
`Quillen/Topology/HomotopyFiber/LoopPrefixNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Contraction-independent forward loop comparison -/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v u' v'
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- Prefix a loop by the displayed fiber path, with no choice of contraction. -/
def loopPrefix (f : C(X, Y)) (x : X) (y : Y) (γ : Path (f x) y) :
    C(Path y y, HomotopyFiber f y) where
  toFun δ := ⟨(x, (γ.trans δ).toContinuousMap), (γ.trans δ).source, (γ.trans δ).target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_const
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Path.trans_continuous_family (fun _ : Path y y ↦ γ) (by fun_prop)
      (fun δ : Path y y ↦ δ) (by fun_prop)

/-- The existing contractible-source equivalence has exactly this forward map. -/
theorem loopPrefix_eq_forward [ContractibleSpace X]
    (f : C(X, Y)) (x : X) (y : Y) (γ : Path (f x) y) :
    loopPrefix f x y γ = (loopEquivOfContractibleSourcePath f x y γ).toFun := by
  apply ContinuousMap.ext
  intro δ
  apply Subtype.ext
  exact Prod.ext rfl (loopEquivOfContractibleSourcePath_path f x y γ δ).symm

/-- Strict squares preserve the entire displayed prefix followed by the original loop. -/
theorem loopPrefix_map_square {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (sq : v.comp f = f'.comp u)
    (x : X) (y : Y) (γ : Path (f x) y) :
    (map u v sq y).comp (loopPrefix f x y γ) =
      (loopPrefix f' (u x) (v y)
        ((γ.map v.continuous).cast (ContinuousMap.congr_fun sq x).symm rfl)).comp
          (basedLoopMap v rfl) := by
  apply ContinuousMap.ext
  intro δ
  apply Subtype.ext
  apply Prod.ext
  · rfl
  apply ContinuousMap.ext
  intro t
  change ((γ.trans δ).map v.continuous) t = _
  rw [Path.map_trans]
  rfl

/-- The unit-removal track is defined without a contraction of the total space. -/
def loopPrefixUnitPath (f : C(X, Y)) (x : X) (y : Y) (γ : Path (f x) y) :
    Path (loopPrefix f x y γ (Path.refl y)) (pointWithPath f x y γ) where
  toFun t := ⟨(x, (Path.delayReflRight t γ).toContinuousMap),
    (Path.delayReflRight t γ).source, (Path.delayReflRight t γ).target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_const
    exact continuous_induced_dom.comp
      (Path.continuous_delayReflRight.comp (continuous_id.prodMk continuous_const))
  source' := by
    apply Subtype.ext
    change (x, (Path.delayReflRight 0 γ).toContinuousMap) = (x, (γ.trans _).toContinuousMap)
    rw [Path.delayReflRight_zero]
  target' := by
    apply Subtype.ext
    change (x, (Path.delayReflRight 1 γ).toContinuousMap) = (x, γ.toContinuousMap)
    rw [Path.delayReflRight_one]

/-- The complete track agrees with the existing specified equivalence track. -/
theorem loopPrefixUnitPath_apply [ContractibleSpace X]
    (f : C(X, Y)) (x : X) (y : Y) (γ : Path (f x) y) (t : unitInterval) :
    loopPrefixUnitPath f x y γ t =
      loopEquivOfContractibleSourcePathUnitPath f x y γ t := rfl

/-- A strict square preserves the complete unit-removal track pointwise. -/
theorem loopPrefixUnitPath_map_square {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (sq : v.comp f = f'.comp u)
    (x : X) (y : Y) (γ : Path (f x) y) (t : unitInterval) :
    map u v sq y (loopPrefixUnitPath f x y γ t) =
      loopPrefixUnitPath f' (u x) (v y)
        ((γ.map v.continuous).cast (ContinuousMap.congr_fun sq x).symm rfl) t := by
  apply Subtype.ext
  rfl

end Topology.HomotopyFiber
