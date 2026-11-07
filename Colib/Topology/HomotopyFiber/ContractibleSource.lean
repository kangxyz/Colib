/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.SourceEquivalence
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence

/-! # The original loop inclusion for a contractible source

The homotopy fiber of the actual map from a point is explicitly homeomorphic
to the existing path space `Path y y`. The accepted canonical change-of-source
equivalence then makes the original loop inclusion an equivalence when the
source is contractible. Every path and the displayed source point are retained.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/ContractibleSource.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A contractible space contracts to any displayed point. No fixed-track
property is inferred for this chosen contraction. -/
def contractibleSourceContraction [ContractibleSpace X] (x : X) :
    (ContinuousMap.id X).Homotopy (ContinuousMap.const X x) := by
  let H := Classical.choice (id_nullhomotopic X).choose_spec
  exact H.trans (H.evalAt x).symm.toHomotopyConst

/-- The actual inclusion of the displayed point is an equivalence. -/
def sourcePointEquiv [ContractibleSpace X] (x : X) :
    ContinuousMap.HomotopyEquiv Unit X where
  toFun := ContinuousMap.const Unit x
  invFun := ContinuousMap.const X ()
  left_inv := by
    have h : (ContinuousMap.const Unit ()) = ContinuousMap.id Unit := by ext a
    change (ContinuousMap.const Unit ()).Homotopic (ContinuousMap.id Unit)
    rw [h]
  right_inv := ⟨(contractibleSourceContraction x).symm⟩

@[simp] theorem sourcePointEquiv_toFun [ContractibleSpace X] (x : X) :
    (sourcePointEquiv x).toFun = ContinuousMap.const Unit x := rfl

variable (f : C(X, Y)) (y : Y) (x : X) (h : f x = y)

/-- The actual point-source fiber is the original loop path space, with unchanged paths. -/
def pointSourceFiberHomeomorph :
    HomotopyFiber (f.comp (ContinuousMap.const Unit x)) y ≃ₜ Path y y where
  toFun z := { toContinuousMap := z.1.2, source' := z.2.1.trans h, target' := z.2.2 }
  invFun γ := ⟨((), γ.toContinuousMap), γ.source.trans h.symm, γ.target⟩
  left_inv z := by
    apply Subtype.ext
    exact _root_.Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : HomotopyFiber (f.comp (ContinuousMap.const Unit x)) y ×
      unitInterval ↦ z.1.1.2 z.2)
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk continuous_induced_dom

@[simp] theorem pointSourceFiberHomeomorph_apply
    (z : HomotopyFiber (f.comp (ContinuousMap.const Unit x)) y) (t : unitInterval) :
    pointSourceFiberHomeomorph f y x h z t = z.1.2 t := rfl

@[simp] theorem pointSourceFiberHomeomorph_symm_path (γ : Path y y) :
    ((pointSourceFiberHomeomorph f y x h).symm γ).1.2 = γ.toContinuousMap := rfl

/-- A contractible source makes the literal original loop inclusion an equivalence. -/
def loopInclusionEquivOfContractibleSource [ContractibleSpace X] :
    ContinuousMap.HomotopyEquiv (Path y y) (HomotopyFiber f y) :=
  (pointSourceFiberHomeomorph f y x h).symm.toHomotopyEquiv.trans
    (sourceEquiv f (sourcePointEquiv x) y)

/-- The forward map has precisely the original fixed source point and original path. -/
@[simp] theorem loopInclusionEquivOfContractibleSource_toFun [ContractibleSpace X] :
    (loopInclusionEquivOfContractibleSource f y x h).toFun = loopInclusion f y x h := by
  ext γ
  rfl

@[simp] theorem loopInclusionEquivOfContractibleSource_source [ContractibleSpace X]
    (γ : Path y y) :
    ((loopInclusionEquivOfContractibleSource f y x h) γ).1.1 = x := rfl

@[simp] theorem loopInclusionEquivOfContractibleSource_path [ContractibleSpace X]
    (γ : Path y y) :
    ((loopInclusionEquivOfContractibleSource f y x h) γ).1.2 = γ.toContinuousMap := rfl

/-- Its basepoint is the original constant-path fiber point. -/
@[simp] theorem loopInclusionEquivOfContractibleSource_basepoint [ContractibleSpace X] :
    loopInclusionEquivOfContractibleSource f y x h (Path.refl y) = basepoint f y x h := rfl

/-- The original based loop inclusion is bijective in every finite homotopy
dimension, including dimension zero. -/
theorem loopInclusion_bijective_of_contractibleSource [ContractibleSpace X] (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (loopInclusion f y x h)
      (x := Path.refl y) (y := basepoint f y x h) rfl) := by
  have he := homotopyGroupMap_bijective_of_homotopyEquiv
    (loopInclusionEquivOfContractibleSource f y x h)
    (loopInclusionEquivOfContractibleSource_basepoint f y x h) n
  exact homotopyGroupMap_bijective_congr
    (loopInclusionEquivOfContractibleSource_toFun f y x h) _ rfl he

end Topology.HomotopyFiber
