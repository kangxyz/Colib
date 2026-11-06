/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.AllWeak.NullhomotopyNaturality
public import Colib.Topology.HomotopyFiber.ContractibleBase
public import Colib.Topology.HomotopyPullback.CartesianTransport
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence

/-! # The original canonical comparison through the all-weak fiber

The actual all-weak contraction supplies a literal lift to the fiber of the
original change-of-weak map. It is a genuine homotopy equivalence because its
projection is identity and the actual target is contracted. The original
acyclic-inclusion square induces a map of these actual fibers, whose composite
with that lift is exactly the canonical acyclic comparison, including its path.
No homotopy-cartesian square or fibration theorem is assumed here.


Implementation provenance:
`Quillen/Waldhausen/Fibration/AllWeak/CanonicalFiberFactorization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.AllWeak
section Lift
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The original contraction evaluated on the original change-of-weak map. -/
def changeWeakNullhomotopy :
    (changeWeakMap (nested W)).Homotopy
      (ContinuousMap.const _ (waldhausenStructure W).kBasepoint) :=
  (contraction W).compContinuousMap (changeWeakMap (nested W))

/-- The source is unchanged and the entire original contraction is its fiber path. -/
def changeWeakFiberLift : C(W.Delooping,
    HomotopyFiber (changeWeakMap (nested W)) (waldhausenStructure W).kBasepoint) :=
  HomotopyFiber.lift (changeWeakMap (nested W)) (waldhausenStructure W).kBasepoint
    (ContinuousMap.id _) (changeWeakNullhomotopy W)

@[simp] theorem changeWeakFiberLift_source (x : W.Delooping) :
    (changeWeakFiberLift W x).1.1 = x := rfl

@[simp] theorem changeWeakFiberLift_path (x : W.Delooping) (t : unitInterval) :
    (changeWeakFiberLift W x).1.2 t = contraction W (t, changeWeakMap (nested W) x) := rfl

/-- The actual projection is a strict left inverse of the prescribed lift. -/
@[simp] theorem changeWeakFiberLift_projection :
    (HomotopyFiber.projection (changeWeakMap (nested W))
      (waldhausenStructure W).kBasepoint).comp (changeWeakFiberLift W) = ContinuousMap.id _ := rfl

/-- Contracted-base projection and its strict section give the genuine equivalence. -/
def changeWeakFiberLiftEquiv : ContinuousMap.HomotopyEquiv W.Delooping
    (HomotopyFiber (changeWeakMap (nested W)) (waldhausenStructure W).kBasepoint) :=
  Topology.homotopyEquivCancelRight
    (a := changeWeakFiberLift W)
    (HomotopyFiber.projectionEquivOfContraction (changeWeakMap (nested W))
      (waldhausenStructure W).kBasepoint (contraction W)) rfl
    (ContinuousMap.HomotopyEquiv.refl W.Delooping) rfl

@[simp] theorem changeWeakFiberLiftEquiv_toFun :
    (changeWeakFiberLiftEquiv W).toFun = changeWeakFiberLift W := rfl

/-- The inverse is the original projection on the original source coordinate. -/
@[simp] theorem changeWeakFiberLiftEquiv_invFun :
    (changeWeakFiberLiftEquiv W).invFun =
      HomotopyFiber.projection (changeWeakMap (nested W)) (waldhausenStructure W).kBasepoint := by
  ext z
  rfl

/-- The contraction fixes the actual zero, so the fiber point has constant path. -/
@[simp] theorem changeWeakFiberLift_basepoint :
    changeWeakFiberLift W W.kBasepoint =
      HomotopyFiber.basepoint (changeWeakMap (nested W)) (waldhausenStructure W).kBasepoint
        W.kBasepoint (changeWeakMap_basepoint (nested W)) := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · rfl
  · apply ContinuousMap.ext
    intro t
    change contraction W (t, changeWeakMap (nested W) W.kBasepoint) = _
    rw [changeWeakMap_basepoint]
    change contraction W (t, (waldhausenStructure W).kBasepoint) =
      (waldhausenStructure W).kBasepoint
    exact contraction_fixed_zero W t

/-- Every finite based homotopy degree, including zero, retains the literal lift. -/
theorem changeWeakFiberLift_bijective (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (changeWeakFiberLift W)
      (x := W.kBasepoint) (changeWeakFiberLift_basepoint W)) := by
  exact homotopyGroupMap_bijective_of_homotopyEquiv (changeWeakFiberLiftEquiv W)
    (changeWeakFiberLift_basepoint W) n
end Lift

section AcyclicSquare
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- The original coarse inclusion preserves the actual all-weak acyclic zero. -/
theorem acyclicCoarseInclusion_basepoint :
    deloopingMap (AllWeak.acyclicInclusion_exact N)
      (waldhausenStructure (acyclicStructure N)).kBasepoint = N.coarse.kBasepoint :=
  deloopingMap_basepoint_of_zeroEq (AllWeak.acyclicInclusion_exact N) N.zero_eq.symm

/-- The map of actual homotopy fibers induced by the original inclusion square.
Both original source and complete postcomposed path are retained, with the
proved equality of the actual chosen target point. -/
def acyclicFiberSquareMap : C(
    HomotopyFiber (changeWeakMap (nested (acyclicStructure N)))
      (waldhausenStructure (acyclicStructure N)).kBasepoint,
    HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) where
  toFun z := ⟨(acyclicInclusionMap N z.1.1,
    (deloopingMap (AllWeak.acyclicInclusion_exact N)).hom.comp z.1.2),
    (congrArg (deloopingMap (AllWeak.acyclicInclusion_exact N)) z.2.1).trans
      (ContinuousMap.congr_fun (changeWeak_acyclicInclusion_realized N) z.1.1),
    (congrArg (deloopingMap (AllWeak.acyclicInclusion_exact N)) z.2.2).trans
      (acyclicCoarseInclusion_basepoint N)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact (ContinuousMap.continuous_postcomp
        (deloopingMap (AllWeak.acyclicInclusion_exact N)).hom).comp (by fun_prop)

@[simp] theorem acyclicFiberSquareMap_source
    (z : HomotopyFiber (changeWeakMap (nested (acyclicStructure N)))
      (waldhausenStructure (acyclicStructure N)).kBasepoint) :
    (acyclicFiberSquareMap N z).1.1 = acyclicInclusionMap N z.1.1 := rfl

@[simp] theorem acyclicFiberSquareMap_path
    (z : HomotopyFiber (changeWeakMap (nested (acyclicStructure N)))
      (waldhausenStructure (acyclicStructure N)).kBasepoint) (t : unitInterval) :
    (acyclicFiberSquareMap N z).1.2 t =
      deloopingMap (AllWeak.acyclicInclusion_exact N) (z.1.2 t) := rfl

/-- The induced map preserves the original constant-path point. -/
@[simp] theorem acyclicFiberSquareMap_basepoint :
    acyclicFiberSquareMap N
      (HomotopyFiber.basepoint (changeWeakMap (nested (acyclicStructure N)))
        (waldhausenStructure (acyclicStructure N)).kBasepoint (acyclicStructure N).kBasepoint
        (changeWeakMap_basepoint (nested (acyclicStructure N)))) =
      HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
        (changeWeakMap_basepoint N) := by
  apply Subtype.ext
  apply Prod.ext
  · exact acyclicInclusionMap_basepoint N
  · apply ContinuousMap.ext
    intro t
    exact acyclicCoarseInclusion_basepoint N

/-- The prescribed canonical comparison is exactly this original fiber-square
map after the genuine contraction lift, including every point of its path. -/
theorem acyclicFiberSquareMap_changeWeakFiberLift :
    (acyclicFiberSquareMap N).comp (changeWeakFiberLift (acyclicStructure N)) =
      canonicalFiberMap N := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · rfl
  · apply ContinuousMap.ext
    intro t
    exact contraction_acyclicNullhomotopy N t x

end AcyclicSquare
end CategoryTheory.Waldhausen.Fibration.AllWeak
