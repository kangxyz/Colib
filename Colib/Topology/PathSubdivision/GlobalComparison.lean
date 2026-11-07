/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.PathSubdivision.FiniteIteration

/-!
# The original strict comparison from genuine local path-pool inputs

A compact cube family determines one finite time mesh. The actual two-chart
pool comparison advances its source point along that mesh. Parameters may
move during the weak HELP homotopies; every remaining tail is evaluated at
the current parameter. The full outer boundary remains literally fixed.
The final map lands in the original strict pullback, so strict finite HELP
proves the complete weak property of its original constant-path inclusion.


Implementation provenance:
`Quillen/Topology/PathSubdivision/GlobalComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.CubicalSubdivision
open Topology.CubicalTests
open Topology.HomotopyPullback


noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology.PathSubdivision
open CubicalTests CubicalSubdivision HomotopyPullback
variable {E X B : Type u} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace B]

/-- Genuine weakness of the displayed two-chart path-pool comparison for
every parameter family. The parameter loci need not be compact. -/
def TwoChartPoolComparison (p : C(E, B)) (U V : Set B) : Prop :=
  ∀ (D : Type u) [TopologicalSpace D] (γ : C(D,C(unitInterval,B)))
    (hcover : ∀ d,γ d ∈ pathSet U ∨ γ d ∈ pathSet V),
      IsWeakHomotopyEquivalence (twoPoolComparison p γ U V hcover)

/-- The first, second and overlap original chart comparisons provide the
actual two-chart pool premise by ordinary weak locality. -/
theorem twoChartPoolComparison_of_local (p : C(E, B))
    (U V : Set B) (hU : IsOpen U) (hV : IsOpen V)
    (hpU : UniversalStrictPullbackComparison (restriction p U))
    (hpV : UniversalStrictPullbackComparison (restriction p V))
    (hpUV : UniversalStrictPullbackComparison (restriction p (U ∩ V))) :
    TwoChartPoolComparison p U V :=
  fun _ _ γ hc ↦ twoPoolComparison_isWeakHomotopyEquivalence p γ U V hU hV hc hpU hpV hpUV

/-- Finite HELP for the literal original strict pullback, obtained solely
from the actual two-chart pool comparisons and a finite mesh of each cube. -/
theorem strictPullbackInclusion_finiteCubeStrictHELP_of_pools
    (p : C(E, B)) (f : C(X, B)) (U V : Set B)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hp : TwoChartPoolComparison p U V) :
    FiniteCubeStrictHELP (strictPullbackInclusion p f) := by
  intro n a b w
  let H : C(unitInterval × cube.{u} n,B) := ⟨fun z ↦ (b z.2).val.2.2 z.1,by fun_prop⟩
  let k : C(cube.{u} n,X) := ⟨fun d ↦ (b d).val.1,by fun_prop⟩
  have hEnd : ∀ d,H (1,d) = f (k d) := fun d ↦ (b d).property.2
  let aD := (boundaryInclusion n).hom
  let e : C(boundary.{u} n,E) := ⟨fun z ↦ (a z).val.2,by fun_prop⟩
  have hw (z : boundary.{u} n) : strictPullbackInclusion p f (a z) = b (aD z) :=
    ContinuousMap.congr_fun w z
  have hk (z : boundary.{u} n) : k (aD z) = (a z).val.1 :=
    (congrArg (fun z ↦ z.val.1) (hw z)).symm
  have he : ∀ z,p (e z) = H (1,aD z) := by
    intro z
    exact (a z).property.trans ((hk z) ▸ (hEnd (aD z)).symm)
  have hfixed : ∀ t z,H (t,aD z) = H (1,aD z) := by
    intro t z
    exact (congrArg (fun q ↦ q.val.2.2 t) (hw z)).symm.trans
      (congrArg (fun q ↦ q.val.2.2 1) (hw z))
  let c₀ : C(cube.{u} n,Stage p H 0) := {
    toFun d := ⟨(d,(b d).val.2.1),(b d).property.1.symm⟩
    continuous_toFun := by fun_prop }
  have hc₀ : c₀.comp (boundaryInclusion n).hom = boundaryStage p H n aD e he hfixed 0 := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    refine Prod.ext rfl ?_
    exact (congrArg (fun q ↦ q.val.2.1) (hw z)).symm
  have hstart : (stageToPullback p f H k hEnd 0).comp c₀ = b := by
    apply ContinuousMap.ext
    intro d
    apply Subtype.ext
    refine Prod.ext rfl ?_
    refine Prod.ext rfl ?_
    apply ContinuousMap.ext
    intro t
    change H (affineTime 0 1 t,d) = H (t,d)
    rw [affineTime_zero_one]
  let Hraw : C(unitInterval × CubicalSubdivision.Cube n,B) :=
    ⟨fun z ↦ H (z.1,ULift.up z.2),by fun_prop⟩
  obtain ⟨m,hm⟩ := exists_uniform_two_slab_cover n Hraw U V hU hV (fun _ _ ↦ by
    rw [hcover]
    trivial)
  have hc : ∀ (i : Fin (m+1)) d,
      slabMap H m i d ∈ pathSet U ∨ slabMap H m i d ∈ pathSet V := by
    intro i d
    have h : d.down ∈ slabSet Hraw U m i ∪ slabSet Hraw V m i := by
      rw [hm i]
      trivial
    exact h
  obtain ⟨c₁,hc₁,⟨K⟩⟩ := exists_finite_time_lift p H n aD e he hfixed f k hEnd
    m U V hc (fun i ↦ hp _ (slabMap H m i) (hc i)) c₀ hc₀
  let c := (stageFinalMap p f H k hEnd).comp c₁
  refine ⟨c,?_,⟨K.cast ?_ hstart⟩⟩
  · apply ContinuousMap.ext
    intro z
    have hz : c₁ ((boundaryInclusion n) z) = boundaryStage p H n aD e he hfixed 1 z :=
      ContinuousMap.congr_fun hc₁ z
    change stageFinalMap p f H k hEnd (c₁ ((boundaryInclusion n) z)) = a z
    rw [hz]
    apply Subtype.ext
    exact Prod.ext (hk z) rfl
  · rw [stageToPullback_one]
    rfl

/-- Complete weakness of the original strict comparison, including the
actual zero-dimensional and empty-source cases. -/
theorem strictPullbackInclusion_isWeakHomotopyEquivalence_of_pools
    (p : C(E, B)) (f : C(X, B)) (U V : Set B)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hp : TwoChartPoolComparison p U V) :
    IsWeakHomotopyEquivalence (strictPullbackInclusion p f) :=
  (strictPullbackInclusion_finiteCubeStrictHELP_of_pools p f U V hU hV hcover
    hp).isWeakHomotopyEquivalence

/-- Universal strict-pullback comparison is local on a two-open cover,
using the first, second and genuine overlap original comparisons. -/
theorem universalStrictPullbackComparison_of_two_open
    (p : C(E, B)) (U V : Set B) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (hpU : UniversalStrictPullbackComparison (restriction p U))
    (hpV : UniversalStrictPullbackComparison (restriction p V))
    (hpUV : UniversalStrictPullbackComparison (restriction p (U ∩ V))) :
    UniversalStrictPullbackComparison p :=
  fun _ _ f ↦ strictPullbackInclusion_isWeakHomotopyEquivalence_of_pools p f U V hU hV hcover
    (twoChartPoolComparison_of_local p U V hU hV hpU hpV hpUV)

end Topology.PathSubdivision
