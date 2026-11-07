/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.CompactComparison
public import Colib.Topology.Homotopy.HomotopyGroup.WeakLocality
public import Colib.Topology.PathSubdivision.SlabCover

/-!
# Weak comparison with the actual one-chart and two-chart path pools

The parameter space is arbitrary. A pool point keeps its original parameter,
source and complete free path to the terminal value of the displayed family.
The local assumption is universal strict-pullback comparison weakness, not a
compactness assumption on an open parameter locus. Compact HLP of each local
restriction is a proved sufficient input.


Implementation provenance:
`Quillen/Topology/PathSubdivision/PoolComparison.lean`
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

/-- The original strict comparison is weak after every base change in the
specified universe. No lifting operation or global inverse is part of this
hypothesis. -/
def UniversalStrictPullbackComparison {E B : Type u}
    [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) : Prop :=
  ∀ (D : Type u) [TopologicalSpace D] (f : C(D,B)),
    IsWeakHomotopyEquivalence (HomotopyPullback.strictPullbackInclusion p f)

/-- Actual compact HLP supplies the universal comparison premise. -/
theorem CompactHomotopyLiftingProperty.universalStrictPullbackComparison
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : CompactHomotopyLiftingProperty p) :
    UniversalStrictPullbackComparison p :=
  fun _ _ f ↦ HomotopyPullback.strictPullbackInclusion_isWeakHomotopyEquivalence_of_compact p f hp

namespace PathSubdivision
open HomotopyPullback CubicalSubdivision
variable {D E B : Type u}
  [TopologicalSpace D] [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B)) (γ : C(D, C(unitInterval, B)))

/-- The endpoint of the original family, with no choice of a path representative. -/
def endpoint : C(D,B) := ⟨fun d ↦ γ d 1,by fun_prop⟩

/-- The literal endpoint strict pullback. -/
abbrev StrictPool := {z : D × E // p z.2 = endpoint γ z.1}

/-- Both the entire family track and the entire free stored path lie in the
same chart. Endpoint membership alone is not used. -/
def chartSet (U : Set B) : Set (HomotopyPullback p (endpoint γ)) :=
  {z | γ z.1.1 ∈ pathSet U ∧ z.1.2.2 ∈ pathSet U}

theorem chartSet_isOpen {U : Set B} (hU : IsOpen U) : IsOpen (chartSet p γ U) := by
  exact ((pathSet_isOpen hU).preimage (by fun_prop :
    Continuous (fun z : HomotopyPullback p (endpoint γ) ↦ γ z.1.1))).inter
      ((pathSet_isOpen hU).preimage (by fun_prop :
        Continuous (fun z : HomotopyPullback p (endpoint γ) ↦ z.1.2.2)))

theorem chartSet_inter (U V : Set B) :
    chartSet p γ (U ∩ V) = chartSet p γ U ∩ chartSet p γ V := by
  ext z
  constructor
  · intro h
    exact ⟨⟨fun t ↦ (h.1 t).1,fun t ↦ (h.2 t).1⟩,
      ⟨fun t ↦ (h.1 t).2,fun t ↦ (h.2 t).2⟩⟩
  · intro h
    exact ⟨fun t ↦ ⟨h.1.1 t,h.2.1 t⟩,fun t ↦ ⟨h.1.2 t,h.2.2 t⟩⟩

/-- The original constant path belongs to a chart pool exactly when its
original parameter's whole family track belongs to that chart. -/
theorem strictPullbackInclusion_mem_chartSet_iff (U : Set B) (z : StrictPool p γ) :
    strictPullbackInclusion p (endpoint γ) z ∈ chartSet p γ U ↔ γ z.1.1 ∈ pathSet U :=
  ⟨fun h ↦ h.1,fun h ↦ ⟨h,fun _ ↦ h 1⟩⟩

/-- Original parameters whose entire family path lies in the chart. -/
abbrev ChartParameter (U : Set B) := {d : D // γ d ∈ pathSet U}

/-- The endpoint map into the actual chart, on its whole-track parameter locus. -/
def chartEndpoint (U : Set B) : C(ChartParameter γ U,U) :=
  ⟨fun d ↦ ⟨γ d.1 1,d.2 1⟩,by fun_prop⟩

/-- A literal chart source is the strict pullback of the local original map
on the unrestricted whole-track parameter locus. -/
def chartSourceHomeomorph (U : Set B) :
    {z : StrictPool p γ // strictPullbackInclusion p (endpoint γ) z ∈ chartSet p γ U} ≃ₜ
      {z : ChartParameter γ U × {e : E // p e ∈ U} //
        restriction p U z.2 = chartEndpoint γ U z.1} where
  toFun z := ⟨(⟨z.1.1.1,z.2.1⟩,⟨z.1.1.2,by
    rw [z.1.2]
    exact z.2.1 1⟩),Subtype.ext z.1.2⟩
  invFun z := ⟨⟨(z.1.1.1,z.1.2.1),congrArg Subtype.val z.2⟩,
    z.1.1.2,fun _ ↦ z.1.1.2 1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The one-chart free-path pool is exactly the actual homotopy pullback of
that local restriction, retaining all parameter, source and path values. -/
def chartTargetHomeomorph (U : Set B) :
    (chartSet p γ U) ≃ₜ HomotopyPullback (restriction p U) (chartEndpoint γ U) where
  toFun z := ⟨(⟨z.1.1.1,z.2.1⟩,⟨z.1.1.2.1,by
    rw [← z.1.2.1]
    exact z.2.2 0⟩,⟨fun t ↦ ⟨z.1.1.2.2 t,z.2.2 t⟩,by fun_prop⟩),
    Subtype.ext z.1.2.1,Subtype.ext z.1.2.2⟩
  invFun z := ⟨⟨(z.1.1.1,z.1.2.1.1,
    ⟨fun t ↦ (z.1.2.2 t).1,by fun_prop⟩),
      congrArg Subtype.val z.2.1,congrArg Subtype.val z.2.2⟩,
    z.1.1.2,fun t ↦ (z.1.2.2 t).2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext rfl ?_
    refine Prod.ext rfl ?_
    ext t
    rfl
  right_inv z := by
    apply Subtype.ext
    refine Prod.ext rfl ?_
    refine Prod.ext rfl ?_
    ext t
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (chartSet p γ U) × unitInterval ↦
      (⟨z.1.1.1.2.2 z.2,z.1.2.2 z.2⟩ : U))
    apply Continuous.subtype_mk
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z :
      HomotopyPullback (restriction p U) (chartEndpoint γ U) × unitInterval ↦
        (z.1.1.2.2 z.2).1)
    fun_prop

/-- Codomain restriction of the original comparison to a specified pool. -/
def poolComparison (P : Set (HomotopyPullback p (endpoint γ)))
    (hP : ∀ z : StrictPool p γ,strictPullbackInclusion p (endpoint γ) z ∈ P) :
    C(StrictPool p γ,P) :=
  ⟨fun z ↦ ⟨strictPullbackInclusion p (endpoint γ) z,hP z⟩,by fun_prop⟩

/-- Flatten the chart restriction inside a larger pool without changing any
of its original three coordinates. -/
def poolChartHomeomorph (P : Set (HomotopyPullback p (endpoint γ)))
    (U : Set B) (hU : chartSet p γ U ⊆ P) :
    {z : P // z.1 ∈ chartSet p γ U} ≃ₜ chartSet p γ U where
  toFun z := ⟨z.1.1,z.2⟩
  invFun z := ⟨⟨z.1,hU z.2⟩,z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The exact chart comparison is the original strict comparison of the
local restriction, under genuine source and target homeomorphisms. -/
theorem poolComparison_chart_naturality
    (P : Set (HomotopyPullback p (endpoint γ)))
    (hP : ∀ z : StrictPool p γ,strictPullbackInclusion p (endpoint γ) z ∈ P)
    (U : Set B) (hU : chartSet p γ U ⊆ P) :
    ((poolChartHomeomorph p γ P U hU).trans (chartTargetHomeomorph p γ
      U)).toHomotopyEquiv.toFun.comp
      (restriction (poolComparison p γ P hP) {z : P | z.1 ∈ chartSet p γ U}) =
    (strictPullbackInclusion (restriction p U) (chartEndpoint γ U)).comp
      (chartSourceHomeomorph p γ U).toHomotopyEquiv.toFun := rfl

/-- A genuine one-chart restriction of the pool comparison is weak from
universal comparison weakness on that chart. Its parameter locus is arbitrary. -/
theorem poolComparison_chart_isWeakHomotopyEquivalence
    (P : Set (HomotopyPullback p (endpoint γ)))
    (hP : ∀ z : StrictPool p γ,strictPullbackInclusion p (endpoint γ) z ∈ P)
    (U : Set B) (hU : chartSet p γ U ⊆ P)
    (hp : UniversalStrictPullbackComparison (restriction p U)) :
    IsWeakHomotopyEquivalence
      (restriction (poolComparison p γ P hP) {z : P | z.1 ∈ chartSet p γ U}) := by
  have h := (hp (ChartParameter γ U) (chartEndpoint γ U)).comp
    (isWeakHomotopyEquivalence_of_homotopyEquiv (chartSourceHomeomorph p γ U).toHomotopyEquiv)
  rw [← poolComparison_chart_naturality p γ P hP U hU] at h
  exact IsWeakHomotopyEquivalence.of_comp_right h
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      ((poolChartHomeomorph p γ P U hU).trans (chartTargetHomeomorph p γ U)).toHomotopyEquiv)

/-- The actual two-chart pool contains a source and a free path to the slab
endpoint, sharing a whole-path chart with the original family track. -/
abbrev TwoPool (U V : Set B) := chartSet p γ U ∪ chartSet p γ V

/-- The canonical pool comparison stores the literal constant terminal path. -/
def twoPoolComparison (U V : Set B)
    (hcover : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V) :
    C(StrictPool p γ,TwoPool p γ U V) :=
  poolComparison p γ (TwoPool p γ U V) (fun z ↦ by
    rcases hcover z.1.1 with h | h
    · exact Or.inl ⟨h,fun _ ↦ h 1⟩
    · exact Or.inr ⟨h,fun _ ↦ h 1⟩)

/-- Forget only the pool-membership proof, retaining the actual homotopy
pullback point and its full path. -/
def twoPoolForget (U V : Set B) :
    C(TwoPool p γ U V,HomotopyPullback p (endpoint γ)) := ⟨Subtype.val,by fun_prop⟩

@[simp] theorem twoPoolForget_comparison (U V : Set B)
    (hcover : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V) :
    (twoPoolForget p γ U V).comp (twoPoolComparison p γ U V hcover) =
      strictPullbackInclusion p (endpoint γ) := rfl

@[simp] theorem twoPoolComparison_parameter (U V : Set B)
    (hcover : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V) (z : StrictPool p γ) :
    (twoPoolComparison p γ U V hcover z).1.1.1 = z.1.1 := rfl

@[simp] theorem twoPoolComparison_source (U V : Set B)
    (hcover : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V) (z : StrictPool p γ) :
    (twoPoolComparison p γ U V hcover z).1.1.2.1 = z.1.2 := rfl

@[simp] theorem twoPoolComparison_path (U V : Set B)
    (hcover : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V) (z : StrictPool p γ) :
    (twoPoolComparison p γ U V hcover z).1.1.2.2 =
      ContinuousMap.const unitInterval (γ z.1.1 1) := rfl

/-- Enter the same pool from an original lift of the slab's initial value,
using the entire original family path as the free stored path. -/
def twoPoolEntrance (U V : Set B)
    (hcover : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V) :
    C({z : D × E // p z.2 = γ z.1 0},TwoPool p γ U V) where
  toFun z := ⟨⟨(z.1.1,z.1.2,γ z.1.1),z.2.symm,rfl⟩,by
    rcases hcover z.1.1 with h | h
    · exact Or.inl ⟨h,h⟩
    · exact Or.inr ⟨h,h⟩⟩
  continuous_toFun := by fun_prop

@[simp] theorem twoPoolEntrance_parameter (U V : Set B)
    (hcover : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V)
    (z : {z : D × E // p z.2 = γ z.1 0}) :
    (twoPoolEntrance p γ U V hcover z).1.1.1 = z.1.1 := rfl

@[simp] theorem twoPoolEntrance_source (U V : Set B)
    (hcover : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V)
    (z : {z : D × E // p z.2 = γ z.1 0}) :
    (twoPoolEntrance p γ U V hcover z).1.1.2.1 = z.1.2 := rfl

@[simp] theorem twoPoolEntrance_path (U V : Set B)
    (hcover : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V)
    (z : {z : D × E // p z.2 = γ z.1 0}) :
    (twoPoolEntrance p γ U V hcover z).1.1.2.2 = γ z.1.1 := rfl

/-- Ordinary weak locality glues the exact pool comparison on its two open
whole-path charts and their actual overlap. The original parameter space and
its open chart loci need not be compact or locally compact. -/
theorem twoPoolComparison_isWeakHomotopyEquivalence
    (U V : Set B) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V)
    (hpU : UniversalStrictPullbackComparison (restriction p U))
    (hpV : UniversalStrictPullbackComparison (restriction p V))
    (hpUV : UniversalStrictPullbackComparison (restriction p (U ∩ V))) :
    IsWeakHomotopyEquivalence (twoPoolComparison p γ U V hcover) := by
  let P := TwoPool p γ U V
  let W : Set P := {z | z.1 ∈ chartSet p γ U}
  let Z : Set P := {z | z.1 ∈ chartSet p γ V}
  have hW : IsOpen W := (chartSet_isOpen p γ hU).preimage continuous_subtype_val
  have hZ : IsOpen Z := (chartSet_isOpen p γ hV).preimage continuous_subtype_val
  have hcover' : W ∪ Z = Set.univ := Set.eq_univ_of_forall (fun z ↦ z.2)
  apply isWeakHomotopyEquivalence_of_two_open (twoPoolComparison p γ U V hcover)
    W Z hW hZ hcover'
  · exact poolComparison_chart_isWeakHomotopyEquivalence p γ P _ U
      (fun _ h ↦ Or.inl h) hpU
  · exact poolComparison_chart_isWeakHomotopyEquivalence p γ P _ V
      (fun _ h ↦ Or.inr h) hpV
  · have hset : W ∩ Z = {z : P | z.1 ∈ chartSet p γ (U ∩ V)} := by
      ext z
      change (z.1 ∈ chartSet p γ U ∧ z.1 ∈ chartSet p γ V) ↔ _
      rw [chartSet_inter]
      rfl
    rw [hset]
    exact poolComparison_chart_isWeakHomotopyEquivalence p γ P _ (U ∩ V)
      (fun z h ↦ Or.inl ((show z ∈ chartSet p γ U ∩ chartSet p γ V from
        (chartSet_inter p γ U V) ▸ h).1)) hpUV

/-- Compact HLP of the three local restrictions is sufficient for the
arbitrary-parameter pool comparison. No global HLP is assumed. -/
theorem twoPoolComparison_isWeakHomotopyEquivalence_of_compact
    (U V : Set B) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ d, γ d ∈ pathSet U ∨ γ d ∈ pathSet V)
    (hpU : CompactHomotopyLiftingProperty (restriction p U))
    (hpV : CompactHomotopyLiftingProperty (restriction p V))
    (hpUV : CompactHomotopyLiftingProperty (restriction p (U ∩ V))) :
    IsWeakHomotopyEquivalence (twoPoolComparison p γ U V hcover) :=
  twoPoolComparison_isWeakHomotopyEquivalence p γ U V hU hV hcover
    hpU.universalStrictPullbackComparison hpV.universalStrictPullbackComparison
    hpUV.universalStrictPullbackComparison

end PathSubdivision
end Topology
