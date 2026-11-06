/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.WeakCubeFilling
public import Colib.Topology.HomotopyLifting.CubeDuration
public import Colib.Topology.HELP.PairLifting
public import Colib.Topology.HomotopyFiber.WeakPullback
public import Colib.Topology.Homotopy.HomotopyGroup.Contractible
public import Colib.Topology.CubicalSubdivision.BoundaryLifting

/-!
# Full finite cube-boundary HELP from an original weak equivalence

The original homotopy pullback over the test cube is weakly contractible.
The actual horn filling extends its boundary map. Genuine stationary lifting
of straight interpolation in the parameter cube retains every boundary point
of the homotopy pullback, including its complete original stored path. Only
finite cube-boundary tests are concluded.


Implementation provenance:
`Quillen/Topology/HELP/WeakFinite.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.CubicalTests
open Topology.HomotopyPullback


noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.CubicalTests

/-- Linear interpolation `(1 - t) * a + t * b` inside the unit interval. -/
def intervalMix (t a b : unitInterval) : unitInterval :=
  ⟨(1-(t : ℝ))*(a : ℝ)+(t : ℝ)*(b : ℝ),by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
        (mul_nonneg t.property.1 b.property.1)
    · have h₀ := mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2)
      have h₁ := mul_le_mul_of_nonneg_left b.property.2 t.property.1
      nlinarith⟩

@[fun_prop] theorem continuous_intervalMix :
    Continuous (fun z : unitInterval × (unitInterval × unitInterval) ↦
      intervalMix z.1 z.2.1 z.2.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun z : unitInterval × (unitInterval × unitInterval) ↦
    (1-(z.1 : ℝ))*(z.2.1 : ℝ)+(z.1 : ℝ)*(z.2.2 : ℝ))
  fun_prop

private theorem intervalMix_zero (a b : unitInterval) : intervalMix 0 a b = a := by
  apply Subtype.ext
  simp [intervalMix]
private theorem intervalMix_one (a b : unitInterval) : intervalMix 1 a b = b := by
  apply Subtype.ext
  simp [intervalMix]
private theorem intervalMix_self (t a : unitInterval) : intervalMix t a a = a := by
  apply Subtype.ext
  change (1-(t : ℝ))*(a : ℝ)+(t : ℝ)*(a : ℝ) = (a : ℝ)
  ring

/-- Literal coordinatewise straight interpolation in the actual finite cube. -/
def straightHomotopy {D : Type u} [TopologicalSpace D] (n : ℕ)
    (a b : C(D, cube.{u} n)) : a.Homotopy b where
  toFun z := ⟨fun i ↦ intervalMix z.1 ((a z.2).down i) ((b z.2).down i)⟩
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply continuous_pi
    intro i
    fun_prop
  map_zero_left z := by
    apply ULift.ext
    funext i
    exact intervalMix_zero _ _
  map_one_left z := by
    apply ULift.ext
    funext i
    exact intervalMix_one _ _

/-- Equal original endpoint values stay fixed for the entire interpolation. -/
theorem straightHomotopy_fixed {D : Type u} [TopologicalSpace D] (n : ℕ)
    (a b : C(D, cube.{u} n)) (z : D) (hz : a z = b z) (t : unitInterval) :
    straightHomotopy n a b (t,z) = b z := by
  apply ULift.ext
  funext i
  change intervalMix t ((a z).down i) ((b z).down i) = (b z).down i
  rw [hz,intervalMix_self]

end Topology.CubicalTests
namespace Topology.IsWeakHomotopyEquivalence
open CubicalTests HomotopyPullback
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f : C(X, Y)} (hf : IsWeakHomotopyEquivalence f)
include hf

/-- Full prescribed-boundary HELP on every actual finite cube-boundary
pair, including dimension zero and nonconstant original boundary maps.
Stationary lifting retains every original stored boundary path exactly. -/
theorem cube_fullHELP (n : ℕ) (a : C(boundary.{u} n, X)) (b : C(cube.{u} n, Y))
    (H : (f.comp a).Homotopy (b.comp (boundaryInclusion n).hom)) :
    ∃ c : C(cube.{u} n,X), c.comp (boundaryInclusion n).hom = a ∧
      ∃ K : (f.comp c).Homotopy b,
        ∀ (t : unitInterval) (z : boundary.{u} n), K (t,z.val) = H (t,z) := by
  let P := HomotopyPullback f b
  let π := baseProjection f b
  have hπ : IsWeakHomotopyEquivalence π := baseProjection_isWeakHomotopyEquivalence f b hf
  let : ContractibleSpace (cube.{u} n) :=
    (contractible_iff_id_nullhomotopic _).mpr ⟨zero n,⟨contraction n⟩⟩
  let : Nonempty P := by
    obtain ⟨z,_⟩ := hπ.component_surjective (zero n)
    exact ⟨z⟩
  have hs (z : P) (k : ℕ) : Subsingleton (HomotopyGroup.Pi k P z) := by
    let : Subsingleton (HomotopyGroup.Pi k (cube.{u} n) (π z)) :=
      subsingleton_pi_of_contractible k (cube.{u} n) (π z)
    exact (hπ.homotopy_bijective z k).injective.subsingleton
  let α : C(boundary.{u} n,P) := {
    toFun z := ⟨(z.val,a z,⟨fun t ↦ H (t,z),by fun_prop⟩),
      H.map_zero_left z,H.map_one_left z⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk continuous_subtype_val
      apply Continuous.prodMk a.continuous
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact H.continuous.comp continuous_swap }
  obtain ⟨c₀,hc₀⟩ := exists_extend_boundary hs n α
  let d := π.comp c₀
  have hd (z : boundary.{u} n) : d z.val = z.val :=
    congrArg (fun q : P ↦ q.val.1) (ContinuousMap.congr_fun hc₀ z)
  let J := straightHomotopy n d (ContinuousMap.id _)
  have hfixed : ∀ z,boundaryDuration n z = 0 → ∀ t,J (t,z) = π (c₀ z) := by
    intro z hz t
    let z' : boundary.{u} n := ⟨z,(boundaryDuration_eq_zero_iff n z).mp hz⟩
    exact (straightHomotopy_fixed n d (ContinuousMap.id _) z (hd z') t).trans (hd z').symm
  obtain ⟨c₁,hc₁,hfix,_⟩ :=
    (baseProjection_homotopyLiftingProperty f b).correct_over_fixed_zero c₀
      (ContinuousMap.id _) J (boundaryDuration n) hfixed
  have hc (z : boundary.{u} n) : c₁ z.val = α z :=
    (hfix z.val (boundaryDuration_boundary n z)).trans (ContinuousMap.congr_fun hc₀ z)
  let c := (sourceProjection f b).comp c₁
  let K : (f.comp c).Homotopy b := {
    toFun z := (c₁ z.2).val.2.2 z.1
    continuous_toFun := by fun_prop
    map_zero_left z := (c₁ z).property.1
    map_one_left z := (c₁ z).property.2.trans (congrArg b (ContinuousMap.congr_fun hc₁ z)) }
  refine ⟨c,?_,K,?_⟩
  · ext z
    exact congrArg (fun q : P ↦ q.val.2.1) (hc z)
  · intro t z
    exact congrArg (fun q : P ↦ q.val.2.2 t) (hc z)

/-- The strict-square specialization retains its entire arbitrary original
boundary map and a homotopy relative to that whole boundary. -/
theorem cube_strictHELP (n : ℕ) (a : C(boundary.{u} n, X)) (b : C(cube.{u} n, Y))
    (w : f.comp a = b.comp (boundaryInclusion n).hom) :
    ∃ c : C(cube.{u} n,X), c.comp (boundaryInclusion n).hom = a ∧
      Nonempty ((f.comp c).HomotopyRel b (Set.range (boundaryInclusion n))) := by
  let H : (f.comp a).Homotopy (b.comp (boundaryInclusion n).hom) :=
    (ContinuousMap.Homotopy.refl (f.comp a)).cast rfl w
  obtain ⟨c,hc,K,hK⟩ := hf.cube_fullHELP n a b H
  refine ⟨c,hc,⟨{ toHomotopy := K,prop' := ?_ }⟩⟩
  rintro t z ⟨z,rfl⟩
  exact (hK t z).trans (congrArg f (ContinuousMap.congr_fun hc z)).symm

/-- The original mapping-path endpoint lifts every literal finite cube
boundary, with its entire stored original boundary path preserved. -/
theorem mappingPath_endpoint_boundaryLifting :
    CubicalSubdivision.BoundaryLifting (MappingPath.endpoint f) := by
  apply CubicalSubdivision.boundaryLifting_of_hasLiftingProperty
  intro n
  exact MappingPath.endpoint_hasLiftingProperty_of_pairHELP f (boundaryInclusion n)
    (fun a b H ↦ hf.cube_fullHELP n a b H)

end Topology.IsWeakHomotopyEquivalence
