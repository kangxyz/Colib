/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyPullback.Connectivity
public import Colib.Topology.HELP.WeakFinite

/-!
# Finite-range HELP for the unchanged connected map

An n-connected original map lifts each actual cube-boundary test of dimension at most n,
retaining the entire supplied boundary track. Only the relevant finite fiber homotopy sets
are used; zero dimension uses actual nonemptiness. The existing stationary correction gives
literal boundary values. No separation or HEP hypothesis on the ambient spaces is imposed.

The connectivity convention agrees with Schwede, *The Blakers-Massey theorem*: a map is
`n`-connected when its fibers are `(n - 1)`-connected in the usual space convention.
See https://www.math.uni-bonn.de/people/schwede/Blakers-Massey.pdf.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HELP/Connectivity.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
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

/-- Only the finite homotopy degrees below the displayed bound are needed to fill each
actual boundary of dimension at most that bound; the empty boundary uses nonemptiness. -/
theorem exists_extend_boundary_of_connectivity {X : Type u} [TopologicalSpace X] [Nonempty X]
    {n : ℕ} (hs : ∀ x : X, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k X x))
    (m : ℕ) (hm : m ≤ n) (a : C(boundary.{u} m, X)) :
    ∃ c : C(cube.{u} m, X), c.comp (boundaryInclusion m).hom = a := by
  cases m with
  | zero =>
    refine ⟨ContinuousMap.const _ (Classical.choice (inferInstance : Nonempty X)), ?_⟩
    ext z
    obtain ⟨i, _⟩ := z.property
    exact Fin.elim0 i
  | succ m =>
    let e := productBoundaryHomeomorph.{u} m
    let a' := a.comp (e : C(ProductBoundary.{u} m, boundary.{u} (m + 1)))
    obtain ⟨c, hc⟩ := exists_extend_productBoundary m (fun x ↦ hs x m (by omega)) a'
    refine ⟨c.comp ((stepHomeomorph m).symm : C(cube.{u} (m + 1), cube.{u} m × unitInterval)), ?_⟩
    ext z
    have h := ContinuousMap.congr_fun hc (e.symm z)
    change c ((stepHomeomorph m).symm z.val) = a (e (e.symm z)) at h
    exact h.trans (congrArg a (e.apply_symm_apply z))

end Topology.CubicalTests

namespace Topology.IsHomotopyConnectedMap

open CubicalTests HomotopyPullback

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} {n : ℕ} (hf : IsHomotopyConnectedMap f n)
include hf

/-- Finite connectivity gives full HELP through that dimension for arbitrary original cube
boundary maps and their entire prescribed paths, with no higher-dimensional hypothesis. -/
theorem cube_fullHELP (m : ℕ) (hm : m ≤ n)
    (a : C(boundary.{u} m, X)) (b : C(cube.{u} m, Y))
    (H : (f.comp a).Homotopy (b.comp (boundaryInclusion m).hom)) :
    ∃ c : C(cube.{u} m, X), c.comp (boundaryInclusion m).hom = a ∧
      ∃ K : (f.comp c).Homotopy b,
        ∀ (t : unitInterval) (z : boundary.{u} m), K (t, z.val) = H (t, z) := by
  let P := HomotopyPullback f b
  let π := baseProjection f b
  let : Nonempty P := by
    let z := Classical.choice (hf.fiber_nonempty (b (zero m)))
    exact ⟨⟨(zero m, z.val), z.property⟩⟩
  have hs (z : P) (k : ℕ) (hk : k < n) : Subsingleton (HomotopyGroup.Pi k P z) :=
    subsingleton_homotopyGroup_of_contraction f b hf (zero m) (contraction m) z k hk
  let α : C(boundary.{u} m,P) := {
    toFun z := ⟨(z.val,a z,⟨fun t ↦ H (t,z),by fun_prop⟩),
      H.map_zero_left z,H.map_one_left z⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk continuous_subtype_val
      apply Continuous.prodMk a.continuous
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact H.continuous.comp continuous_swap }
  obtain ⟨c₀,hc₀⟩ := exists_extend_boundary_of_connectivity hs m hm α
  let d := π.comp c₀
  have hd (z : boundary.{u} m) : d z.val = z.val :=
    congrArg (fun q : P ↦ q.val.1) (ContinuousMap.congr_fun hc₀ z)
  let J := straightHomotopy m d (ContinuousMap.id _)
  have hfixed : ∀ z,boundaryDuration m z = 0 → ∀ t,J (t,z) = π (c₀ z) := by
    intro z hz t
    let z' : boundary.{u} m := ⟨z,(boundaryDuration_eq_zero_iff m z).mp hz⟩
    exact (straightHomotopy_fixed m d (ContinuousMap.id _) z (hd z') t).trans (hd z').symm
  obtain ⟨c₁,hc₁,hfix,_⟩ :=
    (baseProjection_homotopyLiftingProperty f b).correct_over_fixed_zero c₀
      (ContinuousMap.id _) J (boundaryDuration m) hfixed
  have hc (z : boundary.{u} m) : c₁ z.val = α z :=
    (hfix z.val (boundaryDuration_boundary m z)).trans (ContinuousMap.congr_fun hc₀ z)
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

/-- In a strict original square, the lift retains the whole boundary and the comparison
homotopy is fixed there, in every dimension through the given finite bound. -/
theorem cube_strictHELP (m : ℕ) (hm : m ≤ n)
    (a : C(boundary.{u} m, X)) (b : C(cube.{u} m, Y))
    (w : f.comp a = b.comp (boundaryInclusion m).hom) :
    ∃ c : C(cube.{u} m, X), c.comp (boundaryInclusion m).hom = a ∧
      Nonempty ((f.comp c).HomotopyRel b (Set.range (boundaryInclusion m))) := by
  let H : (f.comp a).Homotopy (b.comp (boundaryInclusion m).hom) :=
    (ContinuousMap.Homotopy.refl (f.comp a)).cast rfl w
  obtain ⟨c, hc, K, hK⟩ := hf.cube_fullHELP m hm a b H
  refine ⟨c, hc, ⟨{ toHomotopy := K, prop' := ?_ }⟩⟩
  rintro t z ⟨z, rfl⟩
  exact (hK t z).trans (congrArg f (ContinuousMap.congr_fun hc z)).symm

end Topology.IsHomotopyConnectedMap
