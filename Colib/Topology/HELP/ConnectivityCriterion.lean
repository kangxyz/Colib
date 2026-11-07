/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HELP.Connectivity
public import Colib.Topology.HELP.StrictPair

/-!
# Actual finite fiber connectivity detected by finite cube HELP

A literal extension on the boundary of the `(k + 1)`-cube kills each original k-loop, including
k=0. Full finite HELP fills those boundaries in every actual homotopy fiber while retaining each
stored boundary path. The zero cube provides genuine nonempty fibers. Consequently strict HELP
through dimension n, corrected on each original HEP pair, implies n-connectivity in the convention
of `IsHomotopyConnectedMap`: fiber homotopy sets vanish for k<n, not k≤n.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HELP/ConnectivityCriterion.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Topology.CubicalTests

/-- Filling the actual next cube boundary kills every original loop in this degree, with
its entire boundary fixed. Dimension zero yields path connectedness as well. -/
theorem subsingleton_pi_of_boundary_extension {X : Type u} [TopologicalSpace X] (n : ℕ)
    (h : ∀ a : C(boundary.{u} (n + 1), X),
      ∃ c : C(cube.{u} (n + 1), X), c.comp (boundaryInclusion (n + 1)).hom = a)
    (x : X) : Subsingleton (HomotopyGroup.Pi n X x) := by
  have hnull (a : HomotopyGroup.Pi n X x) : a = Quotient.mk' GenLoop.const := by
    induction a using Quotient.inductionOn with
    | h p =>
      let top : cube.{u} n ⟶ TopCat.of X := TopCat.ofHom (ContinuousMap.const _ x)
      let horn : TopCat.of (Horn.{u} n) ⟶ TopCat.of X :=
        TopCat.ofHom ⟨fun z ↦ p z.val.1.down, by fun_prop⟩
      have w : boundaryInclusion n ≫ top = topRim n ≫ horn := by
        apply ConcreteCategory.hom_ext
        intro z
        exact (GenLoop.boundary p z.val.down z.property).symm
      let a := (hornTopDesc top horn w).hom
      let e := productBoundaryHomeomorph.{u} n
      obtain ⟨c, hc⟩ := h (a.comp (e.symm : C(boundary.{u} (n + 1), ProductBoundary.{u} n)))
      let c' := c.comp ((stepHomeomorph n) : C(cube.{u} n × unitInterval, cube.{u} (n + 1)))
      have hc' (z : ProductBoundary.{u} n) : c' z.val = a z := by
        have he := ContinuousMap.congr_fun hc (e z)
        exact he.trans (congrArg a (e.symm_apply_apply z))
      have hbottom (z : cube.{u} n) : c' (z, 0) = p z.down :=
        (hc' (hornInclusion n ⟨(z, 0), Or.inr rfl⟩)).trans
          (ConcreteCategory.congr_hom (hornInclusion_desc top horn w) ⟨(z, 0), Or.inr rfl⟩)
      have htop (z : cube.{u} n) : c' (z, 1) = x :=
        (hc' (topFace n z)).trans (ConcreteCategory.congr_hom (topFace_desc top horn w) z)
      have hside (r : unitInterval) (z : Fin n → unitInterval)
          (hz : z ∈ _root_.Cube.boundary (Fin n)) : c' (ULift.up z, r) = p z :=
        (hc' (hornInclusion n ⟨(ULift.up z, r), Or.inl hz⟩)).trans
          (ConcreteCategory.congr_hom (hornInclusion_desc top horn w)
            ⟨(ULift.up z, r), Or.inl hz⟩)
      apply Quotient.sound
      exact ⟨{
        toHomotopy := {
          toFun z := c' (ULift.up z.2, z.1)
          continuous_toFun := by fun_prop
          map_zero_left z := hbottom (ULift.up z)
          map_one_left z := htop (ULift.up z) }
        prop' := hside }⟩
  exact ⟨fun a b ↦ (hnull a).trans (hnull b).symm⟩

end Topology.CubicalTests

namespace Topology

/-- Full HELP on one actual cube-boundary pair extends every map of that boundary into each
actual path-space fiber, keeping both original source points and the whole stored paths. -/
theorem homotopyFiber_boundary_extension_of_cubeHELP
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (m : ℕ)
    (hf : ∀ (a : C(CubicalTests.boundary.{u} m, X)) (b : C(CubicalTests.cube.{u} m, Y))
      (H : (f.comp a).Homotopy (b.comp (CubicalTests.boundaryInclusion m).hom)),
      ∃ c : C(CubicalTests.cube.{u} m, X), c.comp (CubicalTests.boundaryInclusion m).hom = a ∧
        ∃ K : (f.comp c).Homotopy b, ∀ t z, K (t, z.val) = H (t, z))
    (y : Y) (a : C(CubicalTests.boundary.{u} m, HomotopyFiber f y)) :
    ∃ c : C(CubicalTests.cube.{u} m, HomotopyFiber f y),
      c.comp (CubicalTests.boundaryInclusion m).hom = a := by
  let src := (HomotopyFiber.projection f y).comp a
  let b := ContinuousMap.const (CubicalTests.cube.{u} m) y
  let H : (f.comp src).Homotopy (b.comp (CubicalTests.boundaryInclusion m).hom) := {
    toFun z := (a z.2).val.2 z.1
    continuous_toFun := by fun_prop
    map_zero_left z := (a z).property.1
    map_one_left z := (a z).property.2 }
  obtain ⟨c, hc, K, hK⟩ := hf src b H
  let c' : C(CubicalTests.cube.{u} m, HomotopyFiber f y) := {
    toFun x := ⟨(c x, ⟨fun t ↦ K (t, x), by fun_prop⟩), K.map_zero_left x, K.map_one_left x⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk c.continuous
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact K.continuous.comp continuous_swap }
  refine ⟨c', ?_⟩
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact Prod.ext (ContinuousMap.congr_fun hc z) (ContinuousMap.ext (fun t ↦ hK t z))

/-- Genuine strict cube HELP through dimension n proves the finite all-point fiber bound
of the original map. Only those dimensions are used; the whole specified boundary homotopy
is recovered by the existing exact HEP correction on each original cube pair. -/
theorem isHomotopyConnectedMap_of_cube_strictHELP
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (hf : ∀ m : ℕ, m ≤ n →
      ∀ (a : C(CubicalTests.boundary.{u} m, X)) (b : C(CubicalTests.cube.{u} m, Y)),
        f.comp a = b.comp (CubicalTests.boundaryInclusion m).hom →
          ∃ c : C(CubicalTests.cube.{u} m, X),
            c.comp (CubicalTests.boundaryInclusion m).hom = a ∧
              Nonempty ((f.comp c).HomotopyRel b
                (Set.range (CubicalTests.boundaryInclusion m)))) :
    IsHomotopyConnectedMap f n := by
  have hfull (m : ℕ) (hm : m ≤ n) :=
    fullHELP_at_pair_of_strict f _ _ (CubicalTests.boundaryInclusion m)
      (CubicalTests.boundaryInclusion_hep m) (hf m hm)
  have hfill (y : Y) (m : ℕ) (hm : m ≤ n) :=
    homotopyFiber_boundary_extension_of_cubeHELP f m (hfull m hm) y
  refine ⟨?_, ?_⟩
  · intro y
    let : IsEmpty (CubicalTests.boundary.{u} 0) := ⟨fun z ↦ by
      obtain ⟨i, _⟩ := z.property
      exact Fin.elim0 i⟩
    let a : C(CubicalTests.boundary.{u} 0, HomotopyFiber f y) :=
      ⟨isEmptyElim, continuous_of_discreteTopology⟩
    obtain ⟨c, _⟩ := hfill y 0 (Nat.zero_le n) a
    exact ⟨c (CubicalTests.zero 0)⟩
  · intro y z k hk
    exact CubicalTests.subsingleton_pi_of_boundary_extension k (hfill y (k + 1) (by omega)) z

end Topology
