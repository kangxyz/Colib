/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.CategoryTheory.Groupoid.Subgroupoid
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Subpath
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Local-to-global tools for a realized edge-path presentation

An open cover generates the genuine topological fundamental groupoid. The proof
subdivides an arbitrary continuous path, using compactness of the unit interval,
and applies actual endpoint-fixed subpath homotopies. In particular, it does not
assume that an arbitrary path is piecewise linear or already lies in a skeleton.

This is a topology-side ingredient for an edge-path presentation, not the
presentation theorem itself: applying it to simplicial edge paths still requires
suitable open neighborhoods in the realization and the local edge-path lemma.
-/
/-!
Adapted from `Quillen/Topology/Realization/EdgePathPresentation/Basic.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This generic layer uses only the pinned Mathlib topology and groupoid APIs.
It does not assert a finite traversal decomposition into original graph edges.
The source path, endpoint, cover and universe hypotheses are retained.
-/
@[expose] public section


noncomputable section

open CategoryTheory Set
open scoped Topology unitInterval

universe u v


section OpenCover

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- A continuous path has a finite monotone subdivision subordinate to any open
cover of its image. No local connectedness hypothesis is required. -/
theorem Path.exists_subdivision_openCover {x y : X} (p : Path x y)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.range p ⊆ ⋃ i, U i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval),
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∀ k : Fin n, ∃ i, Set.range (p.subpath (t k.castSucc) (t k.succ)) ⊆ U i := by
  obtain ⟨t, ht0, htmono, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i ↦ p ⁻¹' U i)
      (fun i ↦ (hU i).preimage p.continuous) (by
        intro z _
        simpa only [Set.mem_iUnion, Set.mem_preimage] using hcover (Set.mem_range_self z))
  refine ⟨n, fun k ↦ t k.val, ht0, htn n le_rfl, fun a b hab ↦ htmono hab, ?_⟩
  intro k
  obtain ⟨i, hi⟩ := htU k.val
  refine ⟨i, ?_⟩
  change Set.range (p.subpath (t k.val) (t (k.val + 1))) ⊆ U i
  rw [Path.range_subpath_of_le _ _ _ (htmono (Nat.le_succ k.val))]
  rintro _ ⟨z, hz, rfl⟩
  exact hi hz

/-- Membership of a path class in a subgroupoid is invariant under changing
its endpoints along equalities. -/
theorem FundamentalGroupoid.pathClass_mem_cast_iff
    (S : Subgroupoid (FundamentalGroupoid X)) {x y x' y' : X}
    (p : Path x y) (hx : x' = x) (hy : y' = y) :
    (⟦p.cast hx hy⟧ : FundamentalGroupoid.mk x' ⟶ FundamentalGroupoid.mk y') ∈
      S.arrows _ _ ↔
    (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _ := by
  subst hx hy
  rfl

/-- Pointwise equal paths determine the same subgroupoid membership even
when their endpoint equalities are not definitionally equal. -/
theorem FundamentalGroupoid.pathClass_mem_of_pointwise_eq
    (S : Subgroupoid (FundamentalGroupoid X)) {x y x' y' : X}
    (p : Path x y) (q : Path x' y') (h : ∀ t, p t = q t)
    (hq : (⟦q⟧ : FundamentalGroupoid.mk x' ⟶ FundamentalGroupoid.mk y') ∈ S.arrows _ _) :
    (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _ := by
  have hx : x = x' := by simpa using h 0
  have hy : y = y' := by simpa using h 1
  have heq : p = q.cast hx hy := by ext t; exact h t
  rw [heq]
  exact (FundamentalGroupoid.pathClass_mem_cast_iff S q hx hy).mpr hq

/-- A subgroupoid containing every path lying in one member of an open cover
contains every path in the space. This is the generation half of the open-cover
fundamental-groupoid argument, proved using actual topological subdivisions. -/
theorem FundamentalGroupoid.path_mem_of_openCover
    (S : Subgroupoid (FundamentalGroupoid X))
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.univ ⊆ ⋃ i, U i)
    (hlocal : ∀ (i : ι) {x y : X} (p : Path x y), Set.range p ⊆ U i →
      (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _)
    {x y : X} (p : Path x y) :
    (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _ := by
  obtain ⟨t, ht0, htmono, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i ↦ p ⁻¹' U i)
      (fun i ↦ (hU i).preimage p.continuous) (by
        intro z _
        simpa only [Set.mem_iUnion, Set.mem_preimage] using hcover (Set.mem_univ (p z)))
  have hsub (k : ℕ) :
      (⟦p.subpath (t 0) (t k)⟧ : FundamentalGroupoid.mk (p (t 0)) ⟶
        FundamentalGroupoid.mk (p (t k))) ∈ S.arrows _ _ := by
    induction k with
    | zero =>
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ (p (t 0))))
      apply hlocal i
      rintro _ ⟨z, rfl⟩
      simpa only [Path.subpath_self, Path.refl_apply] using hi
    | succ k ih =>
      obtain ⟨i, hi⟩ := htU k
      have hstep : (⟦p.subpath (t k) (t (k + 1))⟧ :
          FundamentalGroupoid.mk (p (t k)) ⟶ FundamentalGroupoid.mk (p (t (k + 1)))) ∈
          S.arrows _ _ := by
        apply hlocal i
        rw [Path.range_subpath_of_le _ _ _ (htmono (Nat.le_succ k))]
        rintro _ ⟨z, hz, rfl⟩
        exact hi hz
      have hcomp := S.mul ih hstep
      change (Path.Homotopic.Quotient.mk (p.subpath (t 0) (t k))).trans
        (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) ∈ S.arrows _ _ at hcomp
      have hjoin :
          (Path.Homotopic.Quotient.mk (p.subpath (t 0) (t k))).trans
            (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) =
          Path.Homotopic.Quotient.mk (p.subpath (t 0) (t (k + 1))) := by
        exact Quotient.sound ⟨Path.Homotopy.subpathTransSubpath p (t 0) (t k) (t (k + 1))⟩
      rw [hjoin] at hcomp
      exact hcomp
  have hfinal := hsub n
  rw [ht0, htn n le_rfl, Path.subpath_zero_one] at hfinal
  exact (FundamentalGroupoid.pathClass_mem_cast_iff S p p.source p.target).mp hfinal

/-- The actual topological fundamental groupoid is generated by paths contained
in members of any open cover. The cover may have arbitrary cardinality. -/
theorem FundamentalGroupoid.subgroupoid_eq_top_of_openCover
    (S : Subgroupoid (FundamentalGroupoid X))
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.univ ⊆ ⋃ i, U i)
    (hlocal : ∀ (i : ι) {x y : X} (p : Path x y), Set.range p ⊆ U i →
      (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _) :
    S = ⊤ := by
  apply top_unique
  rw [Subgroupoid.le_iff]
  rintro ⟨x⟩ ⟨y⟩ p _
  refine Quotient.inductionOn p ?_
  intro p
  exact FundamentalGroupoid.path_mem_of_openCover S U hU hcover hlocal p

/-- Compactness also gives a common finite grid for an arbitrary continuous
square. This supplies simultaneous subdivision in the homotopy and path
directions for the relation part of an open-cover presentation. -/
theorem ContinuousMap.square_exists_subdivision_openCover
    (H : C(unitInterval × unitInterval, X))
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.range H ⊆ ⋃ i, U i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval),
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∀ j k : Fin n, ∃ i,
        H '' (Set.Icc (t j.castSucc) (t j.succ) ×ˢ
          Set.Icc (t k.castSucc) (t k.succ)) ⊆ U i := by
  obtain ⟨t, ht0, htmono, ⟨n, htn⟩, htU⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (c := fun i ↦ H ⁻¹' U i)
      (fun i ↦ (hU i).preimage H.continuous) (by
        intro z _
        simpa only [Set.mem_iUnion, Set.mem_preimage] using hcover (Set.mem_range_self z))
  refine ⟨n, fun k ↦ t k.val, ht0, htn n le_rfl, fun a b hab ↦ htmono hab, ?_⟩
  intro j k
  obtain ⟨i, hi⟩ := htU j.val k.val
  exact ⟨i, Set.image_subset_iff.mpr hi⟩

/-- Two ambient paths contained in a simply connected subset are homotopic
in the ambient space, with their endpoints fixed throughout. -/
theorem Path.homotopic_of_range_subset_isSimplyConnected
    {V : Set X} (hV : IsSimplyConnected V) {x y : X}
    (p q : Path x y) (hp : Set.range p ⊆ V) (hq : Set.range q ⊆ V) :
    p.Homotopic q := by
  let := hV.simplyConnectedSpace
  let x' : V := ⟨x, hp p.source_mem_range⟩
  let y' : V := ⟨y, hp p.target_mem_range⟩
  let p' : Path x' y' := {
    toFun := fun t ↦ ⟨p t, hp (Set.mem_range_self t)⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := Subtype.ext p.source
    target' := Subtype.ext p.target }
  let q' : Path x' y' := {
    toFun := fun t ↦ ⟨q t, hq (Set.mem_range_self t)⟩
    continuous_toFun := q.continuous.subtype_mk _
    source' := Subtype.ext q.source
    target' := Subtype.ext q.target }
  have H := (SimplyConnectedSpace.paths_homotopic p' q').map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X))
  exact H

/-- For a simply connected open cover it suffices to supply one chosen local
path class for each pair of endpoints. All other topological paths are then
generated automatically, rather than assumed to be edge paths. -/
theorem FundamentalGroupoid.subgroupoid_eq_top_of_simplyConnected_openCover
    (S : Subgroupoid (FundamentalGroupoid X))
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.univ ⊆ ⋃ i, U i) (hsc : ∀ i, IsSimplyConnected (U i))
    (hchosen : ∀ (i : ι) (x y : X), x ∈ U i → y ∈ U i →
      ∃ p : Path x y, Set.range p ⊆ U i ∧
        (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _) :
    S = ⊤ := by
  apply FundamentalGroupoid.subgroupoid_eq_top_of_openCover S U hU hcover
  intro i x y p hp
  obtain ⟨q, hq, hqS⟩ := hchosen i x y (hp p.source_mem_range) (hp p.target_mem_range)
  have heq : (⟦p⟧ : Path.Homotopic.Quotient x y) = ⟦q⟧ :=
    Quotient.sound (Path.homotopic_of_range_subset_isSimplyConnected (hsc i) p q hp hq)
  rw [heq]
  exact hqS

end OpenCover


attribute [colib_tag "COL-0087",
  colib_ref "HatcherAT" "Section 1.1, proof of Lemma 1.15, page 35"
    "adaptation"
    "Compact-interval subdivision subordinate to an open cover of the path image"]
  Path.exists_subdivision_openCover

attribute [colib_tag "COL-0087",
  colib_ref "HatcherAT" "Section 1.2, proof of the van Kampen theorem, page 45"
    "adaptation"
    "Square subdivision subordinate to an open cover, with a common refined grid"]
  ContinuousMap.square_exists_subdivision_openCover

attribute [colib_tag "COL-0087",
  colib_ref "HatcherAT" "Section 1.1, Proposition 1.6, page 28"
    "adaptation"
    "Paths lying in a simply connected subset are homotopic with fixed endpoints"]
  Path.homotopic_of_range_subset_isSimplyConnected

attribute [colib_tag "COL-0087",
  colib_ref "HatcherAT" "Section 1.1, proof of Lemma 1.15, page 35"
    "background"
    "Local path classes generate a wide subgroupoid; not the based van Kampen theorem"]
  FundamentalGroupoid.path_mem_of_openCover
  FundamentalGroupoid.subgroupoid_eq_top_of_openCover
  FundamentalGroupoid.subgroupoid_eq_top_of_simplyConnected_openCover
