/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.MaxGrid

/-!
# Value Equality

The finite ordered composite of identity arrows is the identity, including
an empty chain. This uses the native ComposableArrows chain construction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Set
universe u v w z
namespace FundamentalGroupoid.OpenCover

/-- The finite ordered composite of identity arrows is the identity, including
an empty chain. This uses the native ComposableArrows chain construction. -/
theorem finiteChainComp_id {C : Type w} [Category.{z} C] (c : C) (n : ℕ) :
    finiteChainComp (fun _ : Fin (n + 1) => c) (fun _ => 𝟙 c) = 𝟙 c := by
  let K := ComposableArrows.mkOfObjOfMapSucc (fun _ : Fin (n + 1) => c) (fun _ => 𝟙 c)
  let F := (Functor.const (Fin (n + 1))).obj c
  let α : K ⟶ F := ComposableArrows.homMk (fun _ => 𝟙 c) (by
    intro j hj
    simp only [K, ComposableArrows.mkOfObjOfMapSucc_map_succ]
    simp [F, ComposableArrows.map'])
  have h := α.naturality (homOfLE (Fin.zero_le (Fin.last n)))
  change K.map _ ≫ 𝟙 c = 𝟙 c ≫ 𝟙 c at h
  change finiteChainComp (fun _ : Fin (n + 1) => c) (fun _ => 𝟙 c) ≫ 𝟙 c =
    𝟙 c ≫ 𝟙 c at h
  simpa only [Category.comp_id] using h

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}

/-- Every edge in a max-grid has a chart: a nonconstant edge lies in its original
segment chart, and a constant edge uses the cover at its actual value. -/
theorem maxSubpath_exists_chart {x y : X} (p : Path x y)
    (hcover : Set.range p ⊆ ⋃ i, U i) (a b c : unitInterval) (hab : a ≤ b)
    (i : ι) (hp : Set.range (p.subpath a b) ⊆ U i) :
    ∃ j, Set.range (p.subpath (max c a) (max c b)) ⊆ U j := by
  by_cases hcb : c ≤ b
  · refine ⟨i, ?_⟩
    rw [Path.range_subpath_of_le p _ _ (max_le_max_left c hab)]
    rintro _ ⟨r, hr, rfl⟩
    apply hp
    rw [Path.range_subpath_of_le p a b hab]
    exact ⟨r, ⟨(le_max_right c a).trans hr.1,
      hr.2.trans (max_le hcb le_rfl)⟩, rfl⟩
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover (Set.mem_range_self c))
    refine ⟨j, ?_⟩
    have hbc : b ≤ c := le_of_not_ge hcb
    rw [max_eq_left (hab.trans hbc), max_eq_left hbc, Path.subpath_self]
    rintro _ ⟨t, rfl⟩
    exact hj

end FundamentalGroupoid.OpenCover
