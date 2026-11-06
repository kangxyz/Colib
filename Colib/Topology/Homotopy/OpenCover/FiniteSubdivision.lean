/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.ChartHomotopy

/-!
# Finite Subdivision

Every affine subpath of a chart-contained path stays in the same chart.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Set
universe u v w z
namespace FundamentalGroupoid.OpenCover.ChartData
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable {C : Type w} [Category.{z} C] {U : ι → Set X}
variable (d : ChartData (C := C) U)

/-- Every affine subpath of a chart-contained path stays in the same chart. -/
theorem subpath_contained (i : ι) {x y : X} (p : Path x y)
    (hp : Set.range p ⊆ U i) (a b : unitInterval) :
    Set.range (p.subpath a b) ⊆ U i := by
  rintro _ ⟨t, rfl⟩
  exact hp ⟨_, rfl⟩

/-- Any finite sequence of parameter values defines the actual local subpath
functor. No monotonicity or distinctness is required for this local identity. -/
def localSubpathFunctor (i : ι) {x y : X} (p : Path x y)
    (hp : Set.range p ⊆ U i) {n : ℕ} (t : Fin (n + 1) → unitInterval) :
    Fin (n + 1) ⥤ C where
  obj j := d.obj (p (t j))
  map {j k} _ := d.localValue i (p.subpath (t j) (t k))
    (subpath_contained i p hp (t j) (t k))
  map_id j := by
    simpa only [Path.subpath_self] using d.localValue_refl i (p (t j))
      (by rintro _ ⟨s, rfl⟩; exact hp (Set.mem_range_self (t j)))
  map_comp {j k l} _ _ :=
    (d.localValue_subpath_split i p hp (t j) (t k) (t l) _ _ _).symm

/-- In one chart the ordered value of every finite subdivision is the value
of the actual endpoint subpath. Thus all such subdivisions with the same
endpoints agree, even with repeated breakpoints. -/
theorem localValue_finiteSubdivision (i : ι) {x y : X} (p : Path x y)
    (hp : Set.range p ⊆ U i) {n : ℕ} (t : Fin (n + 1) → unitInterval) :
    finiteChainComp (fun j => d.obj (p (t j)))
      (fun j => d.localValue i (p.subpath (t j.castSucc) (t j.succ))
        (subpath_contained i p hp (t j.castSucc) (t j.succ))) =
      d.localValue i (p.subpath (t 0) (t (Fin.last n)))
        (subpath_contained i p hp (t 0) (t (Fin.last n))) := by
  let F := d.localSubpathFunctor i p hp t
  let K := ComposableArrows.mkOfObjOfMapSucc (fun j => d.obj (p (t j)))
    (fun j => d.localValue i (p.subpath (t j.castSucc) (t j.succ))
      (subpath_contained i p hp (t j.castSucc) (t j.succ)))
  let α : K ⟶ F := ComposableArrows.homMk (fun j => 𝟙 (d.obj (p (t j)))) (by
    intro j hj
    simp only [K, ComposableArrows.mkOfObjOfMapSucc_map_succ]
    dsimp [F, localSubpathFunctor, ComposableArrows.map']
    simp only [Category.comp_id, Category.id_comp])
  have h := α.naturality (homOfLE (Fin.zero_le (Fin.last n)))
  change K.map (homOfLE (Fin.zero_le (Fin.last n))) ≫ 𝟙 _ =
    𝟙 _ ≫ F.map (homOfLE (Fin.zero_le (Fin.last n))) at h
  simpa only [Category.comp_id, Category.id_comp] using! h

end FundamentalGroupoid.OpenCover.ChartData
