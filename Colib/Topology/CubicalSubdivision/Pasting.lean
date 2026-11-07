/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.Faces

/-! # Continuous pasting on the actual finite affine cube grid

The disjoint union of finitely many compact cells maps by the original affine
maps onto the Hausdorff cube, hence is an actual quotient map. Compatible
continuous cell maps therefore descend continuously, without a separation
hypothesis on the target.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/Pasting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision
universe u

/-- The original finite-cell quotient map, with no change to the cube topology. -/
def gridProjection (n m : ℕ) : C((Σ _k : CellIndex n m, Cube n), Cube n) where
  toFun z := cell n m z.1 z.2
  continuous_toFun := continuous_sigma (fun k ↦ (cell n m k).continuous)

@[simp] theorem gridProjection_apply (n m : ℕ) (k : CellIndex n m) (t : Cube n) :
    gridProjection n m ⟨k,t⟩ = cell n m k t := rfl

theorem gridProjection_surjective (n m : ℕ) : Function.Surjective (gridProjection n m) := by
  intro x
  obtain ⟨k,t,h⟩ := cell_covers n m x
  exact ⟨⟨k,t⟩,h⟩

theorem gridProjection_isQuotientMap (n m : ℕ) :
    Topology.IsQuotientMap (gridProjection n m) :=
  Topology.IsQuotientMap.of_surjective_continuous (gridProjection_surjective n m)
    (gridProjection n m).continuous

/-- Genuine continuous finite pasting, preserving every original cell map. -/
theorem exists_paste (n m : ℕ) {X : Type u} [TopologicalSpace X]
    (f : ∀ _k : CellIndex n m, C(Cube n,X))
    (hf : ∀ k l s t, cell n m k s = cell n m l t → f k s = f l t) :
    ∃ g : C(Cube n,X), ∀ k t, g (cell n m k t) = f k t := by
  choose k t ht using cell_covers n m
  let g : Cube n → X := fun x ↦ f (k x) (t x)
  have hg (l : CellIndex n m) (s : Cube n) : g (cell n m l s) = f l s :=
    hf (k (cell n m l s)) l (t (cell n m l s)) s (ht _)
  have hc : Continuous g := by
    apply (gridProjection_isQuotientMap n m).continuous_iff.2
    have hh : g ∘ gridProjection n m = fun z : Σ _k : CellIndex n m, Cube n ↦ f z.1 z.2 := by
      funext z
      exact hg z.1 z.2
    rw [hh]
    exact continuous_sigma (fun l ↦ (f l).continuous)
  exact ⟨⟨g,hc⟩,hg⟩

/-- Compatible cell data determine a unique map on the original cube. -/
theorem paste_unique (n m : ℕ) {X : Type u} [TopologicalSpace X]
    (g h : C(Cube n, X)) (he : ∀ k t, g (cell n m k t) = h (cell n m k t)) : g = h := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨k,t,rfl⟩ := cell_covers n m x
  exact he k t

/-- Pasting preserves any prescribed subset pointwise. No cofibration
assertion about that subset is needed for this elementary equality. -/
theorem paste_preserves_subset (n m : ℕ) {X : Type u} [TopologicalSpace X]
    (f : ∀ _k : CellIndex n m, C(Cube n,X)) (g : C(Cube n,X))
    (hg : ∀ k t, g (cell n m k t) = f k t)
    (S : Set (Cube n)) (a : S → X)
    (ha : ∀ k t (h : cell n m k t ∈ S), f k t = a ⟨cell n m k t,h⟩) :
    ∀ x : S, g x = a x := by
  intro x
  obtain ⟨k,t,ht⟩ := cell_covers n m x.1
  have hs : cell n m k t ∈ S := by simpa only [ht] using x.2
  have hh := (hg k t).trans (ha k t hs)
  simpa only [ht] using hh

end Topology.CubicalSubdivision
