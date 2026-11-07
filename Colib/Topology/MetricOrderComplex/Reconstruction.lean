/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.RealizationCoordinates
public import Mathlib.Data.Finset.Sort
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

/-!
# Reconstruction on the exact finite chain support

Every metric point is represented by a nondegenerate simplex whose ordered
vertices are exactly its finite support, with strictly positive barycentric
weights. Injective finite-chain charts recover their original weights. In
particular the actual realization coordinate map is surjective. This does
not yet assert a continuous inverse or the global uniqueness of realization
representatives.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/Reconstruction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native realization coordinates are used. -/
@[expose] public section
noncomputable section

open CategoryTheory Convexity SSet Opposite
open scoped Simplicial

universe u v

namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- An injective chain chart loses no barycentric information. -/
theorem chainCoordinates_injective {ι : Type v} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (hi : Function.Injective v) :
    Function.Injective (chainCoordinates v hv) := by
  intro t q h
  apply StdSimplex.ext
  exact Finsupp.mapDomain_injective hi (congrArg weights h)

/-- Every metric point has a strictly ordered representative on its exact support. -/
theorem exists_strict_representation (x : MetricOrderComplex P) :
    ∃ (n : ℕ) (s : (nerve P) _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))),
      StrictMono s.obj ∧ Set.range s.obj = (x.weights.support : Set P) ∧
      (∀ i, 0 < t.weights i) ∧ simplexCoordinates s t = x := by
  classical
  let S := x.weights.support
  let : LinearOrder S := x.support_chain.lt_of_le.linearOrder
  have hcard : Fintype.card S = (S.card - 1) + 1 := by
    rw [Fintype.card_coe]
    exact (Nat.sub_add_cancel (Finset.card_pos.mpr x.support_nonempty)).symm
  let e : Fin ((S.card - 1) + 1) ≃o S := Fintype.orderIsoFinOfCardEq S hcard
  let v : Fin ((S.card - 1) + 1) → P := fun i ↦ (e i).1
  have hstrict : StrictMono v := e.strictMono
  have hrange : Set.range v = (x.weights.support : Set P) := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hp
      exact ⟨e.symm ⟨p, hp⟩, congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)⟩
  let q : StdSimplex ℝ (Fin ((S.card - 1) + 1)) := {
    weights := Finsupp.equivFunOnFinite.symm (fun i ↦ x.weights (v i))
    nonneg i := x.weights_nonneg _
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      change (∑ i, x.weights ((e i).1)) = 1
      calc
        _ = ∑ y : S, x.weights y.1 :=
          e.toEquiv.sum_comp (fun y : S ↦ x.weights y.1)
        _ = ∑ p ∈ S, x.weights p := Finset.sum_coe_sort S (fun p ↦ x.weights p)
        _ = 1 := by
          change x.weights.sum (fun _ a ↦ a) = 1
          exact x.weights_total }
  let s : (nerve P) _⦋S.card - 1⦌ := hstrict.monotone.functor
  refine ⟨S.card - 1, s, q, hstrict, hrange, ?_, ?_⟩
  · intro i
    change 0 < x.weights ((e i).1)
    exact lt_of_le_of_ne (x.weights_nonneg _) (Ne.symm (Finsupp.mem_support_iff.mp (e i).2))
  · apply ext
    intro p
    rw [simplexCoordinates_weights (n := ⦋S.card - 1⦌) s q]
    change (∑ i, Finsupp.single ((e i).1) (x.weights ((e i).1))) p = x.weights p
    have hsum : (∑ i, Finsupp.single ((e i).1) (x.weights ((e i).1))) = x.weights := by
      calc
        _ = ∑ y : S, Finsupp.single y.1 (x.weights y.1) :=
          e.toEquiv.sum_comp (fun y : S ↦ Finsupp.single y.1 (x.weights y.1))
        _ = ∑ p ∈ S, Finsupp.single p (x.weights p) :=
          Finset.sum_coe_sort S (fun p ↦ Finsupp.single p (x.weights p))
        _ = x.weights := by
          change x.weights.sum (fun p a ↦ Finsupp.single p a) = x.weights
          exact Finsupp.sum_single x.weights
    exact congrArg (fun z : P →₀ ℝ ↦ z p) hsum

/-- The reconstructed simplex is genuinely nondegenerate in the original poset nerve. -/
theorem exists_nondegenerate_representation (x : MetricOrderComplex P) :
    ∃ (n : ℕ) (s : (nerve P) _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))),
      s ∈ (nerve P).nonDegenerate n ∧ Set.range s.obj = (x.weights.support : Set P) ∧
      (∀ i, 0 < t.weights i) ∧ realizationCoordinates (realizationSimplex s t) = x := by
  obtain ⟨n, s, t, hs, hr, ht, hx⟩ := exists_strict_representation x
  exact ⟨n, s, t, (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mpr hs,
    hr, ht, (realizationCoordinates_simplex s t).trans hx⟩

/-- The actual coordinate map reaches every finitely supported chain distribution. -/
theorem realizationCoordinates_surjective :
    Function.Surjective (realizationCoordinates (P := P)) := by
  intro x
  obtain ⟨n, s, t, _, _, _, h⟩ := exists_nondegenerate_representation x
  exact ⟨realizationSimplex s t, h⟩

end Topology.MetricOrderComplex
