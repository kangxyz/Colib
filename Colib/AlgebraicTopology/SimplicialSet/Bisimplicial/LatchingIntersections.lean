/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.Bisimplicial.Latching
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! Implementation provenance: adapted from
`Quillen/Topology/Realization/BisimplicialLatchingIntersections.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native simplicial objects,
realization maps and full proof are retained. -/

/-!
# Successive degeneracy unions are genuine simplicial pushouts -/
@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.BisimplicialRealization
variable (X : SimplicialObject SSet.{u})

/-- The inverse image of the preceding union under the next degeneracy is
exactly the preceding union one dimension lower. -/
theorem partialLatching_preimage_degeneracy (n k : ℕ) (hk : k < n + 2) :
    (partialLatching X (n + 1) k).preimage (X.σ ⟨k, hk⟩) = partialLatching X n k := by
  ext q x
  rw [SSet.Subcomplex.preimage_obj, Set.mem_preimage,
    mem_partialLatching_iff, mem_partialLatching_iff]
  let S : SSet.{u} := X ⋙ (evaluation _ _).obj q
  let K : Fin (n + 2) := ⟨k, hk⟩
  constructor
  · rintro ⟨i, hi, y, hy⟩
    have hin : i.val < n + 1 := by omega
    let j : Fin (n + 1) := ⟨i.val, hin⟩
    have hj : j.castSucc = i := Fin.ext rfl
    have hjk : j.castSucc < K := hi
    have h := congrArg (fun z ↦ S.δ K.succ z) hy
    change S.δ K.succ (S.σ i y) = S.δ K.succ (S.σ K x) at h
    rw [← hj, S.δ_comp_σ_of_gt_apply hjk, S.δ_comp_σ_succ_apply] at h
    exact ⟨j, hi, S.δ K y, h⟩
  · rintro ⟨i, hi, y, hy⟩
    have hk0 : 0 < k := by omega
    let j : Fin (n + 1) := ⟨k - 1, by omega⟩
    have hj : j.succ = K := by apply Fin.ext; dsimp [j, K]; omega
    have hij : i ≤ j := by change i.val ≤ k - 1; omega
    refine ⟨i.castSucc, hi, S.σ j y, ?_⟩
    change S.σ i.castSucc (S.σ j y) = S.σ K x
    rw [S.σ_comp_σ_apply hij, hj]
    exact congrArg (fun z ↦ S.σ K z) hy

/-- The common boundary in the next degeneracy attachment. -/
def lowerLatching : (n k : ℕ) → (X.obj (op ⦋n⦌)).Subcomplex
  | 0, _ => ⊥
  | n + 1, k => partialLatching X n k

lemma partialLatching_preimage (n k : ℕ) (hk : k < n + 1) :
    (partialLatching X n k).preimage (X.σ ⟨k, hk⟩) = lowerLatching X n k := by
  cases n with
  | zero =>
    have : k = 0 := by omega
    subst k
    ext q x
    simp [lowerLatching, partialLatching_zero, SSet.Subcomplex.preimage]
  | succ n => exact partialLatching_preimage_degeneracy X n k hk

/-- The characteristic map of the next degeneracy image. -/
def latchingCell (n k : ℕ) (hk : k < n + 1) :
    X.obj (op ⦋n⦌) ⟶ (partialLatching X n (k + 1) : SSet.{u}) :=
  SSet.Subcomplex.lift (X.σ ⟨k, hk⟩) (by
    rw [partialLatching_succ X n k hk]
    exact le_sup_right)

@[reassoc (attr := simp)] lemma latchingCell_ι (n k : ℕ) (hk : k < n + 1) :
    latchingCell X n k hk ≫ (partialLatching X n (k + 1)).ι = X.σ ⟨k, hk⟩ := rfl

/-- The attaching map from the lower-dimensional degeneracy union. -/
def latchingFace (n k : ℕ) (hk : k < n + 1) :
    (lowerLatching X n k : SSet.{u}) ⟶ (partialLatching X n k : SSet.{u}) :=
  (SSet.Subcomplex.eqToIso (partialLatching_preimage X n k hk).symm).hom ≫
    (partialLatching X n k).fromPreimage (X.σ ⟨k, hk⟩)

@[reassoc (attr := simp)] lemma latchingFace_ι (n k : ℕ) (hk : k < n + 1) :
    latchingFace X n k hk ≫ (partialLatching X n k).ι =
      (lowerLatching X n k).ι ≫ X.σ ⟨k, hk⟩ := rfl

/-- A partial latching object is obtained by an actual pushout along a mono. -/
theorem partialLatching_isPushout (n k : ℕ) (hk : k < n + 1) :
    IsPushout (latchingFace X n k hk) (lowerLatching X n k).ι
      (SSet.Subcomplex.homOfLE (partialLatching_mono X n (Nat.le_succ k)))
      (latchingCell X n k hk) where
  w := rfl
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun q ↦ by
    apply (isColimitMapCoconePushoutCoconeEquiv _ _).2
    apply IsPushout.isColimit
    apply Types.isPushout_of_isPullback_of_mono'
    · rw [Types.isPullback_iff]
      refine ⟨rfl, ?_, ?_⟩
      · intro x y h
        exact Subtype.ext h.2
      · intro x y h
        have hy : y ∈ (lowerLatching X n k).obj q := by
          rw [← partialLatching_preimage X n k hk]
          change (X.σ ⟨k, hk⟩).app q y ∈ (partialLatching X n k).obj q
          have he : x.val = (X.σ ⟨k, hk⟩).app q y := congrArg Subtype.val h
          exact he ▸ x.property
        refine ⟨⟨y, hy⟩, ?_, rfl⟩
        apply Subtype.ext
        exact (congrArg Subtype.val h).symm
    · apply Set.eq_univ_of_forall
      rintro ⟨x, hx⟩
      rw [partialLatching_succ X n k hk] at hx
      rcases hx with hx | ⟨y, hy⟩
      · exact Or.inl ⟨⟨x, hx⟩, Subtype.ext rfl⟩
      · exact Or.inr ⟨y, Subtype.ext hy⟩
    · intro x y _ _ h
      exact injective_of_mono ((X.σ ⟨k, hk⟩).app q) (congrArg Subtype.val h))⟩

end SSet.BisimplicialRealization
