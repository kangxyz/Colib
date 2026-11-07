/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! Implementation provenance: adapted from
`Quillen/Topology/Realization/BisimplicialLatching.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native simplicial objects,
realization maps and full proof are retained. -/

/-!
# Outer latching subcomplexes of a bisimplicial set -/
@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.BisimplicialRealization

variable (X : SimplicialObject SSet.{u})

/-- The union of the first `k` outer degeneracy images in degree `n+1`. -/
def partialLatching (n k : ℕ) : (X.obj (op ⦋n + 1⦌)).Subcomplex :=
  ⨆ (i : Fin (n + 1)) (_ : i.val < k), SSet.Subcomplex.range (X.σ i)

/-- The full outer latching subcomplex, including the empty degree-zero case. -/
def latching : (n : ℕ) → (X.obj (op ⦋n⦌)).Subcomplex
  | 0 => ⊥
  | n + 1 => partialLatching X n (n + 1)

lemma mem_partialLatching_iff (n k : ℕ) (q : SimplexCategoryᵒᵖ)
    (x : (X.obj (op ⦋n + 1⦌)).obj q) :
    x ∈ (partialLatching X n k).obj q ↔
      ∃ (i : Fin (n + 1)) (_ : i.val < k) (y : (X.obj (op ⦋n⦌)).obj q),
        (X.σ i).app q y = x := by
  simp [partialLatching, Subfunctor.iSup_obj, Subfunctor.range_obj]

@[simp] lemma partialLatching_zero (n : ℕ) : partialLatching X n 0 = ⊥ := by
  simp [partialLatching]

@[simp] lemma latching_zero : latching X 0 = ⊥ := rfl

lemma mem_latching_iff_degenerate (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (x : (X.obj (op ⦋n⦌)).obj q) :
    x ∈ (latching X n).obj q ↔
      x ∈ SSet.degenerate (X ⋙ (evaluation _ _).obj q) n := by
  cases n with
  | zero => simp [latching]
  | succ n =>
    rw [SSet.degenerate_eq_iUnion_range_σ]
    change x ∈ (partialLatching X n (n + 1)).obj q ↔ _
    simp only [mem_partialLatching_iff, Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨i, _, y, hy⟩
      exact ⟨i, y, hy⟩
    · rintro ⟨i, y, hy⟩
      exact ⟨i, i.isLt, y, hy⟩

lemma partialLatching_mono (n : ℕ) {k l : ℕ} (h : k ≤ l) :
    partialLatching X n k ≤ partialLatching X n l := by
  intro q x hx
  obtain ⟨i, hi, y, hy⟩ := (mem_partialLatching_iff X n k q x).1 hx
  exact (mem_partialLatching_iff X n l q x).2 ⟨i, hi.trans_le h, y, hy⟩

lemma partialLatching_succ (n k : ℕ) (hk : k < n + 1) :
    partialLatching X n (k + 1) =
      partialLatching X n k ⊔ SSet.Subcomplex.range (X.σ ⟨k, hk⟩) := by
  ext q x
  simp only [mem_partialLatching_iff, Subfunctor.max_obj, Set.mem_union,
    Subfunctor.range_obj, Set.mem_range]
  constructor
  · rintro ⟨i, hi, y, hy⟩
    obtain hil | hie := (Nat.le_of_lt_succ hi).lt_or_eq
    · exact Or.inl ⟨i, hil, y, hy⟩
    · have he : i = ⟨k, hk⟩ := Fin.ext hie
      subst i
      exact Or.inr ⟨y, hy⟩
  · rintro (⟨i, hi, y, hy⟩ | ⟨y, hy⟩)
    · exact ⟨i, Nat.lt_succ_of_lt hi, y, hy⟩
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, y, hy⟩

instance outerDegeneracy_mono {n : ℕ} (i : Fin (n + 1)) : Mono (X.σ i) :=
  mono_of_mono_fac (X.δ_comp_σ_self (i := i))

variable {X} {Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)

lemma map_mem_partialLatching (n k : ℕ) (q : SimplexCategoryᵒᵖ)
    (x : (X.obj (op ⦋n + 1⦌)).obj q) (hx : x ∈ (partialLatching X n k).obj q) :
    (η.app (op ⦋n + 1⦌)).app q x ∈ (partialLatching Y n k).obj q := by
  obtain ⟨i, hi, y, rfl⟩ := (mem_partialLatching_iff X n k q x).1 hx
  refine (mem_partialLatching_iff Y n k q _).2 ⟨i, hi, (η.app (op ⦋n⦌)).app q y, ?_⟩
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app (SimplicialObject.σ_naturality η i) q)
    y).symm

/-- The map on partial latching objects induced by any bisimplicial map. -/
def partialLatchingMap (n k : ℕ) :
    (partialLatching X n k : SSet.{u}) ⟶ (partialLatching Y n k : SSet.{u}) where
  app q := ↾fun x ↦ ⟨(η.app _).app q x.1, map_mem_partialLatching η n k q x.1 x.2⟩
  naturality p q f := by
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((η.app _).naturality f) x.1

@[reassoc (attr := simp)] lemma partialLatchingMap_ι (n k : ℕ) :
    partialLatchingMap η n k ≫ (partialLatching Y n k).ι =
      (partialLatching X n k).ι ≫ η.app (op ⦋n + 1⦌) := rfl

/-- The natural full latching map. -/
def latchingMap (n : ℕ) : (latching X n : SSet.{u}) ⟶ (latching Y n : SSet.{u}) := by
  cases n with
  | zero => exact (SSet.Subcomplex.isInitialBot).to _
  | succ n => exact partialLatchingMap η n (n + 1)

@[reassoc (attr := simp)] lemma latchingMap_ι (n : ℕ) :
    latchingMap η n ≫ (latching Y n).ι = (latching X n).ι ≫ η.app (op ⦋n⦌) := by
  cases n with
  | zero => apply (SSet.Subcomplex.isInitialBot).hom_ext
  | succ n => rfl

end SSet.BisimplicialRealization
