/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Locally stationary homotopies

A locally stationary sequence of maps has a continuous eventual value.  A
sequence of homotopies that is locally stationary on the source admits an
actual infinite concatenation: right-associated finite concatenations use
successive dyadic time intervals, and become locally equal on the whole
cylinder.  This proves continuity also at their accumulating endpoint.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/Homotopy/LocallyStationary.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u

namespace Topology

variable {S E B : Type u} [TopologicalSpace S] [TopologicalSpace E]
  [TopologicalSpace B]

/-- The sequence is eventually constant with one bound on a neighborhood of
each source point.  No separation condition on the target is required. -/
def LocallyStationary (f : ℕ → S → E) : Prop :=
  ∀ x, ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
    ∃ N : ℕ, ∀ y ∈ U, ∀ n, N ≤ n → f n y = f N y

namespace LocallyStationary

variable {f : ℕ → S → E}

omit [TopologicalSpace E] in
theorem pointwise (h : LocallyStationary f) (x : S) :
    ∃ N : ℕ, ∀ n, N ≤ n → f n x = f N x := by
  obtain ⟨U, _, hx, N, hN⟩ := h x
  exact ⟨N, hN x hx⟩

/-- The eventual value, chosen using a pointwise stabilization index. -/
def value (h : LocallyStationary f) (x : S) : E :=
  f (h.pointwise x).choose x

omit [TopologicalSpace E] in
/-- Any valid stabilization index computes the chosen eventual value. -/
theorem value_eq (h : LocallyStationary f) {x : S} {N : ℕ}
    (hN : ∀ n, N ≤ n → f n x = f N x) : h.value x = f N x := by
  let M := (h.pointwise x).choose
  have hM : ∀ n, M ≤ n → f n x = f M x := (h.pointwise x).choose_spec
  exact (hM (max M N) (le_max_left _ _)).symm.trans
    (hN (max M N) (le_max_right _ _))

/-- Local stationarity suffices for continuity of the eventual value. -/
theorem continuous_value (h : LocallyStationary f) (hf : ∀ n, Continuous (f n)) :
    Continuous h.value := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨U, hU, hx, N, hN⟩ := h x
  have heq : h.value =ᶠ[𝓝 x] f N := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact h.value_eq (hN y hy)
  exact (hf N).continuousAt.congr heq.symm

/-- The eventual-value continuous map. -/
def continuousMap (h : LocallyStationary f) (hf : ∀ n, Continuous (f n)) : C(S, E) :=
  ⟨h.value, h.continuous_value hf⟩

omit [TopologicalSpace E] in
/-- Every pointwise invariant of every stage holds for the eventual value. -/
theorem value_property (h : LocallyStationary f) (P : S → E → Prop)
    (hP : ∀ n x, P x (f n x)) (x : S) : P x (h.value x) :=
  hP _ x

omit [TopologicalSpace E] in
/-- A property holding at all sufficiently late stages holds at the limit.
The property need not be closed, and the index may depend on the point. -/
theorem value_property_of_eventually (h : LocallyStationary f) {x : S}
    (P : E → Prop) (hP : ∃ N, ∀ n, N ≤ n → P (f n x)) : P (h.value x) := by
  obtain ⟨N, hN⟩ := hP
  obtain ⟨M, hM⟩ := h.pointwise x
  rw [h.value_eq hM, ← hM (max M N) (le_max_left _ _)]
  exact hN _ (le_max_right _ _)

omit [TopologicalSpace B] [TopologicalSpace E] in
/-- A common projection is preserved by taking the eventual value. -/
theorem value_comp (h : LocallyStationary f) (p : E → B) (g : S → B)
    (hp : ∀ n x, p (f n x) = g x) (x : S) : p (h.value x) = g x :=
  hp _ x

end LocallyStationary

/-- Homotopies are stationary after a uniform index on a neighborhood of
each source point, throughout their entire time interval. -/
def LocallyStationaryHomotopies (f : ℕ → C(S, E))
    (H : ∀ n, (f n).Homotopy (f (n + 1))) : Prop :=
  ∀ x, ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
    ∃ N : ℕ, ∀ y ∈ U, ∀ n, N ≤ n → ∀ t : I, H n (t, y) = f N y

namespace LocallyStationaryHomotopies

variable {f : ℕ → C(S, E)} {H : ∀ n, (f n).Homotopy (f (n + 1))}

/-- Stationarity of whole homotopies implies stationarity of their endpoints. -/
theorem maps (h : LocallyStationaryHomotopies f H) :
    LocallyStationary (fun n x ↦ f n x) := by
  intro x
  obtain ⟨U, hU, hx, N, hN⟩ := h x
  refine ⟨U, hU, hx, N, ?_⟩
  intro y hy n hn
  simpa using hN y hy n hn 0

/-- The continuous eventual endpoint of the locally stationary homotopies. -/
def limit (h : LocallyStationaryHomotopies f H) : C(S, E) :=
  h.maps.continuousMap (fun n ↦ (f n).continuous)

theorem limit_eq (h : LocallyStationaryHomotopies f H) {x : S} {N : ℕ}
    (hN : ∀ n, N ≤ n → f n x = f N x) : h.limit x = f N x :=
  h.maps.value_eq hN

/-- A finite right-associated concatenation.  The initial homotopy uses
`[0, 1/2]`, the next uses `[1/2, 3/4]`, and the last endpoint is held fixed. -/
def finiteConcat (H : ∀ n, (f n).Homotopy (f (n + 1))) :
    (m n : ℕ) → (f m).Homotopy (f (m + n))
  | m, 0 => (ContinuousMap.Homotopy.refl (f m)).cast rfl (by simp)
  | m, n + 1 => ((H m).trans (finiteConcat H (m + 1) n)).cast rfl
      (by congr 1; omega)

@[simp]
theorem finiteConcat_zero_apply (m : ℕ) (z : I × S) :
    finiteConcat H m 0 z = f m z.2 := rfl

theorem finiteConcat_succ_apply (m n : ℕ) (z : I × S) :
    finiteConcat H m (n + 1) z = ((H m).trans (finiteConcat H (m + 1) n)) z := rfl

/-- A finite concatenation consisting of constant homotopies is constant. -/
theorem finiteConcat_eq_of_constant {x : S} {e : E} {m : ℕ}
    (hm : ∀ j, m ≤ j → ∀ t : I, H j (t, x) = e) (n : ℕ) (t : I) :
    finiteConcat H m n (t, x) = e := by
  induction n generalizing m t with
  | zero => simpa using hm m le_rfl 0
  | succ n ih =>
    rw [finiteConcat_succ_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · exact hm m le_rfl _
    · exact ih (fun j hj ↦ hm j (by omega)) _

/-- Adding a constant tail does not change a right-associated concatenation. -/
theorem finiteConcat_add_eq {x : S} {e : E} (m n k : ℕ)
    (hn : ∀ j, m + n ≤ j → ∀ t : I, H j (t, x) = e) (t : I) :
    finiteConcat H m (n + k) (t, x) = finiteConcat H m n (t, x) := by
  induction n generalizing m t with
  | zero =>
    have hm : ∀ j, m ≤ j → ∀ t : I, H j (t, x) = e := by simpa using hn
    rw [Nat.zero_add]
    exact (finiteConcat_eq_of_constant hm k t).trans
      (finiteConcat_eq_of_constant hm 0 t).symm
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega,
      finiteConcat_succ_apply, finiteConcat_succ_apply,
      ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · rfl
    · exact ih (m + 1) (fun j hj ↦ hn j (by omega)) _

/-- The entire finite homotopies are locally stationary on the cylinder. -/
theorem finiteConcat_locallyStationary (h : LocallyStationaryHomotopies f H) :
    LocallyStationary (fun n (z : I × S) ↦ finiteConcat H 0 n z) := by
  intro z
  obtain ⟨U, hU, hz, N, hN⟩ := h z.2
  refine ⟨Prod.snd ⁻¹' U, hU.preimage continuous_snd, hz, N, ?_⟩
  intro y hy n hn
  have heq := finiteConcat_add_eq (H := H) 0 N (n - N)
    (fun j hj ↦ hN y.2 hy j (by omega)) y.1
  have hi : N + (n - N) = n := Nat.add_sub_of_le hn
  exact (congrArg (fun k ↦ finiteConcat H 0 k y) hi).symm.trans heq

/-- The infinite concatenation of a locally stationary homotopy sequence.
The finite approximants put successive homotopies in the dyadic intervals
approaching one; local stationarity makes their eventual value continuous
on the whole cylinder, including time one. -/
def homotopy (h : LocallyStationaryHomotopies f H) : (f 0).Homotopy h.limit where
  toContinuousMap := h.finiteConcat_locallyStationary.continuousMap
    (fun n ↦ (finiteConcat H 0 n).continuous)
  map_zero_left x := by
    exact h.finiteConcat_locallyStationary.value_property
      (fun z e ↦ z.1 = 0 → e = f 0 z.2)
      (fun n z hz ↦ by rcases z with ⟨t, y⟩; dsimp at hz; subst t; simp) (0, x) rfl
  map_one_left x := by
    obtain ⟨U, _, hx, N, hN⟩ := h x
    have hm : ∀ n, N ≤ n → f n x = f N x := by
      intro n hn
      simpa using hN x hx n hn 0
    change h.finiteConcat_locallyStationary.value (1, x) = h.limit x
    rw [h.finiteConcat_locallyStationary.value_eq (N := N)]
    · simpa using (h.limit_eq hm).symm
    · intro n hn
      simpa using hm n hn

/-- Every property preserved throughout every given homotopy is preserved
throughout each finite concatenation. -/
theorem finiteConcat_property (P : S → E → Prop)
    (hP : ∀ n (t : I) x, P x (H n (t, x))) (m n : ℕ) (t : I) (x : S) :
    P x (finiteConcat H m n (t, x)) := by
  induction n generalizing m t with
  | zero => simpa using hP m 0 x
  | succ n ih =>
    rw [finiteConcat_succ_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · exact hP m _ x
    · exact ih (m + 1) _

/-- The infinite concatenation preserves pointwise invariants, without
requiring the invariant subsets to be closed. -/
theorem homotopy_property (h : LocallyStationaryHomotopies f H)
    (P : S → E → Prop) (hP : ∀ n (t : I) x, P x (H n (t, x)))
    (t : I) (x : S) : P x (h.homotopy (t, x)) :=
  h.finiteConcat_locallyStationary.value_property (fun z e ↦ P z.2 e)
    (fun n z ↦ finiteConcat_property P hP 0 n z.1 z.2) (t, x)

omit [TopologicalSpace B] in
/-- A common projection is preserved throughout the infinite concatenation. -/
theorem homotopy_comp (h : LocallyStationaryHomotopies f H)
    (p : E → B) (g : S → B) (hp : ∀ n (t : I) x, p (H n (t, x)) = g x)
    (t : I) (x : S) : p (h.homotopy (t, x)) = g x :=
  h.homotopy_property (fun x e ↦ p e = g x) hp t x

/-- The terminal value satisfies every property eventually satisfied by the
endpoints.  The stage at which it holds may depend on the source point. -/
theorem limit_property_of_eventually (h : LocallyStationaryHomotopies f H)
    {x : S} (P : E → Prop) (hP : ∃ N, ∀ n, N ≤ n → P (f n x)) :
    P (h.limit x) :=
  h.maps.value_property_of_eventually P hP

omit [TopologicalSpace B] in
/-- In particular, an eventual prescribed projection becomes exact at time one. -/
theorem limit_comp_of_eventually (h : LocallyStationaryHomotopies f H)
    (p : E → B) (g : S → B)
    (hp : ∀ x, ∃ N, ∀ n, N ≤ n → p (f n x) = g x) (x : S) :
    p (h.limit x) = g x :=
  h.limit_property_of_eventually (fun e ↦ p e = g x) (hp x)

/-- Pointwise stationarity from a specified index computes the entire
infinite homotopy by one finite concatenation. -/
theorem homotopy_eq_finiteConcat (h : LocallyStationaryHomotopies f H)
    {x : S} {N : ℕ}
    (hN : ∀ n, N ≤ n → ∀ t : I, H n (t, x) = f N x) (t : I) :
    h.homotopy (t, x) = finiteConcat H 0 N (t, x) := by
  apply h.finiteConcat_locallyStationary.value_eq
  intro n hn
  have heq := finiteConcat_add_eq (H := H) 0 N (n - N)
    (fun j hj ↦ hN j (by omega)) t
  exact (congrArg (fun k ↦ finiteConcat H 0 k (t, x))
    (Nat.add_sub_of_le hn)).symm.trans heq

end LocallyStationaryHomotopies

end Topology
