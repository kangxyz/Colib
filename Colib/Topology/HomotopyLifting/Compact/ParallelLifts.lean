/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Compact.Stationary
public import Colib.Topology.HomotopyLifting.ParallelLifts

/-! # Compact-parameter coherent parallel-lift correction

The only lifting parameter is the product of the interval with the original
compact locally compact parameter. The entire zero set and actual
backtrack coherence are retained.


Implementation provenance:
`Quillen/Topology/HomotopyLifting/Compact/ParallelLifts.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
open unitInterval
namespace Topology
universe u
variable {X E B : Type u} [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace B]
    [CompactSpace X] [LocallyCompactSpace X]
    (q : C(E, B)) {a b c : C(X, E)} (H : a.Homotopy b) (K : a.Homotopy c)

/-- The endpoint comparison is vertical and fixed on the displayed zero set.
No continuous inverse family is an input or a chosen output. -/
theorem CompactHomotopyLiftingProperty.parallel_lifts_with_coherence
    (hq : CompactHomotopyLiftingProperty q)
    (hsame : ∀ t x, q (H (t, x)) = q (K (t, x)))
    (duration : C(X, unitInterval))
    (hH : ∀ x, duration x = 0 → ∀ t, H (t, x) = a x)
    (hK : ∀ x, duration x = 0 → ∀ t, K (t, x) = a x) :
    ∃ V : b.Homotopy c,
      HomotopyOver (q.comp b) q V ∧
      (∀ x,duration x = 0 → ∀ t,V (t,x) = a x) ∧
      ∃ S : (H.symm.trans K).toContinuousMap.Homotopy V.toContinuousMap,
        (∀ r t x,q (S (r,(t,x))) = q (H (σ (σ r * σ (TopCat.backtrackTime t)),x))) ∧
        (∀ r x,S (r,(0,x)) = b x) ∧ (∀ r x,S (r,(1,x)) = c x) ∧
        ∀ x,duration x = 0 → ∀ r t,S (r,(t,x)) = a x := by
  let J := H.symm.trans K
  let D : C(unitInterval × X,unitInterval) :=
    ⟨fun z ↦ (z.1 * σ z.1) * duration z.2,by fun_prop⟩
  let Q : C(unitInterval × (unitInterval × X),B) := {
    toFun z := q (H (σ (σ z.1 * σ (TopCat.backtrackTime z.2.1)),z.2.2))
    continuous_toFun := by fun_prop }
  have h₀ (z : unitInterval × X) : Q (0,z) = q (J z) := by
    change q (H (σ (σ 0 * σ (TopCat.backtrackTime z.1)),z.2)) = _
    simpa only [symm_zero,one_mul,symm_symm] using
      (parallelLifts_backtrack q H K hsame z.1 z.2).symm
  have hfixed (z : unitInterval × X) (hz : D z = 0) (s : unitInterval) :
      Q (s,z) = q (J z) := by
    rcases z with ⟨t,x⟩
    have hz' : t = 0 ∨ t = 1 ∨ duration x = 0 := by
      change (t * σ t) * duration x = 0 at hz
      simpa only [mul_eq_zero,symm_eq_zero,or_assoc] using hz
    rcases hz' with hz | hz | hz
    · change q (H (σ (σ s * σ (TopCat.backtrackTime t)),x)) = _
      rw [hz,TopCat.backtrackTime_zero,symm_one,mul_zero,symm_zero]
      exact (congrArg q (H.map_one_left x)).trans
        (congrArg q (J.map_zero_left x)).symm
    · change q (H (σ (σ s * σ (TopCat.backtrackTime t)),x)) = _
      rw [hz,TopCat.backtrackTime_one,symm_one,mul_zero,symm_zero]
      exact (hsame 1 x).trans
        ((congrArg q (K.map_one_left x)).trans (congrArg q (J.map_one_left x)).symm)
    · change q (H (_,x)) = q (J (t,x))
      rw [hH x hz]
      exact congrArg q (parallelLifts_fixed H K x (hH x hz) (hK x hz) t).symm
  obtain ⟨L,hL₀,hL,hLfixed⟩ := hq.lift_fixed_zero J.toContinuousMap Q h₀ D hfixed
  let V : b.Homotopy c := {
    toFun z := L (1,z)
    continuous_toFun := by fun_prop
    map_zero_left x := by
      have hh := hLfixed (0,x) (by simp [D]) 1
      exact hh.trans (J.map_zero_left x)
    map_one_left x := by
      have hh := hLfixed (1,x) (by simp [D]) 1
      exact hh.trans (J.map_one_left x) }
  refine ⟨V,?_,?_,?_⟩
  · intro t x
    change q (L (1,(t,x))) = q (b x)
    rw [hL]
    change q (H (σ (σ 1 * σ (TopCat.backtrackTime t)),x)) = _
    rw [symm_one,zero_mul,symm_zero]
    exact congrArg q (H.map_one_left x)
  · intro x hx t
    change L (1,(t,x)) = a x
    have hh := hLfixed (t,x) (by simp [D,hx]) 1
    exact hh.trans (parallelLifts_fixed H K x (hH x hx) (hK x hx) t)
  · let S : J.toContinuousMap.Homotopy V.toContinuousMap := {
      toContinuousMap := L
      map_zero_left := hL₀
      map_one_left := fun _ ↦ rfl }
    refine ⟨S,(fun r t x ↦ hL r (t,x)),?_,?_,?_⟩
    · intro r x
      exact (hLfixed (0,x) (by simp [D]) r).trans (J.map_zero_left x)
    · intro r x
      exact (hLfixed (1,x) (by simp [D]) r).trans (J.map_one_left x)
    · intro x hx r t
      exact (hLfixed (t,x) (by simp [D,hx]) r).trans
        (parallelLifts_fixed H K x (hH x hx) (hK x hx) t)

/-- The vertical endpoint comparison, with the entire prescribed zero set
fixed; the stronger theorem also records its full two-parameter coherence. -/
theorem CompactHomotopyLiftingProperty.parallel_lifts
    (hq : CompactHomotopyLiftingProperty q)
    (hsame : ∀ t x, q (H (t, x)) = q (K (t, x)))
    (duration : C(X, unitInterval))
    (hH : ∀ x, duration x = 0 → ∀ t, H (t, x) = a x)
    (hK : ∀ x, duration x = 0 → ∀ t, K (t, x) = a x) :
    ∃ V : b.Homotopy c,HomotopyOver (q.comp b) q V ∧
      ∀ x,duration x = 0 → ∀ t,V (t,x) = a x := by
  obtain ⟨V,hV,hfix,_⟩ := CompactHomotopyLiftingProperty.parallel_lifts_with_coherence
    q H K hq hsame duration hH hK
  exact ⟨V,hV,hfix⟩

end Topology
