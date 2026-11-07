/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Compact.ParallelLifts

/-! # Compact original comparison homotopies corrected over the base

Only compact locally compact parameters and their interval products are used.
The first actual lift restores the displayed base map while fixing the zero
set. Parallel-lift straightening then supplies a coherent vertical comparison,
retaining that entire set. No ordinary homotopy is presumed to be fiberwise.


Implementation provenance:
`Quillen/Topology/HomotopyLifting/Compact/OverBaseCorrection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
universe u
namespace Topology
variable {E F B X : Type u} [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace B] [TopologicalSpace X] [CompactSpace X] [LocallyCompactSpace X]

/-- Correct an actual ordinary comparison to the displayed base map, with a
vertical comparison homotopy and every prescribed zero-set value retained. -/
theorem compact_correct_comparison_over_fixed_zero
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (hp : CompactHomotopyLiftingProperty p) (hq : CompactHomotopyLiftingProperty q)
    (a : C(X, E)) (b : C(X, F)) (H : (f.comp a).Homotopy b)
    (duration : C(X, unitInterval))
    (hfixed : ∀ x, duration x = 0 → ∀ t, H (t, x) = f (a x)) :
    ∃ c : C(X,E),p.comp c = q.comp b ∧
      (∀ x,duration x = 0 → c x = a x) ∧
      ∃ V : (f.comp c).Homotopy b,
        HomotopyOver (q.comp b) q V ∧
        ∀ x,duration x = 0 → ∀ t,V (t,x) = f (a x) := by
  have hsq (e : E) : q (f e) = p e := ContinuousMap.congr_fun sq e
  let Hb : (p.comp a).Homotopy (q.comp b) :=
    ((ContinuousMap.Homotopy.refl q).comp H).cast (by rw [← sq]; rfl) rfl
  have hbfixed : ∀ x,duration x = 0 → ∀ t,Hb (t,x) = p (a x) := by
    intro x hx t
    change q (H (t,x)) = p (a x)
    rw [hfixed x hx t,hsq]
  obtain ⟨c,hc,hca,K,hK,hKfixed⟩ := hp.correct_over_fixed_zero a (q.comp b) Hb duration hbfixed
  let J : (f.comp a).Homotopy (f.comp c) := (ContinuousMap.Homotopy.refl f).comp K
  have hsame : ∀ t x,q (J (t,x)) = q (H (t,x)) := by
    intro t x
    change q (f (K (t,x))) = q (H (t,x))
    rw [hsq]
    exact hK t x
  have hJfixed : ∀ x,duration x = 0 → ∀ t,J (t,x) = (f.comp a) x := by
    intro x hx t
    change f (K (t,x)) = f (a x)
    rw [hKfixed x hx t]
  obtain ⟨V,hV,hVfixed⟩ := CompactHomotopyLiftingProperty.parallel_lifts q J H hq hsame duration
    hJfixed hfixed
  refine ⟨c,hc,hca,V,?_,hVfixed⟩
  intro t x
  exact (hV t x).trans ((hsq (c x)).trans (ContinuousMap.congr_fun hc x))

end Topology
