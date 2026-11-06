/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Stationary
public import Colib.Topology.DeformationRetract.Cofibration

/-! # Actual homotopy extension over a fixed base

Ordinary HEP extends the prescribed homotopy first. Stationary HLP then
corrects its projection by reversing its time coordinate. The correction
fixes both time zero and the entire prescribed subspace.


Implementation provenance:
`Quillen/Topology/HomotopyLifting/FiberwiseExtension.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
open scoped Topology unitInterval
open unitInterval
universe u
namespace Topology
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]

theorem HomotopyLiftingProperty.extend_over_fixed_base
    {q : C(E, B)} (hq : HomotopyLiftingProperty q)
    (A D : TopCat.{u}) (i : A ⟶ D) (hi : TopCat.HomotopyExtensionProperty i)
    (duration : C(D, unitInterval)) (hzero : ∀ x, duration x = 0 ↔ x ∈ Set.range i)
    (b : C(D, E)) (H : C(unitInterval × A, E))
    (h₀ : ∀ a, H (0, a) = b (i a))
    (hbase : ∀ t a, q (H (t, a)) = q (b (i a))) :
    ∃ T : C(unitInterval × D,E),
      (∀ x,T (0,x) = b x) ∧ (∀ t a,T (t,i a) = H (t,a)) ∧
      ∀ t x,q (T (t,x)) = q (b x) := by
  obtain ⟨Q,hQ₀,hQA⟩ := TopCat.homotopyExtensionProperty_continuous hi
    (TopCat.of E) b H h₀
  let d : C(unitInterval × D,unitInterval) := ⟨fun z ↦ z.1 * duration z.2,by fun_prop⟩
  let P : C(unitInterval × (unitInterval × D),B) :=
    ⟨fun z ↦ q (Q (σ z.1 * z.2.1,z.2.2)),by fun_prop⟩
  have hP₀ (z : unitInterval × D) : P (0,z) = q (Q z) := by
    change q (Q (σ 0 * z.1,z.2)) = q (Q z)
    rw [symm_zero,one_mul]
  have hfixed (z : unitInterval × D) (hz : d z = 0) (s : unitInterval) :
      P (s,z) = q (Q z) := by
    rcases z with ⟨t,x⟩
    have hz' : t = 0 ∨ duration x = 0 := mul_eq_zero.mp hz
    rcases hz' with ht | hx
    · change q (Q (σ s * t,x)) = q (Q (t,x))
      rw [ht,mul_zero]
    · obtain ⟨a,rfl⟩ := (hzero x).mp hx
      change q (Q (σ s * t,i a)) = q (Q (t,i a))
      rw [hQA,hQA,hbase,hbase]
  obtain ⟨L,_,hL,hLfixed⟩ := hq.lift_fixed_zero Q P hP₀ d hfixed
  let T : C(unitInterval × D,E) := ⟨fun z ↦ L (1,z),by fun_prop⟩
  refine ⟨T,?_,?_,?_⟩
  · intro x
    exact (hLfixed (0,x) (by simp [d]) 1).trans (hQ₀ x)
  · intro t a
    have hd : d (t,i a) = 0 := by
      change t * duration (i a) = 0
      rw [(hzero (i a)).mpr ⟨a,rfl⟩,mul_zero]
    exact (hLfixed (t,i a) hd 1).trans (hQA t a)
  · intro t x
    change q (L (1,(t,x))) = q (b x)
    rw [hL]
    change q (Q (σ 1 * t,x)) = q (b x)
    rw [symm_one,zero_mul,hQ₀]

end Topology
