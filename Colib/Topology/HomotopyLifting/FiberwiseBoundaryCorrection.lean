/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Stationary
public import Colib.Topology.Homotopy.BoundaryCorrection
public import Colib.Topology.Homotopy.Equiv.Fiberwise

/-! # Actual boundary-track correction over a fixed base

The original interval-square extension is corrected by a stationary lift.
Its duration vanishes on both path endpoints, the initial correction time,
and the whole prescribed boundary. Thus all original data survive.


Implementation provenance:
`Quillen/Topology/HomotopyLifting/FiberwiseBoundaryCorrection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
open unitInterval
universe u
namespace Topology
variable {A D : TopCat.{u}} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]

/-- Correct the prescribed boundary track, preserving the displayed base and
both endpoint maps everywhere in the ambient parameter space. -/
theorem correct_boundary_over_fixed_base
    (q : C(E, B)) (hq : HomotopyLiftingProperty q)
    (i : A ⟶ D) (hi : TopCat.HomotopyExtensionProperty i)
    (duration : C(D, unitInterval)) (hzero : ∀ x, duration x = 0 ↔ x ∈ Set.range i)
    (base : C(D, B)) {f g : C(D, E)} (K : f.Homotopy g)
    (hK : HomotopyOver base q K)
    (L : (f.comp i.hom).Homotopy (g.comp i.hom))
    (Q : (K.compContinuousMap i.hom).toContinuousMap.HomotopyRel L.toContinuousMap
      {z : unitInterval × A | z.1 = 0 ∨ z.1 = 1})
    (hQ : ∀ s t a, q (Q (s, (t, a))) = base (i a)) :
    ∃ K' : f.Homotopy g,HomotopyOver base q K' ∧ ∀ t a,K' (t,i a) = L (t,a) := by
  let F : C(D × unitInterval,E) := K.toContinuousMap.comp ContinuousMap.prodSwap
  let R : C((A × unitInterval) × unitInterval,E) :=
    ⟨fun z ↦ Q (z.2,(z.1.2,z.1.1)),by fun_prop⟩
  let R₀ : C(D × unitInterval,E) := f.comp ContinuousMap.fst
  let R₁ : C(D × unitInterval,E) := g.comp ContinuousMap.fst
  obtain ⟨S,hS,hSA,hS₀,hS₁⟩ := TopCat.homotopyExtensionProperty_interval_square_extension
    (Z := TopCat.of E) hi F R R₀ R₁ (fun a t ↦ Q.map_zero_left (t,a))
    (fun x ↦ (K.map_zero_left x).symm) (fun x ↦ (K.map_one_left x).symm)
    (fun a t ↦ (Q.prop t (0,a) (Or.inl rfl)).trans (K.map_zero_left (i a)))
    (fun a t ↦ (Q.prop t (1,a) (Or.inr rfl)).trans (K.map_one_left (i a)))
  let d : C((D × unitInterval) × unitInterval,unitInterval) :=
    ⟨fun z ↦ ((z.2 * z.1.2) * σ z.1.2) * duration z.1.1,by fun_prop⟩
  let P : C(unitInterval × ((D × unitInterval) × unitInterval),B) :=
    ⟨fun z ↦ q (S (z.2.1,σ z.1 * z.2.2)),by fun_prop⟩
  have hP₀ (z : (D × unitInterval) × unitInterval) : P (0,z) = q (S z) := by
    change q (S (z.1,σ 0 * z.2)) = q (S z)
    rw [symm_zero,one_mul]
  have hfixed (z : (D × unitInterval) × unitInterval) (hz : d z = 0) (r : unitInterval) :
      P (r,z) = q (S z) := by
    rcases z with ⟨⟨x,t⟩,s⟩
    have hz' : s = 0 ∨ t = 0 ∨ t = 1 ∨ duration x = 0 := by
      change ((s * t) * σ t) * duration x = 0 at hz
      simpa only [mul_eq_zero,symm_eq_zero,or_assoc] using hz
    rcases hz' with hs | ht | ht | hx
    · change q (S ((x,t),σ r * s)) = q (S ((x,t),s))
      rw [hs,mul_zero]
    · change q (S ((x,t),σ r * s)) = q (S ((x,t),s))
      rw [ht,hS₀,hS₀]
      rfl
    · change q (S ((x,t),σ r * s)) = q (S ((x,t),s))
      rw [ht,hS₁,hS₁]
      rfl
    · obtain ⟨a,rfl⟩ := (hzero x).mp hx
      change q (S ((i a,t),σ r * s)) = q (S ((i a,t),s))
      rw [hSA,hSA]
      exact (hQ _ t a).trans (hQ s t a).symm
  obtain ⟨M,_,hM,hMfixed⟩ := hq.lift_fixed_zero S P hP₀ d hfixed
  let K' : f.Homotopy g := {
    toFun z := M (1,((z.2,z.1),1))
    continuous_toFun := by fun_prop
    map_zero_left x :=
      (hMfixed ((x,0),1) (by simp [d]) 1).trans (hS₀ x 1)
    map_one_left x :=
      (hMfixed ((x,1),1) (by simp [d]) 1).trans (hS₁ x 1) }
  refine ⟨K',?_,?_⟩
  · intro t x
    change q (M (1,((x,t),1))) = base x
    rw [hM]
    change q (S ((x,t),σ 1 * 1)) = base x
    rw [symm_one,zero_mul,hS]
    exact hK t x
  · intro t a
    have hd : d ((i a,t),1) = 0 := by
      change ((1 * t) * σ t) * duration (i a) = 0
      rw [(hzero (i a)).mpr ⟨a,rfl⟩,mul_zero]
    exact (hMfixed ((i a,t),1) hd 1).trans ((hSA a t 1).trans (Q.map_one_left (t,a)))

/-- Remove the actual constant prefix on the boundary without changing the
base coordinate, either endpoint, or any prescribed boundary value. -/
theorem unpad_boundary_over_fixed_base
    (q : C(E, B)) (hq : HomotopyLiftingProperty q)
    (i : A ⟶ D) (hi : TopCat.HomotopyExtensionProperty i)
    (duration : C(D, unitInterval)) (hzero : ∀ x, duration x = 0 ↔ x ∈ Set.range i)
    (base : C(D, B)) {f g : C(D, E)} (K : f.Homotopy g) (hK : HomotopyOver base q K)
    (L : (f.comp i.hom).Homotopy (g.comp i.hom))
    (hL : ∀ t a, q (L (t, a)) = base (i a))
    (hKL : ∀ t a, K (t, i a) = Path.delayReflLeft 0 (L.evalAt a) t) :
    ∃ K' : f.Homotopy g,HomotopyOver base q K' ∧ ∀ t a,K' (t,i a) = L (t,a) := by
  let Q : (K.compContinuousMap i.hom).toContinuousMap.HomotopyRel L.toContinuousMap
      {z : unitInterval × A | z.1 = 0 ∨ z.1 = 1} := {
    toFun z := Path.delayReflLeft z.1 (L.evalAt z.2.2) z.2.1
    continuous_toFun := by
      change Continuous (fun z : unitInterval × (unitInterval × A) ↦
        L (σ (qRight (σ z.2.1,z.1)),z.2.2))
      fun_prop
    map_zero_left z := (hKL z.1 z.2).symm
    map_one_left z := by
      change Path.delayReflLeft 1 (L.evalAt z.2) z.1 = L (z.1,z.2)
      rw [Path.delayReflLeft_one]
      rfl
    prop' := by
      intro s z hz
      rcases z with ⟨t,a⟩
      rcases hz with ht | ht
      · change t = 0 at ht
        subst t
        exact (Path.source (Path.delayReflLeft s (L.evalAt a))).trans (K.map_zero_left (i a)).symm
      · change t = 1 at ht
        subst t
        exact (Path.target (Path.delayReflLeft s (L.evalAt a))).trans (K.map_one_left (i a)).symm }
  apply correct_boundary_over_fixed_base q hq i hi duration hzero base K hK L Q
  intro s t a
  change q (L (_,a)) = base (i a)
  exact hL _ a

end Topology
