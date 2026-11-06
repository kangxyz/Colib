/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Stationary

/-! # Compact-parameter homotopy lifting and stationary correction

Only actual compact, locally compact parameter spaces are quantified over.
This property does not supply a lift on an arbitrary mapping-path space or
a continuous inverse on an entire homotopy fiber.


Implementation provenance:
`Quillen/Topology/HomotopyLifting/Compact/Stationary.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
universe u
namespace Topology
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]

/-- Covering homotopy lifting for compact locally compact parameter spaces. -/
def CompactHomotopyLiftingProperty (p : C(E, B)) : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [LocallyCompactSpace X]
    (a : C(X,E)) (H : C(unitInterval × X,B)),
    (∀ x,H (0,x) = p (a x)) →
      ∃ L : C(unitInterval × X,E),
        (∀ x,L (0,x) = a x) ∧ ∀ t x,p (L (t,x)) = H (t,x)

/-- Genuine covering homotopy lifting has the stated restricted scope. -/
theorem HomotopyLiftingProperty.compact {p : C(E, B)} (hp : HomotopyLiftingProperty p) :
    CompactHomotopyLiftingProperty p := fun X _ _ _ a H h₀ ↦ hp X a H h₀

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [LocallyCompactSpace X]

/-- Compact-parameter lifting supplies a lift fixed on the zero set of the displayed
continuous duration when the original base homotopy is stationary there. -/
theorem CompactHomotopyLiftingProperty.lift_fixed_zero
    {p : C(E, B)} (hp : CompactHomotopyLiftingProperty p)
    (a : C(X, E)) (H : C(unitInterval × X, B))
    (h₀ : ∀ x, H (0, x) = p (a x)) (duration : C(X, unitInterval))
    (hfixed : ∀ x, duration x = 0 → ∀ t, H (t, x) = p (a x)) :
    ∃ L : C(unitInterval × X,E),
      (∀ x,L (0,x) = a x) ∧
      (∀ t x,p (L (t,x)) = H (t,x)) ∧
      ∀ x,duration x = 0 → ∀ t,L (t,x) = a x := by
  have hH : ∀ x,duration x = 0 → ∀ t,H (t,x) = H (0,x) :=
    fun x hx t ↦ (hfixed x hx t).trans (h₀ x).symm
  obtain ⟨Q,hQ₀,hQ⟩ := hp X a (acceleratedHomotopy H duration hH) (by
    intro x
    exact (acceleratedHomotopy_zero H duration hH x).trans (h₀ x))
  let L : C(unitInterval × X,E) := ⟨fun z ↦ Q (z.1 * duration z.2,z.2),by fun_prop⟩
  refine ⟨L,?_,?_,?_⟩
  · intro x
    change Q (0 * duration x,x) = a x
    rw [zero_mul,hQ₀]
  · intro t x
    change p (Q (t * duration x,x)) = _
    rw [hQ,acceleratedHomotopy_mul]
  · intro x hx t
    change Q (t * duration x,x) = a x
    rw [hx,mul_zero,hQ₀]

/-- The terminal corrected map has the displayed base coordinate exactly,
and retains all prescribed zero-set values. The whole correction homotopy
is included, not merely its endpoint. -/
theorem CompactHomotopyLiftingProperty.correct_over_fixed_zero
    {p : C(E, B)} (hp : CompactHomotopyLiftingProperty p)
    (a : C(X, E)) (b : C(X, B)) (H : (p.comp a).Homotopy b)
    (duration : C(X, unitInterval))
    (hfixed : ∀ x, duration x = 0 → ∀ t, H (t, x) = p (a x)) :
    ∃ c : C(X,E),p.comp c = b ∧
      (∀ x,duration x = 0 → c x = a x) ∧
      ∃ K : a.Homotopy c,
        (∀ t x,p (K (t,x)) = H (t,x)) ∧
        ∀ x,duration x = 0 → ∀ t,K (t,x) = a x := by
  obtain ⟨L,hL₀,hL,hfix⟩ := hp.lift_fixed_zero a H.toContinuousMap H.map_zero_left duration hfixed
  let c : C(X,E) := ⟨fun x ↦ L (1,x),by fun_prop⟩
  let K : a.Homotopy c :=
    { toContinuousMap := L, map_zero_left := hL₀, map_one_left := fun _ ↦ rfl }
  refine ⟨c,?_,fun x hx ↦ hfix x hx 1,K,hL,hfix⟩
  ext x
  exact (hL 1 x).trans (H.map_one_left x)

end Topology
