/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Basic

/-!
# Weak covering-homotopy lifting

The initial point of a lift may be changed by a specified homotopy over the
unchanged base. This is the fiberwise-homotopy formulation of weak covering
homotopy lifting used in the homotopy-cartesian gluing argument. It is
preserved by fiberwise deformation domination. No local-to-global lifting
theorem is assumed here.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyLifting/Weak.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology

/-- The time slice of a continuous family. -/
def homotopyTimeSlice {A E : Type u} [TopologicalSpace A] [TopologicalSpace E]
    (H : C(I × A, E)) (t : I) : C(A, E) :=
  ⟨fun a ↦ H (t, a), H.continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- Weak covering-homotopy lifting, allowing a controlled initial homotopy
within each fixed fiber. -/
def WeakHomotopyLiftingProperty {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) : Prop :=
  ∀ (A : Type u) [TopologicalSpace A] (a : C(A, E)) (H : C(I × A, B)),
    (∀ x, H (0, x) = p (a x)) →
      ∃ L : C(I × A, E), (∀ t x, p (L (t, x)) = H (t, x)) ∧
        ∃ K : a.Homotopy (homotopyTimeSlice L 0), ∀ t x, p (K (t, x)) = p (a x)

/-- Strict covering-homotopy lifting gives weak covering-homotopy lifting
with a constant initial correction. -/
theorem HomotopyLiftingProperty.weak {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : HomotopyLiftingProperty p) : WeakHomotopyLiftingProperty p := by
  intro A _ a H hzero
  obtain ⟨L, hLzero, hL⟩ := hp A a H hzero
  have heq : a = homotopyTimeSlice L 0 := ContinuousMap.ext fun x ↦ (hLzero x).symm
  refine ⟨L, hL, ⟨(ContinuousMap.Homotopy.refl a).cast rfl heq, ?_⟩⟩
  intro t x
  rfl

/-- Fiberwise deformation domination transfers weak lifting. The maps,
retraction homotopy, and base equations are explicit; no homotopy-cartesian
conclusion appears among the assumptions. -/
theorem weakLifting_of_fiberwise_deformation
    {E E' B : Type u} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    (p : C(E, B)) (q : C(E', B)) (hq : WeakHomotopyLiftingProperty q)
    (i : C(E', E)) (r : C(E, E'))
    (hi : p.comp i = q) (hr : q.comp r = p)
    (R : (ContinuousMap.id E).Homotopy (i.comp r))
    (hR : ∀ t x, p (R (t, x)) = p x) : WeakHomotopyLiftingProperty p := by
  intro A _ a H hzero
  have hz : ∀ x, H (0, x) = q ((r.comp a) x) := by
    intro x
    exact (hzero x).trans (ContinuousMap.congr_fun hr (a x)).symm
  obtain ⟨L, hL, K, hK⟩ := hq A (r.comp a) H hz
  let L' := i.comp L
  have hL' : ∀ t x, p (L' (t, x)) = H (t, x) := by
    intro t x
    exact (ContinuousMap.congr_fun hi (L (t, x))).trans (hL t x)
  let R' : a.Homotopy ((i.comp r).comp a) := R.compContinuousMap a
  let K' : ((i.comp r).comp a).Homotopy (homotopyTimeSlice L' 0) :=
    ((ContinuousMap.Homotopy.refl i).comp K).cast rfl rfl
  refine ⟨L', hL', ⟨R'.trans K', ?_⟩⟩
  intro t x
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hR _ (a x)
  · exact (ContinuousMap.congr_fun hi _).trans
      ((hK _ x).trans (ContinuousMap.congr_fun hr (a x)))

end Topology
