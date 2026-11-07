/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.PausedHomotopy

/-!
# Continuous cutoff extension of local lifting families

A local lifting family with exact initial values extends globally after
multiplication by a cutoff supported within its open domain. Outside the
cutoff region the family is exactly stationary. This is the elementary
gluing operation used in the two-collar construction.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyLifting/Collar/Cutoff.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology

variable {Z E : Type u} [TopologicalSpace Z] [TopologicalSpace E]

/-- The two cylinder domains form an open neighborhood cover. -/
theorem cutoffLift_cover (U V : Set Z) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    ∀ z : I × Z, ∃ b : Bool,
      (if b then Prod.snd ⁻¹' U else Prod.snd ⁻¹' V) ∈ nhds z := by
  intro z
  have hz : z.2 ∈ U ∪ V := by rw [hcover]; trivial
  rcases hz with hz | hz
  · exact ⟨true, (hU.preimage continuous_snd).mem_nhds hz⟩
  · exact ⟨false, (hV.preimage continuous_snd).mem_nhds hz⟩

/-- Extend a local time-dependent map using an open cutoff domain. -/
def cutoffLift (U V : Set Z) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (c : C(Z, I)) (hc : ∀ z ∈ V, c z = 0)
    (a : C(Z, E)) (M : C(I × U, E)) (hM : ∀ z : U, M (0, z) = a z.1) :
    C(I × Z, E) := by
  let S : Bool → Set (I × Z) := fun b ↦ if b then Prod.snd ⁻¹' U else Prod.snd ⁻¹' V
  let f : (b : Bool) → C(S b, E) := fun b ↦ if h : b then
    ⟨fun z ↦ M (z.1.1 * c z.1.2, ⟨z.1.2, by simpa [S, h] using z.2⟩), by fun_prop⟩
    else ⟨fun z ↦ a z.1.2, by fun_prop⟩
  have hagree : ∀ (i j : Bool) (z : I × Z) (hi : z ∈ S i) (hj : z ∈ S j),
      f i ⟨z, hi⟩ = f j ⟨z, hj⟩ := by
    intro i j z hi hj
    cases i <;> cases j
    · rfl
    · have hz : z.2 ∈ V := by simpa [S] using hi
      simp only [f, Bool.false_eq_true, ↓reduceDIte, ContinuousMap.coe_mk, hc _ hz, mul_zero]
      exact (hM ⟨z.2, by simpa [S] using hj⟩).symm
    · have hz : z.2 ∈ V := by simpa [S] using hj
      simp only [f, Bool.false_eq_true, ↓reduceDIte, ContinuousMap.coe_mk, hc _ hz, mul_zero]
      exact hM ⟨z.2, by simpa [S] using hi⟩
    · rfl
  have hS : ∀ z : I × Z, ∃ b, S b ∈ nhds z := by
    intro z
    have hz : z.2 ∈ U ∪ V := by rw [hcover]; trivial
    rcases hz with hz | hz
    · exact ⟨true, (hU.preimage continuous_snd).mem_nhds hz⟩
    · exact ⟨false, (hV.preimage continuous_snd).mem_nhds hz⟩
  exact ContinuousMap.liftCover S f hagree hS

variable (U V : Set Z) (hU : IsOpen U) (hV : IsOpen V)
  (hcover : U ∪ V = Set.univ) (c : C(Z, I)) (hc : ∀ z ∈ V, c z = 0)
  (a : C(Z, E)) (M : C(I × U, E)) (hM : ∀ z : U, M (0, z) = a z.1)

/-- On its local domain, the extension is the cutoff-rescaled local family. -/
theorem cutoffLift_apply_of_mem (r : I) (z : Z) (hz : z ∈ U) :
    cutoffLift U V hU hV hcover c hc a M hM (r, z) = M (r * c z, ⟨z, hz⟩) :=
  ContinuousMap.liftCover_coe (hS := cutoffLift_cover U V hU hV hcover) (i := true) ⟨(r, z), hz⟩

/-- On the complementary open set the extension is exactly stationary. -/
theorem cutoffLift_apply_of_mem_complement (r : I) (z : Z) (hz : z ∈ V) :
    cutoffLift U V hU hV hcover c hc a M hM (r, z) = a z :=
  ContinuousMap.liftCover_coe (hS := cutoffLift_cover U V hU hV hcover) (i := false) ⟨(r, z), hz⟩

/-- Vanishing cutoff makes every time slice the prescribed initial map. -/
theorem cutoffLift_apply_of_zero (r : I) (z : Z) (hz : c z = 0) :
    cutoffLift U V hU hV hcover c hc a M hM (r, z) = a z := by
  have hmem : z ∈ U ∪ V := by rw [hcover]; trivial
  rcases hmem with hu | hv
  · rw [cutoffLift_apply_of_mem U V hU hV hcover c hc a M hM r z hu, hz, mul_zero, hM]
  · exact cutoffLift_apply_of_mem_complement U V hU hV hcover c hc a M hM r z hv

/-- Exact initial values survive cutoff extension. -/
@[simp]
theorem cutoffLift_zero (z : Z) :
    cutoffLift U V hU hV hcover c hc a M hM (0, z) = a z := by
  have hmem : z ∈ U ∪ V := by rw [hcover]; trivial
  rcases hmem with hu | hv
  · rw [cutoffLift_apply_of_mem U V hU hV hcover c hc a M hM 0 z hu, zero_mul, hM]
  · exact cutoffLift_apply_of_mem_complement U V hU hV hcover c hc a M hM 0 z hv

/-- Identities verified on the two local formulas hold on the extension. -/
theorem cutoffLift_property (P : I → Z → E → Prop)
    (hu : ∀ r (z : U), P r z.1 (M (r * c z.1, z)))
    (hv : ∀ r z, z ∈ V → P r z (a z)) (r : I) (z : Z) :
    P r z (cutoffLift U V hU hV hcover c hc a M hM (r, z)) := by
  have hmem : z ∈ U ∪ V := by rw [hcover]; trivial
  rcases hmem with hz | hz
  · rw [cutoffLift_apply_of_mem U V hU hV hcover c hc a M hM r z hz]
    exact hu r ⟨z, hz⟩
  · rw [cutoffLift_apply_of_mem_complement U V hU hV hcover c hc a M hM r z hz]
    exact hv r z hz

end Topology
