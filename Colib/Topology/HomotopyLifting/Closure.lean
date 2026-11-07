/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Collar.LiftData

/-! Elementary closure properties of actual covering-homotopy lifting. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyLifting/Closure.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology

/-- Covering-homotopy lifting is preserved by restriction to any base subspace. -/
theorem HomotopyLiftingProperty.baseRestriction
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : HomotopyLiftingProperty p) (S : Set B) :
    HomotopyLiftingProperty (baseRestrictionMap p S) := by
  intro A _ a H hzero
  let a' : C(A, E) := ⟨fun x ↦ (a x).1, by fun_prop⟩
  let H' : C(I × A, B) := ⟨fun x ↦ (H x).1, by fun_prop⟩
  obtain ⟨L, hL₀, hL⟩ := hp A a' H' (fun x ↦ congrArg Subtype.val (hzero x))
  let L' : C(I × A, {e : E // p e ∈ S}) := {
    toFun z := ⟨L z, by rw [hL z.1 z.2]; exact (H z).2⟩
    continuous_toFun := by fun_prop }
  refine ⟨L', fun x ↦ Subtype.ext (hL₀ x), fun t x ↦ Subtype.ext (hL t x)⟩

/-- Products of genuine Hurewicz fibrations have the same lifting property. -/
theorem HomotopyLiftingProperty.prod
    {E B F C : Type u} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace C] {p : C(E, B)} {q : C(F, C)}
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q) :
    HomotopyLiftingProperty (p.prodMap q) := by
  intro A _ a H hzero
  obtain ⟨L, hL₀, hL⟩ := hp A (ContinuousMap.fst.comp a)
    (ContinuousMap.fst.comp H) (fun x ↦ congrArg Prod.fst (hzero x))
  obtain ⟨K, hK₀, hK⟩ := hq A (ContinuousMap.snd.comp a)
    (ContinuousMap.snd.comp H) (fun x ↦ congrArg Prod.snd (hzero x))
  refine ⟨L.prodMk K, fun x ↦ Prod.ext (hL₀ x) (hK₀ x),
    fun t x ↦ Prod.ext (hL t x) (hK t x)⟩

/-- The identity has exact covering-homotopy lifting. -/
theorem homotopyLiftingProperty_id (B : Type u) [TopologicalSpace B] :
    HomotopyLiftingProperty (ContinuousMap.id B) := by
  intro A _ a H hzero
  exact ⟨H, hzero, fun _ _ ↦ rfl⟩

/-- A product with an identity map remains a Hurewicz fibration. -/
theorem HomotopyLiftingProperty.prod_id
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : HomotopyLiftingProperty p)
    (K : Type) [TopologicalSpace K] :
    HomotopyLiftingProperty (p.prodMap (ContinuousMap.id K)) :=
  by
    intro A _ a H hzero
    obtain ⟨L, hL₀, hL⟩ := hp A (ContinuousMap.fst.comp a)
      (ContinuousMap.fst.comp H) (fun x ↦ congrArg Prod.fst (hzero x))
    refine ⟨L.prodMk (ContinuousMap.snd.comp H), ?_, ?_⟩
    · intro x
      have h := congrArg (fun z : B × K ↦ z.2) (hzero x)
      exact Prod.ext (hL₀ x) h
    · intro t x
      exact Prod.ext (hL t x) rfl

/-- Weak lifting is invariant under a source homeomorphism over the base. -/
theorem WeakHomotopyLiftingProperty.of_sourceHomeomorph
    {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    {p : C(E, B)} (hp : WeakHomotopyLiftingProperty p)
    (q : C(F, B)) (e : F ≃ₜ E) (he : p.comp (e : C(F, E)) = q) :
    WeakHomotopyLiftingProperty q := by
  have hi : q.comp (e.symm : C(E, F)) = p := by
    ext x
    exact (ContinuousMap.congr_fun he (e.symm x)).symm.trans (by simp)
  have hid : ContinuousMap.id F = (e.symm : C(E, F)).comp (e : C(F, E)) := by
    ext x
    simp
  exact weakLifting_of_fiberwise_deformation q p hp (e.symm : C(E, F))
    (e : C(F, E)) hi he ((ContinuousMap.Homotopy.refl _).cast rfl hid)
    (fun _ _ ↦ rfl)

end Topology
