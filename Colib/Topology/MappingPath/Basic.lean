/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.UnitInterval
public import Colib.Topology.Homotopy.IntervalEndpoints
public import Colib.Topology.HomotopyFiber.Basic
public import Mathlib.Topology.Homotopy.Equiv

/-!
# The compact-open mapping-path replacement

The actual mapping-path space carries a source projection and an endpoint
projection. Its constant-path inclusion is a homotopy equivalence by the
explicit contraction which shrinks each path to its initial point.
The endpoint projection has covering homotopy lifting for every parameter
space. Its strict fibers are homeomorphic to the actual homotopy fibers.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/MappingPath/Basic.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, homotopies,
hypotheses and universes are retained; imports use native lower owners. -/
@[expose] public section


noncomputable section

open Topology CategoryTheory MonoidalCategory
open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology

/-- The mapping-path space retains the initial endpoint equation and lets
the terminal endpoint vary. -/
def MappingPath {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :=
  {z : X × C(I, Y) // z.2 0 = f z.1}

namespace MappingPath

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))

instance : TopologicalSpace (MappingPath f) :=
  inferInstanceAs (TopologicalSpace {z : X × C(I, Y) // z.2 0 = f z.1})

/-- The endpoint map of the mapping-path replacement. -/
def endpoint : C(MappingPath f, Y) where
  toFun z := z.1.2 1
  continuous_toFun := by fun_prop

/-- Projection to the original source. -/
def source : C(MappingPath f, X) where
  toFun z := z.1.1
  continuous_toFun := by fun_prop

/-- The canonical constant-path map from the original source. -/
def inclusion : C(X, MappingPath f) where
  toFun x := ⟨(x, ContinuousMap.const I (f x)), rfl⟩
  continuous_toFun := by fun_prop

@[simp]
theorem endpoint_inclusion : (endpoint f).comp (inclusion f) = f := rfl

@[simp]
theorem source_inclusion : (source f).comp (inclusion f) = ContinuousMap.id X := rfl

/-- Shrinking a path to its fixed starting point contracts the mapping-path
replacement back onto the original source. -/
def contraction : (ContinuousMap.id (MappingPath f)).Homotopy ((inclusion f).comp (source f)) where
  toFun z := ⟨(z.2.1.1, ⟨fun s ↦ z.2.1.2 (σ z.1 * s), by fun_prop⟩), by simpa using z.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (I × MappingPath f) × I ↦ z.1.2.1.2 (σ z.1.1 * z.2))
      fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext s
      simp
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext s
      change z.1.2 (σ 1 * s) = f z.1.1
      simpa using z.2

@[simp]
theorem contraction_inclusion (t : I) (x : X) :
    contraction f (t, inclusion f x) = inclusion f x := rfl

/-- The source-to-mapping-path inclusion is a genuine homotopy equivalence. -/
def inclusionHomotopyEquiv : ContinuousMap.HomotopyEquiv X (MappingPath f) where
  toFun := inclusion f
  invFun := source f
  left_inv := ContinuousMap.Homotopic.refl _
  right_inv := ⟨(contraction f).symm⟩


/-- The strict fiber of the endpoint projection is exactly the usual
compact-open homotopy fiber, with no change of topology. -/
def endpointFiberHomeomorph (y : Y) :
    {z : MappingPath f // endpoint f z = y} ≃ₜ HomotopyFiber f y where
  toFun z := ⟨z.1.1, z.1.2, z.2⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Genuine covering homotopy lifting for the endpoint projection. Both
the initial lift and the entire prescribed base homotopy are preserved
exactly. The parameter space is arbitrary. -/
theorem endpoint_homotopy_lifting {A : Type u} [TopologicalSpace A]
    (a : C(A, MappingPath f)) (H : C(I × A, Y))
    (hzero : ∀ x, H (0, x) = endpoint f (a x)) :
    ∃ L : C(I × A, MappingPath f),
      (∀ x, L (0, x) = a x) ∧ (∀ t x, endpoint f (L (t, x)) = H (t, x)) := by
  let P : C(↑((TopCat.of A) ⊗ TopCat.I : TopCat.{u}), Y) := by
    change C(A × ULift.{u} I, Y)
    exact ⟨fun z ↦ (a z.1).1.2 z.2.down, by fun_prop⟩
  let K : C(I × (A ⊕ A), Y) := {
    toFun z := Sum.elim (fun x ↦ f (source f (a x))) (fun x ↦ H (z.1, x)) z.2
    continuous_toFun := by
      have hK : Continuous (fun z : (A ⊕ A) × I ↦
          Sum.elim (fun x ↦ f (source f (a x))) (fun x ↦ H (z.2, x)) z.1) := by
        convert ((f.continuous.comp ((source f).continuous.comp
          (a.continuous.comp continuous_fst))).sumElim
          (H.continuous.comp continuous_swap)).comp Homeomorph.sumProdDistrib.continuous using 1
        ext ⟨x, t⟩
        cases x <;> rfl
      exact hK.comp continuous_swap }
  have hKzero : ∀ x : A ⊕ A,
      K (0, x) = P (TopCat.intervalEndpoints (TopCat.of A) x) := by
    intro x
    cases x with
    | inl x => exact (a x).2.symm
    | inr x => exact hzero x
  obtain ⟨Q, hQzero, hQend⟩ := TopCat.homotopyExtensionProperty_continuous
    (TopCat.homotopyExtensionProperty_intervalEndpoints (TopCat.of A)) (TopCat.of Y) P K hKzero
  let L : C(I × A, MappingPath f) := {
    toFun z := ⟨((a z.2).1.1, ⟨fun s ↦ Q (z.1, (z.2, ULift.up s)), by fun_prop⟩),
      hQend z.1 (Sum.inl z.2)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk
      · fun_prop
      · apply ContinuousMap.continuous_of_continuous_uncurry
        exact Q.continuous.comp (continuous_fst.fst.prodMk
          (continuous_fst.snd.prodMk (continuous_uliftUp.comp continuous_snd))) }
  refine ⟨L, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro s
      exact hQzero (x, ULift.up s)
  · intro t x
    exact hQend t (Sum.inr x)

end MappingPath
end Topology
