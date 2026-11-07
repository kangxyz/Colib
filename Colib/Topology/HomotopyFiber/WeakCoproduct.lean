/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.WeakCriterion
public import Colib.Topology.HomotopyFiber.ProjectionFibration
public import Colib.Topology.HomotopyPullback.CoproductPaths

/-! # Empty-aware weak equivalences assemble over actual coproducts

The original fiber over one coproduct component is homeomorphic to the
original summand fiber. The complete all-fiber criterion then proves the
weak property for the original index-preserving sigma map. Empty indices
and empty summands require no extra nonemptiness assumption.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/WeakCoproduct.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Topology.WeakCoproduct
open Topology.HomotopyPullback
variable {ι : Type u} {X Y : ι → Type u}
  [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
  (f : ∀ i, C(X i, Y i))

/-- The actual summand fiber is the entire original sigma fiber over that
summand, with its compact-open path topology unchanged. -/
def fiberHomeomorph (i : ι) (y : Y i) :
    HomotopyFiber (f i) y ≃ₜ HomotopyFiber (sigmaMap f) ⟨i,y⟩ :=
  ((HomotopyFiber.constantParameterHomeomorph (f i) y).trans
    (componentPullbackHomeomorph f i (ContinuousMap.const (ULift.{u} Unit) y))).trans
      (HomotopyFiber.constantParameterHomeomorph (sigmaMap f) ⟨i,y⟩).symm

@[simp] theorem fiberHomeomorph_source (i : ι) (y : Y i) (z : HomotopyFiber (f i) y) :
    (fiberHomeomorph f i y z).1.1 = ⟨i,z.1.1⟩ := rfl

@[simp] theorem fiberHomeomorph_path (i : ι) (y : Y i) (z : HomotopyFiber (f i) y) :
    (fiberHomeomorph f i y z).1.2 = (ContinuousMap.sigmaMk i).comp z.1.2 := rfl

/-- Arbitrary coproducts preserve the complete weak homotopy-equivalence
property for the original sigma map, including all empty-space cases. -/
theorem isWeakHomotopyEquivalence_sigma
    (hf : ∀ i, IsWeakHomotopyEquivalence (f i)) : IsWeakHomotopyEquivalence (sigmaMap f) := by
  apply HomotopyFiber.isWeakHomotopyEquivalence_of_fibers
  · rintro ⟨i,y⟩
    exact (HomotopyFiber.nonempty_of_weakEquivalence (f i) (hf i) y).map
      (fiberHomeomorph f i y)
  · rintro ⟨i,y⟩ z n
    let e := (fiberHomeomorph f i y).symm
    let := HomotopyFiber.subsingleton_of_weakEquivalence (f i) (hf i) y (e z) n
    exact (homotopyGroupMap_bijective_of_homotopyEquiv e.toHomotopyEquiv
      (x := z) (y := e z) rfl n).injective.subsingleton

end Topology.WeakCoproduct
