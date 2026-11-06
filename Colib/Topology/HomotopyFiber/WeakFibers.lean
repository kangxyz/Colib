/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.WeakContractibility
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceCancellation
public import Colib.Topology.HomotopyLifting.Basic

/-! # Actual fibers of weak equivalences at all points

The mapping-path replacement is a genuine homotopy equivalence on total
spaces and its endpoint projection has covering-homotopy lifting. This
transfers the pointed LES calculation to arbitrary points of every actual
homotopy fiber. No continuous choice of inverse paths is made.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/WeakFibers.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual mapping-path endpoint retains the original weak equivalence. -/
theorem MappingPath.endpoint_isWeakHomotopyEquivalence (f : C(X, Y))
    (hf : IsWeakHomotopyEquivalence f) : IsWeakHomotopyEquivalence (endpoint f) :=
  IsWeakHomotopyEquivalence.of_comp_left (f := inclusion f) (g := endpoint f)
    hf (isWeakHomotopyEquivalence_of_homotopyEquiv (inclusionHomotopyEquiv f))

namespace HomotopyFiber

/-- A weak genuine fibration has singleton finite homotopy sets on its actual
strict fibers, at every displayed point. -/
theorem subsingleton_strictFiber_of_weak_fibration
    (f : C(X, Y)) (hf : IsWeakHomotopyEquivalence f)
    (hl : HomotopyLiftingProperty f) (y : Y) (z : {x : X // f x = y}) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi n {x : X // f x = y} z) := by
  have h : ∀ n : ℕ, Function.Bijective (HomotopyGroup.map (N := Fin n) f z.2) := by
    rcases z with ⟨z, rfl⟩
    exact hf.homotopy_bijective z
  let := subsingleton_homotopyGroup_of_adjacent f y z.1 z.2 n
    (h n).injective (h (n + 1)).surjective
  exact (homotopyGroupMap_bijective_of_homotopyEquiv
    (strictFiberHomotopyEquivOfLifting f hl y) (x := z)
      (y := basepoint f y z.1 z.2) rfl n).injective.subsingleton

/-- Every finite homotopy set of every actual homotopy fiber of a weak
 equivalence is singleton, at any supplied fiber point. -/
theorem subsingleton_of_weakEquivalence (f : C(X, Y))
    (hf : IsWeakHomotopyEquivalence f) (y : Y) (z : HomotopyFiber f y) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi n (HomotopyFiber f y) z) := by
  let e := (MappingPath.endpointFiberHomeomorph f y).symm
  let := subsingleton_strictFiber_of_weak_fibration (MappingPath.endpoint f)
    (MappingPath.endpoint_isWeakHomotopyEquivalence f hf)
    (MappingPath.endpoint_homotopyLiftingProperty f) y (e z) n
  exact (homotopyGroupMap_bijective_of_homotopyEquiv e.toHomotopyEquiv
    (x := z) (y := e z) rfl n).injective.subsingleton

/-- The component-surjectivity clause supplies an actual point of every fiber,
including the cases where either ambient type might otherwise be empty. -/
theorem nonempty_of_weakEquivalence (f : C(X, Y))
    (hf : IsWeakHomotopyEquivalence f) (y : Y) : Nonempty (HomotopyFiber f y) := by
  obtain ⟨x, hx⟩ := hf.component_surjective y
  let γ := hx.somePath
  exact ⟨⟨(x, γ.toContinuousMap), γ.source, γ.target⟩⟩

/-- All actual homotopy fibers of a weak equivalence are path connected. -/
theorem pathConnectedSpace_of_weakEquivalence (f : C(X, Y))
    (hf : IsWeakHomotopyEquivalence f) (y : Y) : PathConnectedSpace (HomotopyFiber f y) := by
  let z := Classical.choice (nonempty_of_weakEquivalence f hf y)
  let := subsingleton_of_weakEquivalence f hf y z 0
  let : Subsingleton (ZerothHomotopy (HomotopyFiber f y)) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (X := HomotopyFiber f y) (x :=
      z)).symm.injective.subsingleton
  exact pathConnectedSpace_iff_zerothHomotopy.2 ⟨⟨ZerothHomotopy.mk z⟩, inferInstance⟩

end HomotopyFiber
end Topology
