/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingPath.Basic

/-!
# Strict fibers of maps with covering-homotopy lifting

The ordinary covering homotopy property implies that the constant-path
inclusion of each strict fiber into the actual homotopy fiber is a genuine
homotopy equivalence. Both inverse homotopies are constructed from one
universal lift. The mapping-path endpoint projection satisfies the lifting
hypothesis by the preceding, independent proof.
-/
/-! Implementation source: `Quillen/Topology/HomotopyLifting/Basic.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual compact-open path topology,
parameter spaces and canonical forward maps are retained. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology

/-- The ordinary covering homotopy property for all parameter spaces in
the given universe. This is a lifting property, not a fiber-equivalence
hypothesis. -/
def HomotopyLiftingProperty {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) : Prop :=
  ∀ (A : Type u) [TopologicalSpace A] (a : C(A, E)) (H : C(I × A, B)),
    (∀ x, H (0, x) = p (a x)) →
      ∃ L : C(I × A, E), (∀ x, L (0, x) = a x) ∧ ∀ t x, p (L (t, x)) = H (t, x)

namespace MappingPath

/-- The constructed mapping-path endpoint map is a Hurewicz fibration in
the explicit covering-homotopy sense. -/
theorem endpoint_homotopyLiftingProperty {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) : HomotopyLiftingProperty (endpoint f) :=
  fun _ _ a H hzero ↦ endpoint_homotopy_lifting f a H hzero

end MappingPath

namespace HomotopyFiber

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B)) (hp : HomotopyLiftingProperty p) (b : B)

/-- The universal covering homotopy lifts every path in a homotopy fiber
simultaneously, starting at its given source. -/
def universalFiberLift : C(I × HomotopyFiber p b, E) :=
  (hp (HomotopyFiber p b) (projection p b) (projectionNullhomotopy p b).toContinuousMap
    (fun z ↦ z.2.1)).choose

theorem universalFiberLift_zero (z : HomotopyFiber p b) :
    universalFiberLift p hp b (0, z) = projection p b z :=
  (hp (HomotopyFiber p b) (projection p b) (projectionNullhomotopy p b).toContinuousMap
    (fun z ↦ z.2.1)).choose_spec.1 z

theorem universalFiberLift_projection (t : I) (z : HomotopyFiber p b) :
    p (universalFiberLift p hp b (t, z)) = z.1.2 t :=
  (hp (HomotopyFiber p b) (projection p b) (projectionNullhomotopy p b).toContinuousMap
    (fun z ↦ z.2.1)).choose_spec.2 t z

/-- Lift to the final endpoint to obtain a point of the strict fiber. -/
def strictFiberRetraction : C(HomotopyFiber p b, {x : E // p x = b}) where
  toFun z := ⟨universalFiberLift p hp b (1, z),
    (universalFiberLift_projection p hp b 1 z).trans z.2.2⟩
  continuous_toFun := by fun_prop

/-- Following the lifted source while shortening the remaining path
homotopes the identity to inclusion after retraction. -/
def strictFiberRightHomotopy : (ContinuousMap.id (HomotopyFiber p b)).Homotopy
    ((strictFiberInclusion p b).comp (strictFiberRetraction p hp b)) where
  toFun z := ⟨(universalFiberLift p hp b (z.1, z.2),
    ⟨fun s ↦ z.2.1.2 (σ (σ z.1 * σ s)), by fun_prop⟩),
    by simpa using (universalFiberLift_projection p hp b z.1 z.2).symm,
    by simpa using z.2.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (universalFiberLift p hp b).continuous
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (I × HomotopyFiber p b) × I ↦
        z.1.2.1.2 (σ (σ z.1.1 * σ z.2)))
      fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · exact universalFiberLift_zero p hp b z
    · ext s
      simp
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro s
      change z.1.2 (σ (σ 1 * σ s)) = b
      simpa using z.2.2

/-- On constant paths the same lifted homotopy stays in the strict fiber,
so the retraction is a homotopy inverse there as well. -/
def strictFiberLeftHomotopy : (ContinuousMap.id {x : E // p x = b}).Homotopy
    ((strictFiberRetraction p hp b).comp (strictFiberInclusion p b)) where
  toFun z := ⟨universalFiberLift p hp b (z.1, strictFiberInclusion p b z.2),
    universalFiberLift_projection p hp b z.1 (strictFiberInclusion p b z.2)⟩
  continuous_toFun := by fun_prop
  map_zero_left z := Subtype.ext (universalFiberLift_zero p hp b (strictFiberInclusion p b z))
  map_one_left z := rfl

/-- For every map with genuine homotopy lifting, the canonical strict-fiber
inclusion is an actual homotopy equivalence. -/
def strictFiberHomotopyEquivOfLifting :
    ContinuousMap.HomotopyEquiv {x : E // p x = b} (HomotopyFiber p b) where
  toFun := strictFiberInclusion p b
  invFun := strictFiberRetraction p hp b
  left_inv := ⟨(strictFiberLeftHomotopy p hp b).symm⟩
  right_inv := ⟨(strictFiberRightHomotopy p hp b).symm⟩

@[simp]
theorem strictFiberHomotopyEquivOfLifting_toFun :
    (strictFiberHomotopyEquivOfLifting p hp b).toFun = strictFiberInclusion p b := rfl

end HomotopyFiber
end Topology
