/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Basic
public import Colib.Topology.HomotopyPullback.Basic

/-!
# Fibrations and path-space homotopy pullbacks

The stated homotopy lifting properties compare a fibration pullback with its actual path-space
    homotopy pullback.
-/
/-! Implementation source: `Quillen/Topology/HomotopyPullback/Fibration.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual compact-open path topology,
parameter spaces and canonical forward maps are retained. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.HomotopyPullback

variable {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A]
  [TopologicalSpace B] (f : C(X, B)) (g : C(A, B))

/-- Forgetting the chosen parameter gives a point of the mapping-path
replacement with the same initial point and path. -/
def toMappingPath : C(HomotopyPullback f g, MappingPath f) where
  toFun z := ⟨z.1.2, z.2.1⟩
  continuous_toFun := by fun_prop

/-- The actual homotopy-pullback base projection has covering-homotopy
lifting for arbitrary parameter spaces. -/
theorem baseProjection_homotopyLiftingProperty : HomotopyLiftingProperty (baseProjection f g) := by
  intro W _ a H hzero
  have hz : ∀ x, (g.comp H) (0, x) = MappingPath.endpoint f ((toMappingPath f g).comp a x) := by
    intro x
    change g (H (0, x)) = (a x).1.2.2 1
    rw [hzero]
    exact (a x).2.2.symm
  obtain ⟨L, hLzero, hLend⟩ := MappingPath.endpoint_homotopy_lifting f
    ((toMappingPath f g).comp a) (g.comp H) hz
  let Q : C(I × W, HomotopyPullback f g) := {
    toFun z := ⟨(H z, (L z).1), (L z).2, hLend z.1 z.2⟩
    continuous_toFun := by fun_prop }
  refine ⟨Q, ?_, fun _ _ ↦ rfl⟩
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact hzero x
  · exact congrArg Subtype.val (hLzero x)

/-- The strict fiber of the homotopy-pullback projection is homeomorphic
to the homotopy fiber of the original map at the chosen parameter value. -/
def strictBaseFiberHomeomorph (a : A) :
    {z : HomotopyPullback f g // baseProjection f g z = a} ≃ₜ HomotopyFiber f (g a) where
  toFun z := ⟨z.1.1.2, z.1.2.1, z.1.2.2.trans (congrArg g z.2)⟩
  invFun z := ⟨⟨(a, z.1), z.2⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact z.2.symm
    · rfl
  right_inv z := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The canonical fiber comparison for a homotopy-pullback projection:
retain the original source/path and add a constant parameter path. -/
def baseFiberComparison (a : A) :
    C(HomotopyFiber f (g a), HomotopyFiber (baseProjection f g) a) :=
  (HomotopyFiber.strictFiberInclusion (baseProjection f g) a).comp
    ((strictBaseFiberHomeomorph f g a).symm :
      C(HomotopyFiber f (g a), {z : HomotopyPullback f g // baseProjection f g z = a}))

/-- Every actual homotopy pullback has the expected homotopy fibers, via
the canonical fiber comparison and a genuine homotopy equivalence. -/
def baseFiberHomotopyEquiv (a : A) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber f (g a))
      (HomotopyFiber (baseProjection f g) a) :=
  (strictBaseFiberHomeomorph f g a).symm.toHomotopyEquiv.trans
    (HomotopyFiber.strictFiberHomotopyEquivOfLifting (baseProjection f g)
      (baseProjection_homotopyLiftingProperty f g) a)

@[simp]
theorem baseFiberHomotopyEquiv_toFun (a : A) :
    (baseFiberHomotopyEquiv f g a).toFun = baseFiberComparison f g a := rfl

/-- The strict pullback includes in the path-space pullback by constant
paths, with the usual subspace topology on its source. -/
def strictPullbackInclusion : C({z : A × X // f z.2 = g z.1}, HomotopyPullback f g) where
  toFun z := ⟨(z.1.1, z.1.2, ContinuousMap.const I (g z.1.1)), z.2.symm, rfl⟩
  continuous_toFun := by fun_prop

variable (hf : HomotopyLiftingProperty f)

/-- Covering-homotopy lifting applied to all points of the path-space
pullback at once. The parameter coordinate remains unchanged. -/
def universalLift : C(I × HomotopyPullback f g, X) :=
  (hf (HomotopyPullback f g) (sourceProjection f g)
    ⟨fun z ↦ z.2.1.2.2 z.1, by fun_prop⟩ (fun z ↦ z.2.1)).choose

theorem universalLift_zero (z : HomotopyPullback f g) :
    universalLift f g hf (0, z) = z.1.2.1 :=
  (hf (HomotopyPullback f g) (sourceProjection f g)
    ⟨fun z ↦ z.2.1.2.2 z.1, by fun_prop⟩ (fun z ↦ z.2.1)).choose_spec.1 z

theorem universalLift_projection (t : I) (z : HomotopyPullback f g) :
    f (universalLift f g hf (t, z)) = z.1.2.2 t :=
  (hf (HomotopyPullback f g) (sourceProjection f g)
    ⟨fun z ↦ z.2.1.2.2 z.1, by fun_prop⟩ (fun z ↦ z.2.1)).choose_spec.2 t z

/-- The universal lift sends the path-space pullback back to the strict
pullback, retaining the chosen parameter. -/
def strictPullbackRetraction : C(HomotopyPullback f g, {z : A × X // f z.2 = g z.1}) where
  toFun z := ⟨(z.1.1, universalLift f g hf (1, z)),
    (universalLift_projection f g hf 1 z).trans z.2.2⟩
  continuous_toFun := by fun_prop

/-- The lifted starting point and remaining tail yield the right inverse
homotopy continuously over the entire parameter space. -/
def strictPullbackRightHomotopy :
    (ContinuousMap.id (HomotopyPullback f g)).Homotopy
      ((strictPullbackInclusion f g).comp (strictPullbackRetraction f g hf)) where
  toFun z := ⟨(z.2.1.1, universalLift f g hf (z.1, z.2),
    ⟨fun s ↦ z.2.1.2.2 (σ (σ z.1 * σ s)), by fun_prop⟩),
    by simpa using (universalLift_projection f g hf z.1 z.2).symm,
    by simpa using z.2.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.prodMk
      · exact (universalLift f g hf).continuous
      · apply ContinuousMap.continuous_of_continuous_uncurry
        change Continuous (fun z : (I × HomotopyPullback f g) × I ↦
          z.1.2.1.2.2 (σ (σ z.1.1 * σ z.2)))
        fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact universalLift_zero f g hf z
      · ext s
        simp
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro s
        change z.1.2.2 (σ (σ 1 * σ s)) = g z.1.1
        simpa using z.2.2

/-- Restricting the universal lift to constant paths gives the left
inverse homotopy within the strict pullback. -/
def strictPullbackLeftHomotopy :
    (ContinuousMap.id {z : A × X // f z.2 = g z.1}).Homotopy
      ((strictPullbackRetraction f g hf).comp (strictPullbackInclusion f g)) where
  toFun z := ⟨(z.2.1.1, universalLift f g hf (z.1, strictPullbackInclusion f g z.2)),
    universalLift_projection f g hf z.1 (strictPullbackInclusion f g z.2)⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact universalLift_zero f g hf (strictPullbackInclusion f g z)
  map_one_left z := rfl

/-- Pulling back a map with covering-homotopy lifting gives a genuine
homotopy-cartesian square. This is proved for an arbitrary base-change
map and retains the canonical constant-path comparison. -/
def strictPullbackHomotopyEquivOfLifting :
    ContinuousMap.HomotopyEquiv {z : A × X // f z.2 = g z.1} (HomotopyPullback f g) where
  toFun := strictPullbackInclusion f g
  invFun := strictPullbackRetraction f g hf
  left_inv := ⟨(strictPullbackLeftHomotopy f g hf).symm⟩
  right_inv := ⟨(strictPullbackRightHomotopy f g hf).symm⟩

@[simp]
theorem strictPullbackHomotopyEquivOfLifting_toFun :
    (strictPullbackHomotopyEquivOfLifting f g hf).toFun = strictPullbackInclusion f g := rfl

end Topology.HomotopyPullback

end
