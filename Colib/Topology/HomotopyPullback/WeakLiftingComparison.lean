/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Weak
public import Colib.Topology.HomotopyPullback.Fibration

/-!
# Weak covering-homotopy lifting implies homotopy-cartesian pullbacks

A weak lift first corrects its initial source within the fixed fiber. The
correction followed by the lifted path gives both inverse homotopies for
the canonical strict-pullback comparison. This proves the weak-lifting
version of the pullback lemma used in homotopy-cartesian gluing; no global
realization or local-to-global lifting conclusion is assumed.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyPullback/WeakLiftingComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.HomotopyPullback

variable {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A]
  [TopologicalSpace B] (f : C(X, B)) (g : C(A, B)) (hf : WeakHomotopyLiftingProperty f)

include hf in
/-- Weak lifting of all pullback paths at once, with its initial correction. -/
theorem exists_weakUniversalLift :
    ∃ L : C(I × HomotopyPullback f g, X),
      (∀ t z, f (L (t, z)) = z.1.2.2 t) ∧
        ∃ K : (sourceProjection f g).Homotopy (homotopyTimeSlice L 0),
          ∀ t z, f (K (t, z)) = f z.1.2.1 :=
  hf (HomotopyPullback f g) (sourceProjection f g)
    ⟨fun z ↦ z.2.1.2.2 z.1, by fun_prop⟩ (fun z ↦ z.2.1)

/-- A chosen universal weak lift. -/
def weakUniversalLift : C(I × HomotopyPullback f g, X) :=
  (exists_weakUniversalLift f g hf).choose

theorem weakUniversalLift_projection (t : I) (z : HomotopyPullback f g) :
    f (weakUniversalLift f g hf (t, z)) = z.1.2.2 t :=
  (exists_weakUniversalLift f g hf).choose_spec.1 t z

/-- Its specified initial correction stays in each fixed original fiber. -/
def weakUniversalCorrection :
    (sourceProjection f g).Homotopy (homotopyTimeSlice (weakUniversalLift f g hf) 0) :=
  (exists_weakUniversalLift f g hf).choose_spec.2.choose

theorem weakUniversalCorrection_projection (t : I) (z : HomotopyPullback f g) :
    f (weakUniversalCorrection f g hf (t, z)) = f z.1.2.1 :=
  (exists_weakUniversalLift f g hf).choose_spec.2.choose_spec t z

/-- The corrected initial source paired with the original unchanged path. -/
def weakPrepared : C(HomotopyPullback f g, HomotopyPullback f g) where
  toFun z := ⟨(z.1.1, weakUniversalLift f g hf (0, z), z.1.2.2),
    (weakUniversalLift_projection f g hf 0 z).symm, z.2.2⟩
  continuous_toFun := by fun_prop

/-- Correct the initial source in its fixed fiber, leaving the target path
unchanged. -/
def weakPrepareHomotopy : (ContinuousMap.id (HomotopyPullback f g)).Homotopy
    (weakPrepared f g hf) where
  toFun z := ⟨(z.2.1.1, weakUniversalCorrection f g hf (z.1, z.2), z.2.1.2.2),
    z.2.2.1.trans (weakUniversalCorrection_projection f g hf z.1 z.2).symm, z.2.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact (weakUniversalCorrection f g hf).continuous.prodMk (by fun_prop)
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact (weakUniversalCorrection f g hf).map_zero_left z
      · rfl
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact (weakUniversalCorrection f g hf).map_one_left z
      · rfl

/-- The endpoint of the universal weak lift lies in the strict pullback. -/
def weakStrictPullbackRetraction :
    C(HomotopyPullback f g, {z : A × X // f z.2 = g z.1}) where
  toFun z := ⟨(z.1.1, weakUniversalLift f g hf (1, z)),
    (weakUniversalLift_projection f g hf 1 z).trans z.2.2⟩
  continuous_toFun := by fun_prop

/-- After correcting the initial source, follow the lift and shorten the
remaining path continuously. -/
def weakSlideHomotopy : (weakPrepared f g hf).Homotopy
    ((strictPullbackInclusion f g).comp (weakStrictPullbackRetraction f g hf)) where
  toFun z := ⟨(z.2.1.1, weakUniversalLift f g hf (z.1, z.2),
    ⟨fun s ↦ z.2.1.2.2 (σ (σ z.1 * σ s)), by fun_prop⟩),
    by simpa using (weakUniversalLift_projection f g hf z.1 z.2).symm,
    by simpa using z.2.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.prodMk
      · exact (weakUniversalLift f g hf).continuous
      · apply ContinuousMap.continuous_of_continuous_uncurry
        change Continuous (fun z : (I × HomotopyPullback f g) × I ↦
          z.1.2.1.2.2 (σ (σ z.1.1 * σ z.2)))
        fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · ext s
        change z.1.2.2 (σ (σ 0 * σ s)) = z.1.2.2 s
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

/-- The corrected initial point of a strict pullback remains strict. -/
def weakPreparedStrict : C({z : A × X // f z.2 = g z.1}, {z : A × X // f z.2 = g z.1}) where
  toFun z := ⟨(z.1.1, weakUniversalLift f g hf (0, strictPullbackInclusion f g z)),
    weakUniversalLift_projection f g hf 0 (strictPullbackInclusion f g z)⟩
  continuous_toFun := by fun_prop

/-- The initial correction restricts to a homotopy within the strict pullback. -/
def weakPrepareStrictHomotopy :
    (ContinuousMap.id {z : A × X // f z.2 = g z.1}).Homotopy (weakPreparedStrict f g hf) where
  toFun z := ⟨(z.2.1.1, weakUniversalCorrection f g hf (z.1, strictPullbackInclusion f g z.2)),
    (weakUniversalCorrection_projection f g hf z.1 (strictPullbackInclusion f g z.2)).trans z.2.2⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (weakUniversalCorrection f g hf).map_zero_left (strictPullbackInclusion f g z)
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (weakUniversalCorrection f g hf).map_one_left (strictPullbackInclusion f g z)

/-- The weak lift of a constant path stays in its strict fiber. -/
def weakSlideStrictHomotopy : (weakPreparedStrict f g hf).Homotopy
    ((weakStrictPullbackRetraction f g hf).comp (strictPullbackInclusion f g)) where
  toFun z := ⟨(z.2.1.1, weakUniversalLift f g hf (z.1, strictPullbackInclusion f g z.2)),
    weakUniversalLift_projection f g hf z.1 (strictPullbackInclusion f g z.2)⟩
  continuous_toFun := by fun_prop
  map_zero_left z := rfl
  map_one_left z := rfl

/-- Weak covering-homotopy lifting suffices for every strict pullback
square to be genuinely homotopy cartesian, with the canonical comparison. -/
def strictPullbackHomotopyEquivOfWeakLifting :
    ContinuousMap.HomotopyEquiv {z : A × X // f z.2 = g z.1} (HomotopyPullback f g) where
  toFun := strictPullbackInclusion f g
  invFun := weakStrictPullbackRetraction f g hf
  left_inv := ⟨((weakPrepareStrictHomotopy f g hf).trans (weakSlideStrictHomotopy f g hf)).symm⟩
  right_inv := ⟨((weakPrepareHomotopy f g hf).trans (weakSlideHomotopy f g hf)).symm⟩

@[simp]
theorem strictPullbackHomotopyEquivOfWeakLifting_toFun :
    (strictPullbackHomotopyEquivOfWeakLifting f g hf).toFun = strictPullbackInclusion f g := rfl

end Topology.HomotopyPullback
