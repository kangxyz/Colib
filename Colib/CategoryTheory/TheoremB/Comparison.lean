/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Comma.Transitions
public import Colib.Topology.ClassifyingSpace.Constant
public import Colib.Topology.Realization.HomotopyBridge
public import Colib.Topology.HomotopyFiber.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.Topology.Homotopy.Equiv

/-!
# The canonical comparison in Quillen's Theorem B

We use the covariant comma categories `(F ↓ d)`. Their structure arrows give
an actual continuous nullhomotopy of the projection followed by `|N F|`, and
hence the canonical map into the genuine path-space homotopy fiber.

Theorem B's hypothesis is stated for the actual postcomposition maps of
classifying spaces. Merely defining this hypothesis and comparison is not
an assertion that the comparison is a homotopy equivalence.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/Comparison.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual comma categories, nerves and
path-space maps are retained; no fiber-equivalence conclusion is assumed. -/
@[expose] public section


noncomputable section

open Topology CategoryTheory
open scoped Topology unitInterval

universe u

namespace CategoryTheory.TheoremB

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The structure-arrow transformation realizes to an actual nullhomotopy. -/
def commaNullhomotopy (d : D) :
    ((classifyingSpaceMap F).hom.comp
      (classifyingSpaceMap (CostructuredArrow.proj F d)).hom).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint d)) :=
  (classifyingSpaceNaturalTransformationHomotopy (commaTransformation F d)).cast
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
    (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- The canonical map from the realized comma category to the actual homotopy
fiber, carrying each point together with the path given by the comma homotopy. -/
def fiberComparison (d : D) :
    C(ClassifyingSpace (CostructuredArrow F d),
      HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  HomotopyFiber.lift _ _ (classifyingSpaceMap (CostructuredArrow.proj F d)).hom
    (commaNullhomotopy F d)

/-- The canonical fiber comparison lies strictly over the comma projection. -/
@[simp]
theorem fiberComparison_projection (d : D) :
    (HomotopyFiber.projection (classifyingSpaceMap F).hom (classifyingSpacePoint d)).comp
      (fiberComparison F d) = (classifyingSpaceMap (CostructuredArrow.proj F d)).hom :=
  HomotopyFiber.projection_lift _ _ _ _

/-- The actual path coordinate of the comparison map. -/
@[simp]
theorem fiberComparison_path (d : D) (x : ClassifyingSpace (CostructuredArrow F d))
    (t : unitInterval) :
    (fiberComparison F d x).1.2 t = commaNullhomotopy F d (t, x) := rfl

/-- The continuous transition map in Theorem B's hypothesis. -/
def transitionMap {d e : D} (f : d ⟶ e) :
    C(ClassifyingSpace (CostructuredArrow F d), ClassifyingSpace (CostructuredArrow F e)) :=
  (classifyingSpaceMap (transition F f)).hom

/-- The hypothesis of Quillen's Theorem B, in the `(F ↓ d)` convention:
every actual comma transition map has a continuous homotopy inverse. The
forward map is fixed, so an unrelated equivalence of the spaces cannot
satisfy this condition. -/
def TransitionHomotopyEquivalences : Prop :=
  ∀ ⦃d e : D⦄ (f : d ⟶ e), ∃ g : C(ClassifyingSpace (CostructuredArrow F e),
    ClassifyingSpace (CostructuredArrow F d)),
    (g.comp (transitionMap F f)).Homotopic (ContinuousMap.id _) ∧
    ((transitionMap F f).comp g).Homotopic (ContinuousMap.id _)

/-- Packaging the precise transition hypothesis as a homotopy equivalence
retains the prescribed forward map. -/
def transitionHomotopyEquiv (h : TransitionHomotopyEquivalences F)
    {d e : D} (f : d ⟶ e) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (CostructuredArrow F d))
      (ClassifyingSpace (CostructuredArrow F e)) where
  toFun := transitionMap F f
  invFun := (h f).choose
  left_inv := (h f).choose_spec.1
  right_inv := (h f).choose_spec.2

@[simp]
theorem transitionHomotopyEquiv_apply (h : TransitionHomotopyEquivalences F)
    {d e : D} (f : d ⟶ e) (x : ClassifyingSpace (CostructuredArrow F d)) :
    transitionHomotopyEquiv F h f x = transitionMap F f x := rfl

/-- At the identity comma object the canonical comparison selects the genuine
constant-path basepoint, rather than merely a point over the same source. -/
@[simp]
theorem fiberComparison_identity (c : C) :
    fiberComparison F (F.obj c) (classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) =
      HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c) := by
  apply Subtype.ext
  apply Prod.ext
  · exact classifyingSpaceMap_point (CostructuredArrow.proj F (F.obj c)) _
  · apply ContinuousMap.ext
    intro t
    exact (classifyingSpaceNaturalTransformationBasedHomotopy
      (commaTransformation F (F.obj c)) (CostructuredArrow.mk (𝟙 (F.obj c))) rfl rfl).eq_snd
      t rfl |>.trans (classifyingSpaceMap_point _ _)

end CategoryTheory.TheoremB
