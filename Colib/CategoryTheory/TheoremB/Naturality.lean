/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.Comparison
public import Colib.Topology.ClassifyingSpace.Naturality
public import Colib.Topology.HomotopyFiber.Map

/-!
# Naturality of comma-to-fiber comparisons

Implementation source: `Quillen/CategoryTheory/TheoremB/Naturality.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual simplex families,
path coordinates, and endpoint data are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology CategoryTheory SSet Opposite MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- On a comma vertex the nullhomotopy is the realized structure arrow. -/
@[simp]
theorem commaNullhomotopy_vertex (d : D) (X : CostructuredArrow F d) (t : unitInterval) :
    commaNullhomotopy F d (t, classifyingSpacePoint X) = classifyingSpacePath X.hom t :=
  classifyingSpaceNaturalTransformationHomotopy_vertex (commaTransformation F d) X t

section Postcomposition

variable {E : Type u} [SmallCategory E] (K : D ⥤ E)

/-- Applying a functor to the target gives the corresponding map of actual
homotopy fibers, including the required vertex endpoint equality. -/
def postFiberMap (d : D) :
    C(HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d),
      HomotopyFiber (classifyingSpaceMap (F ⋙ K)).hom (classifyingSpacePoint (K.obj d))) where
  toFun z := ⟨(z.1.1, (classifyingSpaceMap K).hom.comp z.1.2),
    (congrArg (classifyingSpaceMap K) z.2.1).trans (by
      rw [classifyingSpaceMap_comp]
      rfl),
    (congrArg (classifyingSpaceMap K) z.2.2).trans (classifyingSpaceMap_point K d)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact (ContinuousMap.continuous_postcomp (classifyingSpaceMap K).hom).comp (by fun_prop)

/-- Target functors commute with the actual nullhomotopies supplied by comma arrows. -/
theorem commaNullhomotopy_post (d : D) (t : unitInterval)
    (x : ClassifyingSpace (CostructuredArrow F d)) :
    commaNullhomotopy (F ⋙ K) (K.obj d)
      (t, classifyingSpaceMap (CostructuredArrow.post F K d) x) =
      classifyingSpaceMap K (commaNullhomotopy F d (t, x)) := by
  change classifyingSpaceNaturalTransformationHomotopy
    (commaTransformation (F ⋙ K) (K.obj d))
    (t, classifyingSpaceMap (CostructuredArrow.post F K d) x) =
    classifyingSpaceMap K
      (classifyingSpaceNaturalTransformationHomotopy (commaTransformation F d) (t, x))
  rw [← classifyingSpaceNaturalTransformationHomotopy_whiskerLeft,
    ← classifyingSpaceNaturalTransformationHomotopy_whiskerRight]
  have hc : naturalTransformationCylinderFunctor
      (Functor.whiskerLeft (CostructuredArrow.post F K d)
        (commaTransformation (F ⋙ K) (K.obj d))) =
      naturalTransformationCylinderFunctor
        (Functor.whiskerRight (commaTransformation F d) K) := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ rfl ?_ ?_
    · refine CategoryTheory.Functor.ext (fun a ↦ rfl) ?_
      intro a b f
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
        Functor.uncurry, ComposableArrows.mk₁]
    · ext a
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
        Functor.uncurry, ComposableArrows.mk₁, ComposableArrows.hom, commaTransformation,
          CostructuredArrow.post]
  have hn : naturalTransformationNerveCylinder
      (Functor.whiskerLeft (CostructuredArrow.post F K d)
        (commaTransformation (F ⋙ K) (K.obj d))) =
      naturalTransformationNerveCylinder
        (Functor.whiskerRight (commaTransformation F d) K) := by
    ext n z
    change _ ⋙ naturalTransformationCylinderFunctor _ =
      _ ⋙ naturalTransformationCylinderFunctor _
    rw [hc]
  change SSet.toTop.map (naturalTransformationNerveCylinder
    (Functor.whiskerLeft (CostructuredArrow.post F K d)
      (commaTransformation (F ⋙ K) (K.obj d)))) _ =
    SSet.toTop.map (naturalTransformationNerveCylinder
      (Functor.whiskerRight (commaTransformation F d) K)) _
  rw [hn]

/-- The canonical comma-to-fiber map commutes strictly with postcomposition,
including its path coordinate. -/
theorem fiberComparison_post (d : D) :
    (fiberComparison (F ⋙ K) (K.obj d)).comp
      (classifyingSpaceMap (CostructuredArrow.post F K d)).hom =
      (postFiberMap F K d).comp (fiberComparison F d) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply _root_.Prod.ext
  · change classifyingSpaceMap (CostructuredArrow.proj (F ⋙ K) (K.obj d))
      (classifyingSpaceMap (CostructuredArrow.post F K d) x) =
        classifyingSpaceMap (CostructuredArrow.proj F d) x
    change (classifyingSpaceMap (CostructuredArrow.post F K d) ≫
      classifyingSpaceMap (CostructuredArrow.proj (F ⋙ K) (K.obj d))) x = _
    rw [← classifyingSpaceMap_comp]
    rfl
  · apply ContinuousMap.ext
    intro t
    exact commaNullhomotopy_post F K d t x

end Postcomposition

end CategoryTheory.TheoremB
