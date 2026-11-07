/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.StructuredFullWeakTransitionComparison
public import Colib.Topology.ClassifyingSpace.CommaAsSmall
public import Colib.Topology.ClassifyingSpace.UniverseNaturality

/-!
# The original structured Theorem B comparison in arbitrary universes

The comparison is the lift of the original structured projection using the
reversed realization of its original structure-arrow transformation. Its full
weak-equivalence theorem allows independent object and morphism universes and
arbitrary target objects, including empty comma categories. Strict universe
lifting identifies this prescribed map with the common-universe comparison;
no abstract comparison map or unspecified basepoint path is substituted.

Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredUniverseComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology CategoryTheory
open scoped Topology unitInterval
universe u₁ v₁ u₂ v₂
namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace TheoremB
variable (F : C ⥤ D)

/-- The original component arrows in the structured comma, without universe restrictions. -/
@[simps] def structuredCommaTransformationUniversal (d : D) :
    (Functor.const (StructuredArrow d F)).obj d ⟶ StructuredArrow.proj d F ⋙ F where
  app X := X.hom
  naturality X Y f := by simp

/-- Reverse the actual realized structure arrows to obtain paths from `F(x)` to `d`. -/
def structuredCommaNullhomotopyUniversal (d : D) :
    ((classifyingSpaceMapUniversal F).comp
      (classifyingSpaceMapUniversal (StructuredArrow.proj d F))).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint d)) :=
  (classifyingSpaceUniversalHomotopy (structuredCommaTransformationUniversal F d)).symm.cast
    (classifyingSpaceMapUniversal_comp _ _) (classifyingSpaceMapUniversal_const _)

/-- The original structured projection, lifted by its reversed structure-arrow homotopy. -/
def structuredFiberComparisonUniversal (d : D) :
    C(ClassifyingSpace (StructuredArrow d F),
      HomotopyFiber (classifyingSpaceMapUniversal F) (classifyingSpacePoint d)) :=
  HomotopyFiber.lift _ _ (classifyingSpaceMapUniversal (StructuredArrow.proj d F))
    (structuredCommaNullhomotopyUniversal F d)

@[simp] theorem structuredFiberComparisonUniversal_projection (d : D) :
    (HomotopyFiber.projection (classifyingSpaceMapUniversal F) (classifyingSpacePoint d)).comp
      (structuredFiberComparisonUniversal F d) =
        classifyingSpaceMapUniversal (StructuredArrow.proj d F) :=
  HomotopyFiber.projection_lift _ _ _ _

/-- The full path coordinate remains the reversed original structure-arrow homotopy. -/
@[simp] theorem structuredFiberComparisonUniversal_path (d : D)
    (x : ClassifyingSpace (StructuredArrow d F)) (t : unitInterval) :
    (structuredFiberComparisonUniversal F d x).1.2 t =
      classifyingSpaceUniversalHomotopy (structuredCommaTransformationUniversal F d)
        (unitInterval.symm t, x) := rfl

/-- At every object vertex, the comparison retains the exact reversed original arrow path. -/
theorem structuredFiberComparisonUniversal_vertex_path (d : D)
    (X : StructuredArrow d F) (t : unitInterval) :
    (structuredFiberComparisonUniversal F d (classifyingSpacePoint X)).1.2 t =
      classifyingSpacePath X.hom (unitInterval.symm t) := by
  rw [structuredFiberComparisonUniversal_path, classifyingSpaceUniversalHomotopy_vertex_track]
  rfl

/-- An identity structured arrow gives the exact constant-path basepoint. -/
@[simp] theorem structuredFiberComparisonUniversal_identity (c : C) :
    structuredFiberComparisonUniversal F (F.obj c)
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) =
      HomotopyFiber.basepoint (classifyingSpaceMapUniversal F) (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMapUniversal_point F c) := by
  apply Subtype.ext
  apply Prod.ext
  · exact classifyingSpaceMapUniversal_point (StructuredArrow.proj (F.obj c) F) _
  · apply ContinuousMap.ext
    intro t
    rw [structuredFiberComparisonUniversal_vertex_path]
    exact congrArg (fun p : Path (classifyingSpacePoint (F.obj c))
      (classifyingSpacePoint (F.obj c)) ↦ p (unitInterval.symm t))
        (classifyingSpacePath_id (F.obj c))

/-- In common small universes, both coordinates are exactly those of the existing
structured comparison, rather than merely homotopic choices of paths. -/
theorem structuredFiberComparisonUniversal_val_eq {A B : Type u₁}
    [SmallCategory A] [SmallCategory B] (G : A ⥤ B) (d : B)
    (x : ClassifyingSpace (StructuredArrow d G)) :
    (structuredFiberComparisonUniversal G d x).val = (structuredFiberComparison G d x).val := by
  apply Prod.ext
  · exact ContinuousMap.congr_fun (classifyingSpaceMapUniversal_eq (StructuredArrow.proj d G)) x
  · apply ContinuousMap.ext
    intro t
    change classifyingSpaceUniversalHomotopy (structuredCommaTransformationUniversal G d)
      (unitInterval.symm t, x) = _
    rw [classifyingSpaceUniversalHomotopy_eq]
    rfl

/-- Every original structured transition is a weak equivalence in its original universes. -/
def StructuredTransitionWeakEquivalencesUniversal : Prop :=
  ∀ ⦃d e : D⦄ (f : d ⟶ e), IsWeakHomotopyEquivalence
    (classifyingSpaceMapUniversal (StructuredArrow.map (T := F) f))

/-- Original structured transitions pass to their common-universe lift. -/
theorem structuredTransitionWeakEquivalences_universeLift
    (h : StructuredTransitionWeakEquivalencesUniversal F) :
    StructuredTransitionWeakEquivalences
      ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙
        (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D)) := by
  intro d e f
  have hu := isWeakHomotopyEquivalence_of_homotopyEquiv
    (structuredArrowUniverseHomeomorph.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂}
      F (ULift.down e)).toHomotopyEquiv
  have hv := isWeakHomotopyEquivalence_of_homotopyEquiv
    (structuredArrowUniverseHomeomorph.{u₁, v₁, u₂, v₂, max u₁ v₁ u₂ v₂}
      F (ULift.down d)).toHomotopyEquiv
  have ht := hv.comp (h (ULift.down f))
  change IsWeakHomotopyEquivalence
    ((classifyingSpaceMapUniversal (StructuredArrow.asSmallUp F (ULift.down d))).comp
      (classifyingSpaceMapUniversal (StructuredArrow.map (ULift.down f)))) at ht
  rw [← classifyingSpaceMapUniversal_comp, ← StructuredArrow.asSmallUp_map,
    classifyingSpaceMapUniversal_comp] at ht
  have he := ht.of_comp_left hu
  change IsWeakHomotopyEquivalence (classifyingSpaceMap (StructuredArrow.map f)).hom
  simpa only [classifyingSpaceMapUniversal_eq, AsSmall.up, ULift.up_down] using he

/-- Universe lifting gives the actual homeomorphism of the original path-space fibers. -/
def structuredComparisonUniverseFiberHomeomorph (d : D) :
    HomotopyFiber (classifyingSpaceMapUniversal F) (classifyingSpacePoint d) ≃ₜ
      HomotopyFiber
        (classifyingSpaceMap
          ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙
            (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D))).hom
        (classifyingSpacePoint (AsSmall.up.obj d)) :=
  (HomotopyFiber.homeomorphOfSquare (classifyingSpaceMapUniversal F)
    (classifyingSpaceMap ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙
      (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D))).hom
    (classifyingSpaceUniverseHomeomorph.{u₁, v₁, max u₁ v₁ u₂ v₂} C)
    (classifyingSpaceUniverseHomeomorph.{u₂, v₂, max u₁ v₁ u₂ v₂} D)
    (by
      change (classifyingSpaceMapUniversal AsSmall.up).comp (classifyingSpaceMapUniversal F) =
        (classifyingSpaceMap (AsSmall.down ⋙ F ⋙ AsSmall.up)).hom.comp
          (classifyingSpaceMapUniversal AsSmall.up)
      rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_comp,
        ← classifyingSpaceMapUniversal_comp]
      rfl) (classifyingSpacePoint d)).trans
    (fiberEndpointHomeomorph _ (classifyingSpaceUniverseHomeomorph_point D d))

/-- Lifting identifies the complete original structure-arrow homotopy with the
common-universe structure-arrow homotopy, including its interval parameter. -/
theorem structuredCommaUniversalHomotopy_universeLift (d : D)
    (x : ClassifyingSpace (StructuredArrow d F)) (t : unitInterval) :
    classifyingSpaceUniversalHomotopy (structuredCommaTransformationUniversal F d) (t, x) =
      (classifyingSpaceUniverseHomeomorph.{u₂, v₂, max u₁ v₁ u₂ v₂} D).symm
        (classifyingSpaceNaturalTransformationHomotopy
          (structuredCommaTransformation
            ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙
              (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D))
            (AsSmall.up.obj d))
          (t, structuredArrowUniverseHomeomorph F d x)) := by
  let K : AsSmall.{max u₁ v₁ u₂ v₂} (StructuredArrow d F) ⥤
      StructuredArrow (AsSmall.up.obj d)
        ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙
          (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D)) :=
    AsSmall.down ⋙ StructuredArrow.asSmallUp F d
  let α := structuredCommaTransformation
    ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙
      (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D)) (AsSmall.up.obj d)
  change classifyingSpaceMapUniversal AsSmall.down
    (classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerLeft K α)
      (t, classifyingSpaceMapUniversal AsSmall.up x)) =
    classifyingSpaceMapUniversal AsSmall.down
      (classifyingSpaceNaturalTransformationHomotopy α
        (t, classifyingSpaceMapUniversal (StructuredArrow.asSmallUp F d) x))
  rw [classifyingSpaceNaturalTransformationHomotopy_whiskerLeft]
  apply congrArg (classifyingSpaceMapUniversal
    (AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} D ⥤ D))
  apply congrArg (fun y ↦ classifyingSpaceNaturalTransformationHomotopy α (t, y))
  change (classifyingSpaceMap K).hom (classifyingSpaceMapUniversal AsSmall.up x) =
    classifyingSpaceMapUniversal (StructuredArrow.asSmallUp F d) x
  rw [← classifyingSpaceMapUniversal_eq]
  change ((classifyingSpaceMapUniversal K).comp
    (classifyingSpaceMapUniversal AsSmall.up)) x = _
  rw [← classifyingSpaceMapUniversal_comp]
  rfl

/-- The canonical universe square commutes for the original structured comparison,
including its full path coordinate. -/
theorem structuredFiberComparisonUniversal_universeLift (d : D) :
    (structuredComparisonUniverseFiberHomeomorph F d : C(_, _)).comp
        (structuredFiberComparisonUniversal F d) =
      (structuredFiberComparison
        ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙
          (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D)) (AsSmall.up.obj d)).comp
        (structuredArrowUniverseHomeomorph F d : C(_, _)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · change ((classifyingSpaceMapUniversal AsSmall.up).comp
        (classifyingSpaceMapUniversal (StructuredArrow.proj d F))) x =
      ((classifyingSpaceMap (StructuredArrow.proj (AsSmall.up.obj d)
        (AsSmall.down ⋙ F ⋙ AsSmall.up))).hom.comp
          (classifyingSpaceMapUniversal (StructuredArrow.asSmallUp F d))) x
    rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_comp,
      ← classifyingSpaceMapUniversal_comp, StructuredArrow.asSmallUp_proj]
  · apply ContinuousMap.ext
    intro t
    change classifyingSpaceUniverseHomeomorph D
      (classifyingSpaceUniversalHomotopy (structuredCommaTransformationUniversal F d)
        (unitInterval.symm t, x)) = _
    rw [structuredCommaUniversalHomotopy_universeLift, Homeomorph.apply_symm_apply]
    rfl

/-- The original structured comparison is a full weak equivalence at every target
object in independent universes, under weak equivalence of its original transitions. -/
theorem structuredFiberComparisonUniversal_isWeakHomotopyEquivalence
    (h : StructuredTransitionWeakEquivalencesUniversal F) (d : D) :
    IsWeakHomotopyEquivalence (structuredFiberComparisonUniversal F d) := by
  have hc := (structuredFiberComparison_isWeakHomotopyEquivalence_of_weakTransitions
    ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙
      (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D))
      (structuredTransitionWeakEquivalences_universeLift F h) (AsSmall.up.obj d)).comp
        (isWeakHomotopyEquivalence_of_homotopyEquiv
          (structuredArrowUniverseHomeomorph F d).toHomotopyEquiv)
  change IsWeakHomotopyEquivalence
    ((structuredFiberComparison
      ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙
        (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D)) (AsSmall.up.obj d)).comp
      (structuredArrowUniverseHomeomorph F d :
        C(ClassifyingSpace (StructuredArrow d F), _))) at hc
  rw [← structuredFiberComparisonUniversal_universeLift] at hc
  exact hc.of_comp_right (isWeakHomotopyEquivalence_of_homotopyEquiv
    (structuredComparisonUniverseFiberHomeomorph F d).toHomotopyEquiv)

end TheoremB
end CategoryTheory
