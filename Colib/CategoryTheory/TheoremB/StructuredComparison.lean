/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Comma.Transitions
public import Colib.CategoryTheory.TheoremB.Conditions
public import Colib.CategoryTheory.TheoremA.Conclusion
public import Colib.Topology.ClassifyingSpace.CommaOpposite

/-!
# The structured-arrow convention for Quillen's Theorem B

The arrows in `(d ↓ F)` run from `d` to `F(x)`. Their realized homotopy is
reversed, so the path coordinate of the comparison still runs from `F(x)`
to `d`, as required by the actual path-space homotopy fiber.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredComparison.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual comma functors, realized maps
and basepoint tracks are retained. No general fiber-equivalence theorem is assumed. -/
@[expose] public section


noncomputable section
open Topology CategoryTheory Opposite
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- Reverse the structure-arrow homotopy to agree with the path-space fiber
convention `F(x) → d`. -/
def structuredCommaNullhomotopy (d : D) :
    ((classifyingSpaceMap F).hom.comp
      (classifyingSpaceMap (StructuredArrow.proj d F)).hom).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint d)) :=
  (classifyingSpaceNaturalTransformationHomotopy
    (structuredCommaTransformation F d)).symm.cast
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
    (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- The canonical structured-comma comparison, using the reversed homotopy. -/
def structuredFiberComparison (d : D) :
    C(ClassifyingSpace (StructuredArrow d F),
      HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  HomotopyFiber.lift _ _ (classifyingSpaceMap (StructuredArrow.proj d F)).hom
    (structuredCommaNullhomotopy F d)

@[simp] theorem structuredFiberComparison_projection (d : D) :
    (HomotopyFiber.projection (classifyingSpaceMap F).hom (classifyingSpacePoint d)).comp
      (structuredFiberComparison F d) = (classifyingSpaceMap (StructuredArrow.proj d F)).hom :=
  HomotopyFiber.projection_lift _ _ _ _

@[simp] theorem structuredFiberComparison_path (d : D)
    (x : ClassifyingSpace (StructuredArrow d F)) (t : unitInterval) :
    (structuredFiberComparison F d x).1.2 t = structuredCommaNullhomotopy F d (t, x) := rfl

/-- At the identity structured arrow, the comparison is the exact constant-path
basepoint of the genuine homotopy fiber. -/
@[simp] theorem structuredFiberComparison_identity (c : C) :
    structuredFiberComparison F (F.obj c)
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) =
      HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c) := by
  apply Subtype.ext
  apply Prod.ext
  · exact classifyingSpaceMap_point (StructuredArrow.proj (F.obj c) F) _
  · apply ContinuousMap.ext
    intro t
    exact (classifyingSpaceNaturalTransformationBasedHomotopy
      (structuredCommaTransformation F (F.obj c)) (StructuredArrow.mk (𝟙 (F.obj c))) rfl rfl).eq_snd
      (unitInterval.symm t) rfl |>.trans (classifyingSpaceMap_point _ _)

/-- The exact realized precomposition map. -/
def structuredTransitionMap {d e : D} (f : d ⟶ e) :
    C(ClassifyingSpace (StructuredArrow e F), ClassifyingSpace (StructuredArrow d F)) :=
  (classifyingSpaceMap (structuredTransition F f)).hom

/-- The structured convention of the actual transition-map hypothesis. -/
def StructuredTransitionHomotopyEquivalences : Prop :=
  ∀ ⦃d e : D⦄ (f : d ⟶ e), ∃ g : C(ClassifyingSpace (StructuredArrow d F),
    ClassifyingSpace (StructuredArrow e F)),
    (g.comp (structuredTransitionMap F f)).Homotopic (ContinuousMap.id _) ∧
    ((structuredTransitionMap F f).comp g).Homotopic (ContinuousMap.id _)

/-- Package the prescribed structured transition as a homotopy equivalence. -/
def structuredTransitionHomotopyEquiv (h : StructuredTransitionHomotopyEquivalences F)
    {d e : D} (f : d ⟶ e) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (StructuredArrow e F))
      (ClassifyingSpace (StructuredArrow d F)) where
  toFun := structuredTransitionMap F f
  invFun := (h f).choose
  left_inv := (h f).choose_spec.1
  right_inv := (h f).choose_spec.2

/-- This comma equivalence intertwines the actual transition maps exactly. -/
theorem structuredCommaOppositeEquiv_transition {d e : D} (f : d ⟶ e) :
    (transitionMap F.op f.op).comp (structuredCommaOppositeEquiv F e).toFun =
      (structuredCommaOppositeEquiv F d).toFun.comp (structuredTransitionMap F f) := by
  have h := congrArg classifyingSpaceMap (structuredOppositeTransition F f)
  simp only [classifyingSpaceMap_comp] at h
  have hn := classifyingOppositeIso_naturality (structuredTransition F f)
  have hi : (classifyingOppositeIso (StructuredArrow e F)).inv ≫
      classifyingSpaceMap (structuredTransition F f).op =
      classifyingSpaceMap (structuredTransition F f) ≫
        (classifyingOppositeIso (StructuredArrow d F)).inv :=
    (CommSq.vert_inv (CommSq.mk hn)).w.symm
  ext x
  change (classifyingSpaceMap (structuredArrowOpEquivalence F e).functor ≫
      classifyingSpaceMap (transition F.op f.op))
      ((classifyingOppositeIso (StructuredArrow e F)).inv x) = _
  rw [h]
  change classifyingSpaceMap (structuredArrowOpEquivalence F d).functor
    (((classifyingOppositeIso (StructuredArrow e F)).inv ≫
      classifyingSpaceMap (structuredTransition F f).op) x) = _
  rw [hi]
  rfl

/-- The structured transition hypothesis transports to the ordinary
costructured hypothesis for `F.op`, preserving each prescribed map. -/
theorem transitionHomotopyEquivalences_op_of_structured
    (h : StructuredTransitionHomotopyEquivalences F) :
    TransitionHomotopyEquivalences F.op := by
  intro d e f
  let s := structuredCommaOppositeEquiv F d.unop
  let t := (structuredTransitionHomotopyEquiv F h f.unop).trans
    (structuredCommaOppositeEquiv F e.unop)
  let E := TheoremA.homotopyEquivOfTriangle s t (transitionMap F.op f)
    (by
      change ((transitionMap F.op f.unop.op).comp
        (structuredCommaOppositeEquiv F d.unop).toFun).Homotopic
        ((structuredCommaOppositeEquiv F e.unop).toFun.comp
          (structuredTransitionMap F f.unop))
      rw [structuredCommaOppositeEquiv_transition]
      )
  exact ⟨E.invFun, E.left_inv, E.right_inv⟩

end CategoryTheory.TheoremB
