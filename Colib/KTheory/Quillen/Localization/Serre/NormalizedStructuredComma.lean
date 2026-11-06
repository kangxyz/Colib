/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Quillen.Localization.Serre.NormalizedComma
public import Colib.KTheory.Quillen.Localization.Serre.StructuredTransitions
public import Colib.CategoryTheory.TheoremB.StructuredFunctorIso
public import Colib.CategoryTheory.TheoremB.StructuredIsoHomotopy
public import Colib.Topology.ClassifyingSpace.InverseHomotopy

/-! # Normalized structured comparison with based two-parameter coherence

The structured zero-comma map retains the exact normalized functors of the
canonical K-maps. Its comparison has the prescribed realized forward map, and
the full two-parameter homotopy fixes the original constant-path basepoint.
The actual quotient structured-transition theorem is used without an input hypothesis.

Adapted from `Quillen/Localization/Serre/NormalizedStructuredComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No weak-comparison transport or localization adapter is
  imported. -/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology
open scoped ZeroObject Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.ExactCategory.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The structured-arrow category of Q-arrows from the quotient Q-zero object to the image of
the normalized quotient functor. -/
abbrev NormalizedZeroStructuredComma :=
  StructuredArrow ((abelianExactStructure
    P.isoModSerre.Localization)).qZero (ExactFunctor.serreLocalization P
      P.isoModSerre.Q).normalizedQ

/-- The functor from the Serre subcategory Q-category to the normalized structured zero-comma
category, using the inverse of the natural zero comparison as its structure arrow. -/
def normalizedSerreToZeroStructuredComma :
    (abelianExactStructure P.FullSubcategory).QCategory ⥤
      NormalizedZeroStructuredComma P :=
  (ObjectProperty.exactInclusion P).normalizedQ.toStructuredArrow _ (ExactFunctor.serreLocalization
    P P.isoModSerre.Q).normalizedQ
    (fun X ↦ (normalizedQuotientInclusionZeroIso P).inv.app X)
    (fun f ↦ by simpa using ((normalizedQuotientInclusionZeroIso P).inv.naturality f).symm)

/-- The natural isomorphism comparing the raw structured zero-comma inclusion, transported along
the quotient normalization, with `normalizedSerreToZeroStructuredComma P`. -/
def normalizedSerreToZeroStructuredCommaIso :
    serreToZeroStructuredComma P ⋙ (StructuredArrow.mapNatIso
      (S := ((abelianExactStructure
        P.isoModSerre.Localization)).qZero) (quotientNormalizedIso
        P)).functor ≅
      normalizedSerreToZeroStructuredComma P :=
  NatIso.ofComponents (fun X ↦ StructuredArrow.isoMk ((inclusionNormalizedIso P).app X)
    (by
      apply (cancel_mono ((normalizedQuotientInclusionZeroIso P).hom.app X)).1
      exact (((abelianExactStructure
        P.isoModSerre.Localization)).qHom_subsingleton_of_isZero _ _
        (isZero_zero _)).elim _ _)) (by
    intro X Y f
    apply StructuredArrow.hom_ext
    exact (inclusionNormalizedIso P).hom.naturality f)

/-- The already proved raw structured inclusion transports by actual natural
isomorphisms, retaining the normalized inclusion as its forward map. -/
def normalizedZeroStructuredCommaClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (abelianExactStructure P.FullSubcategory).KSpace
      (ClassifyingSpace (NormalizedZeroStructuredComma P)) :=
  TheoremA.homotopyEquivWithMap
    ((zeroStructuredCommaClassifyingHomotopyEquiv P).trans
      (equivalenceClassifyingHomotopyEquiv (StructuredArrow.mapNatIso
        (S := ((abelianExactStructure
          P.isoModSerre.Localization)).qZero) (quotientNormalizedIso
          P))))
    (classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)).hom
    (by
      have H := classifyingSpaceNaturalTransformationHomotopy
        (normalizedSerreToZeroStructuredCommaIso P).inv
      exact ⟨H.cast rfl (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)⟩)

@[simp] theorem normalizedZeroStructuredCommaClassifyingHomotopyEquiv_toFun :
    (normalizedZeroStructuredCommaClassifyingHomotopyEquiv P).toFun =
      (classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)).hom := rfl

@[simp] theorem normalizedSerreToZeroStructuredComma_projection :
    normalizedSerreToZeroStructuredComma P ⋙ StructuredArrow.proj
      (abelianExactStructure P.isoModSerre.Localization).qZero
        (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ =
        (ObjectProperty.exactInclusion P).normalizedQ := rfl

@[simp] theorem normalizedSerreToZeroStructuredComma_transformation :
    Functor.whiskerLeft (normalizedSerreToZeroStructuredComma P)
      (TheoremB.structuredCommaTransformation (ExactFunctor.serreLocalization P
        P.isoModSerre.Q).normalizedQ
        (abelianExactStructure P.isoModSerre.Localization).qZero) =
          (normalizedQuotientInclusionZeroIso P).inv := rfl

/-- The source-zero route uses precisely the reversed inverse of the
normalized natural isomorphism, not a separately chosen nullhomotopy. -/
theorem normalizedSerreToZeroStructuredComma_nullhomotopy (t : unitInterval)
    (x : (abelianExactStructure P.FullSubcategory).KSpace) :
    TheoremB.structuredCommaNullhomotopy (ExactFunctor.serreLocalization P
      P.isoModSerre.Q).normalizedQ
      (abelianExactStructure P.isoModSerre.Localization).qZero
      (t, classifyingSpaceMap (normalizedSerreToZeroStructuredComma P) x) =
      TheoremB.naturalIsoInverseNullhomotopy (ObjectProperty.exactInclusion P).normalizedQ
        (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ ((abelianExactStructure
          P.isoModSerre.Localization)).qZero
        (normalizedQuotientInclusionZeroIso P) (t, x) := by
  change classifyingSpaceNaturalTransformationHomotopy
    (TheoremB.structuredCommaTransformation (ExactFunctor.serreLocalization P
      P.isoModSerre.Q).normalizedQ
      (abelianExactStructure P.isoModSerre.Localization).qZero)
    (unitInterval.symm t, classifyingSpaceMap (normalizedSerreToZeroStructuredComma P) x) =
    classifyingSpaceNaturalTransformationHomotopy (normalizedQuotientInclusionZeroIso P).inv
      (unitInterval.symm t, x)
  rw [← classifyingSpaceNaturalTransformationHomotopy_whiskerLeft,
    normalizedSerreToZeroStructuredComma_transformation]

/-- Every transition of the actual normalized quotient functor is a homotopy equivalence. -/
theorem normalizedQuotient_structuredTransitions :
    TheoremB.StructuredTransitionHomotopyEquivalences (ExactFunctor.serreLocalization P
      P.isoModSerre.Q).normalizedQ :=
  TheoremB.structuredTransitionHomotopyEquivalences_of_natIso (quotientNormalizedIso P)
    (quotientStructuredTransitionHomotopyEquivalences P)

/-- The complete normalized structured comparison into the actual fiber. -/
def normalizedStructuredFiberComparison :
    C((abelianExactStructure P.FullSubcategory).KSpace,
      NormalizedLocalizationFiber P) :=
  (TheoremB.structuredFiberComparison (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
    (abelianExactStructure P.isoModSerre.Localization).qZero).comp
      (classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)).hom

theorem normalizedStructuredFiberComparison_eq_lift :
    normalizedStructuredFiberComparison P =
      HomotopyFiber.lift (classifyingSpaceMap (ExactFunctor.serreLocalization P
        P.isoModSerre.Q).normalizedQ).hom
        (abelianExactStructure P.isoModSerre.Localization).kBasepoint
        (classifyingSpaceMap (ObjectProperty.exactInclusion P).normalizedQ).hom
        (TheoremB.naturalIsoInverseNullhomotopy (ObjectProperty.exactInclusion P).normalizedQ
          (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ ((abelianExactStructure
            P.isoModSerre.Localization)).qZero
          (normalizedQuotientInclusionZeroIso P)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact ConcreteCategory.congr_hom
      (classifyingSpaceMap_comp (normalizedSerreToZeroStructuredComma P)
        (StructuredArrow.proj ((abelianExactStructure
          P.isoModSerre.Localization)).qZero
          (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ)).symm x
  · apply ContinuousMap.ext
    intro t
    exact normalizedSerreToZeroStructuredComma_nullhomotopy P t x

/-- Actual two-parameter coherence connects the chosen direct nullhomotopy
with the normalized structured-comma comparison. -/
def normalizedStructuredFiberComparisonHomotopy :
    (basedLocalizationFiberComparison P).Homotopy (normalizedStructuredFiberComparison P) :=
  (TheoremB.naturalIsoFiberLiftHomotopy (ObjectProperty.exactInclusion P).normalizedQ
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ ((abelianExactStructure
      P.isoModSerre.Localization)).qZero
    (normalizedQuotientInclusionZeroIso P)).cast rfl
      (normalizedStructuredFiberComparison_eq_lift P).symm

/-- The full comparison homotopy leaves the actual inclusion source coordinate fixed. -/
@[simp]
theorem normalizedStructuredFiberComparisonHomotopy_projection (s : unitInterval)
    (x : (abelianExactStructure P.FullSubcategory).KSpace) :
    (normalizedStructuredFiberComparisonHomotopy P (s, x)).1.1 =
      classifyingSpaceMap (ObjectProperty.exactInclusion P).normalizedQ x := rfl

/-- Its full path coordinate is exactly the inverse-isomorphism two-simplex coherence. -/
@[simp]
theorem normalizedStructuredFiberComparisonHomotopy_path (s t : unitInterval)
    (x : (abelianExactStructure P.FullSubcategory).KSpace) :
    (normalizedStructuredFiberComparisonHomotopy P (s, x)).1.2 t =
      naturalIsoInverseHomotopy (normalizedQuotientInclusionZeroIso P).symm (s, (t, x)) := rfl

/-- The coherence fixes the original zero basepoint at every time, not merely
its source coordinate or the endpoints of its path coordinate. -/
theorem normalizedStructuredFiberComparisonHomotopy_based (s : unitInterval) :
    normalizedStructuredFiberComparisonHomotopy P
      (s, (abelianExactStructure P.FullSubcategory).kBasepoint) =
        normalizedFiberBasepoint P := by
  apply Subtype.ext
  apply Prod.ext
  · exact (ObjectProperty.exactInclusion P).normalizedQ_map_point
  · apply ContinuousMap.ext
    intro t
    exact naturalIsoInverseHomotopy_vertex_of_subsingleton
      (normalizedQuotientInclusionZeroIso P).symm
      (abelianExactStructure P.FullSubcategory).qZero
        ((abelianExactStructure
        P.isoModSerre.Localization)).qZero
      rfl (normalizedComposite_obj_zero P)
      (fun Y ↦ ((abelianExactStructure
        P.isoModSerre.Localization)).qHom_subsingleton_of_isZero
        _ _ (isZero_zero _)) s t

end CategoryTheory.ExactCategory.SerreLocalization
