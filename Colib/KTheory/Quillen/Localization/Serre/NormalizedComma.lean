/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Quillen.Localization.Serre.LocalizationComma
public import Colib.KTheory.Quillen.Localization.Serre.BasedFiberComparison
public import Colib.CategoryTheory.TheoremB.Comparison
public import Colib.Topology.ClassifyingSpace.Naturality

/-! # The actual normalized zero-comma comparison

The categorical equivalence and its exact full-path fiber comparison use the
normalized Q-functors of the native exact inclusion and quotient, not adapters.

Adapted from `Quillen/Localization/Serre/NormalizedComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The final conditional ordinary-transition wrapper is not
  ported. -/
@[expose] public section

open CategoryTheory.ExactCategory

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

/-- The canonical natural isomorphism from the raw quotient to its zero normalization. -/
def quotientNormalizedIso : quotientMapQ P ≅ (ExactFunctor.serreLocalization P
  P.isoModSerre.Q).normalizedQ :=
  rebaseFunctorIso (quotientMapQ P) (abelianExactStructure C).qZero
    (abelianExactStructure P.isoModSerre.Localization).qZero
    ((abelianExactStructure P.isoModSerre.Localization).qIsoOfIso
      ((ExactFunctor.serreLocalization P
      P.isoModSerre.Q)).toFunctor.mapZeroObject)

/-- The canonical natural isomorphism from the raw inclusion to its zero normalization. -/
def inclusionNormalizedIso : Abelian.Devissage.mapQ P ≅ (ObjectProperty.exactInclusion
  P).normalizedQ :=
  rebaseFunctorIso (Abelian.Devissage.mapQ P) (abelianExactStructure P.FullSubcategory).qZero
    (abelianExactStructure C).qZero
    ((abelianExactStructure C).qIsoOfIso (ObjectProperty.exactInclusion
      P).toFunctor.mapZeroObject)

/-- The costructured-arrow category of Q-arrows from the image of the normalized quotient
functor to the quotient Q-zero object. -/
abbrev NormalizedZeroComma :=
  CostructuredArrow (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
    ((abelianExactStructure
    P.isoModSerre.Localization)).qZero

/-- The normalized nullhomotopy determines the exact normalized zero-comma comparison. -/
def normalizedSerreToZeroComma :
    (abelianExactStructure P.FullSubcategory).QCategory ⥤ NormalizedZeroComma P :=
  (ObjectProperty.exactInclusion P).normalizedQ.toCostructuredArrow (ExactFunctor.serreLocalization
    P P.isoModSerre.Q).normalizedQ _
    (fun X ↦ (normalizedQuotientInclusionZeroIso P).hom.app X)
    (fun f ↦ by simpa using (normalizedQuotientInclusionZeroIso P).hom.naturality f)

/-- Normalization transports the previously proved equivalence by actual
natural isomorphisms, retaining the normalized structure arrows. -/
def normalizedSerreToZeroCommaIso :
    serreToZeroComma P ⋙ (CostructuredArrow.mapNatIso
      (T := (abelianExactStructure P.isoModSerre.Localization).qZero) (quotientNormalizedIso
        P)).functor ≅
      normalizedSerreToZeroComma P :=
  NatIso.ofComponents (fun X ↦ CostructuredArrow.isoMk ((inclusionNormalizedIso P).app X)
    (by exact ((abelianExactStructure P.isoModSerre.Localization).qHom_subsingleton_of_isZero _ _
      (isZero_zero _)).elim _ _)) (by
    intro X Y f
    apply CostructuredArrow.hom_ext
    exact (inclusionNormalizedIso P).hom.naturality f)

instance normalizedSerreToZeroComma_isEquivalence :
    (normalizedSerreToZeroComma P).IsEquivalence :=
  Functor.isEquivalence_of_iso (normalizedSerreToZeroCommaIso P)

/-- The normalized Serre comparison is a genuine categorical equivalence. -/
def normalizedZeroCommaEquivalence :
    (abelianExactStructure P.FullSubcategory).QCategory ≌ NormalizedZeroComma P :=
  (normalizedSerreToZeroComma P).asEquivalence

/-- Its actual realized homotopy equivalence uses exactly the normalized comparison. -/
def normalizedZeroCommaClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (abelianExactStructure P.FullSubcategory).KSpace
      (ClassifyingSpace (NormalizedZeroComma P)) :=
  equivalenceClassifyingHomotopyEquiv (normalizedZeroCommaEquivalence P)

@[simp] theorem normalizedZeroCommaClassifyingHomotopyEquiv_toFun :
    (normalizedZeroCommaClassifyingHomotopyEquiv P).toFun =
      (classifyingSpaceMap (normalizedSerreToZeroComma P)).hom := rfl

@[simp] theorem normalizedSerreToZeroComma_projection :
    normalizedSerreToZeroComma P ⋙ CostructuredArrow.proj (ExactFunctor.serreLocalization P
      P.isoModSerre.Q).normalizedQ
      (abelianExactStructure P.isoModSerre.Localization).qZero = (ObjectProperty.exactInclusion
        P).normalizedQ := rfl

@[simp] theorem normalizedSerreToZeroComma_transformation :
    Functor.whiskerLeft (normalizedSerreToZeroComma P)
      (TheoremB.commaTransformation (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
        ((abelianExactStructure
        P.isoModSerre.Localization)).qZero) =
      (normalizedQuotientInclusionZeroIso P).hom := rfl

/-- The complete normalized comma homotopy is the already-chosen based
localization nullhomotopy, including every value of its path coordinate. -/
theorem normalizedSerreToZeroComma_nullhomotopy (t : unitInterval)
    (x : (abelianExactStructure P.FullSubcategory).KSpace) :
    TheoremB.commaNullhomotopy (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
      ((abelianExactStructure
      P.isoModSerre.Localization)).qZero
      (t, classifyingSpaceMap (normalizedSerreToZeroComma P) x) =
      normalizedQuotientInclusionHomotopy P (t, x) := by
  change classifyingSpaceNaturalTransformationHomotopy
    (TheoremB.commaTransformation (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
      ((abelianExactStructure
      P.isoModSerre.Localization)).qZero)
    (t, classifyingSpaceMap (normalizedSerreToZeroComma P) x) =
    classifyingSpaceNaturalTransformationHomotopy (normalizedQuotientInclusionZeroIso P).hom (t, x)
  rw [← classifyingSpaceNaturalTransformationHomotopy_whiskerLeft,
    normalizedSerreToZeroComma_transformation]

/-- The normalized zero-comma route gives exactly the existing based fiber
comparison, not merely some homotopic map into the same unbased fiber. -/
theorem normalizedSerreToZeroComma_fiberComparison :
    (TheoremB.fiberComparison (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
      ((abelianExactStructure
      P.isoModSerre.Localization)).qZero).comp
      (classifyingSpaceMap (normalizedSerreToZeroComma P)).hom =
      basedLocalizationFiberComparison P := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · change classifyingSpaceMap (CostructuredArrow.proj (ExactFunctor.serreLocalization P
    P.isoModSerre.Q).normalizedQ
        (abelianExactStructure P.isoModSerre.Localization).qZero) (classifyingSpaceMap
          (normalizedSerreToZeroComma P) x) =
      classifyingSpaceMap (ObjectProperty.exactInclusion P).normalizedQ x
    have h := classifyingSpaceMap_comp (normalizedSerreToZeroComma P)
      (CostructuredArrow.proj (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
        ((abelianExactStructure
        P.isoModSerre.Localization)).qZero)
    exact ConcreteCategory.congr_hom h.symm x
  · apply ContinuousMap.ext
    intro t
    exact normalizedSerreToZeroComma_nullhomotopy P t x

end CategoryTheory.ExactCategory.SerreLocalization
