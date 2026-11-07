/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Quillen.Localization.Serre.NormalizedBasepoint

/-! Exact-map, full-path and original-basepoint regressions for Serre normalization. -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology
open CategoryTheory.ExactCategory.SerreLocalization
open scoped ZeroObject Topology

section Identity

variable {A B : Type u} [SmallCategory A] [SmallCategory B] (F : A ⥤ B)

example (a : A) (b : B) (h : F.obj a = b) :
    TheoremB.structuredFiberComparison F b
      (classifyingSpacePoint (StructuredArrow.mk (eqToHom h.symm))) =
      HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint b)
        (classifyingSpacePoint a)
        ((classifyingSpaceMap_point F a).trans (congrArg classifyingSpacePoint h)) :=
  TheoremB.structuredFiberComparison_identity_of_eq F a b h

end Identity

section Serre

attribute [local instance] Abelian.hasFiniteBiproducts canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

example : quotientMapQ P ≅ (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ :=
  quotientNormalizedIso P

example : Abelian.Devissage.mapQ P ≅ (ObjectProperty.exactInclusion P).normalizedQ :=
  inclusionNormalizedIso P

example : (normalizedSerreToZeroComma P).IsEquivalence := inferInstance

example : (normalizedZeroCommaEquivalence P).functor = normalizedSerreToZeroComma P := rfl

example : (normalizedZeroCommaClassifyingHomotopyEquiv P).toFun =
    (classifyingSpaceMap (normalizedSerreToZeroComma P)).hom := rfl

example : normalizedSerreToZeroComma P ⋙
    CostructuredArrow.proj (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
      (abelianExactStructure P.isoModSerre.Localization).qZero =
        (ObjectProperty.exactInclusion P).normalizedQ := rfl

example (x : (abelianExactStructure P.FullSubcategory).KSpace) (t : unitInterval) :
    (TheoremB.fiberComparison (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
      (abelianExactStructure P.isoModSerre.Localization).qZero
        (classifyingSpaceMap (normalizedSerreToZeroComma P) x)).1.2 t =
          normalizedQuotientInclusionHomotopy P (t, x) :=
  normalizedSerreToZeroComma_nullhomotopy P t x

example : (TheoremB.fiberComparison
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
    (abelianExactStructure P.isoModSerre.Localization).qZero).comp
      (classifyingSpaceMap (normalizedSerreToZeroComma P)).hom =
        basedLocalizationFiberComparison P :=
  normalizedSerreToZeroComma_fiberComparison P

example : (normalizedZeroStructuredCommaClassifyingHomotopyEquiv P).toFun =
    (classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)).hom := rfl

example : normalizedSerreToZeroStructuredComma P ⋙
    StructuredArrow.proj (abelianExactStructure P.isoModSerre.Localization).qZero
      (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ =
        (ObjectProperty.exactInclusion P).normalizedQ := rfl

example (x : (abelianExactStructure P.FullSubcategory).KSpace) (t : unitInterval) :
    (normalizedStructuredFiberComparison P x).1.2 t =
      TheoremB.naturalIsoInverseNullhomotopy (ObjectProperty.exactInclusion P).normalizedQ
        (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
        (abelianExactStructure P.isoModSerre.Localization).qZero
        (normalizedQuotientInclusionZeroIso P) (t, x) :=
  normalizedSerreToZeroStructuredComma_nullhomotopy P t x

example : TheoremB.StructuredTransitionHomotopyEquivalences
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ :=
  normalizedQuotient_structuredTransitions P

example (x : (abelianExactStructure P.FullSubcategory).KSpace) :
    normalizedStructuredFiberComparisonHomotopy P (0, x) =
      basedLocalizationFiberComparison P x :=
  (normalizedStructuredFiberComparisonHomotopy P).map_zero_left x

example (x : (abelianExactStructure P.FullSubcategory).KSpace) :
    normalizedStructuredFiberComparisonHomotopy P (1, x) =
      normalizedStructuredFiberComparison P x :=
  (normalizedStructuredFiberComparisonHomotopy P).map_one_left x

example (s : unitInterval) (x : (abelianExactStructure P.FullSubcategory).KSpace) :
    (normalizedStructuredFiberComparisonHomotopy P (s, x)).1.1 =
      classifyingSpaceMap (ObjectProperty.exactInclusion P).normalizedQ x :=
  normalizedStructuredFiberComparisonHomotopy_projection P s x

example (s t : unitInterval) (x : (abelianExactStructure P.FullSubcategory).KSpace) :
    (normalizedStructuredFiberComparisonHomotopy P (s, x)).1.2 t =
      naturalIsoInverseHomotopy (normalizedQuotientInclusionZeroIso P).symm (s, (t, x)) :=
  normalizedStructuredFiberComparisonHomotopy_path P s t x

example (s t : unitInterval) :
    (normalizedStructuredFiberComparisonHomotopy P
      (s, (abelianExactStructure P.FullSubcategory).kBasepoint)).1.2 t =
        (abelianExactStructure P.isoModSerre.Localization).kBasepoint := by
  rw [normalizedStructuredFiberComparisonHomotopy_based]
  rfl

example (s : unitInterval) :
    normalizedStructuredFiberComparisonHomotopy P
      (s, (abelianExactStructure P.FullSubcategory).kBasepoint) = normalizedFiberBasepoint P :=
  normalizedStructuredFiberComparisonHomotopy_based P s

example : (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ.obj
    (abelianExactStructure C).qZero =
      (abelianExactStructure P.isoModSerre.Localization).qZero := quotientNormalized_obj_zero P

example : (normalizedSerreToZeroStructuredComma P).obj
    (abelianExactStructure P.FullSubcategory).qZero =
      StructuredArrow.mk (eqToHom (quotientNormalized_obj_zero P).symm) :=
  normalizedSerreToZeroStructuredComma_obj_zero P

example : classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)
    (abelianExactStructure P.FullSubcategory).kBasepoint =
      classifyingSpacePoint (StructuredArrow.mk (eqToHom (quotientNormalized_obj_zero P).symm)) :=
  normalizedSerreToZeroStructuredComma_map_basepoint P

example : normalizedStructuredFiberComparison P
    (abelianExactStructure P.FullSubcategory).kBasepoint = normalizedFiberBasepoint P :=
  normalizedStructuredFiberComparison_basepoint P

end Serre
