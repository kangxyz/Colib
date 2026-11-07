/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Quillen.Localization.Serre.LocalizationComma

/-! Regression checks for actual comma functors, interval models and realized forward maps. -/

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.ExactCategory.SerreLocalization
open scoped ZeroObject Topology

section General

example (A : Type u) [SemilatticeSup A] [Nonempty A] :
    ContractibleSpace (ClassifyingSpace A) :=
  classifyingSpace_contractible_of_semilatticeSup A

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
  (E : ExactStructure D)

example {X Y : E.QCategory} (f : X ⟶ Y) (hY : IsZero Y.obj.of) : IsZero X.obj.of :=
  E.isZero_source_of_qHom f hY

end General

section Serre

attribute [local instance] Abelian.hasFiniteBiproducts canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

example (X : ZeroComma P) : P X.left.obj.of := zeroComma_object_mem P X

example : (serreToZeroComma P).IsEquivalence := inferInstance

example : (zeroCommaEquivalence P).functor = serreToZeroComma P := rfl

example : serreToZeroComma P ⋙ CostructuredArrow.proj (quotientMapQ P)
    (abelianExactStructure P.isoModSerre.Localization).qZero = Abelian.Devissage.mapQ P := rfl

example (x : (abelianExactStructure P.FullSubcategory).KSpace) :
    zeroCommaClassifyingHomotopyEquiv P x = classifyingSpaceMap (serreToZeroComma P) x := rfl

example : (classifyingSpaceMap (CostructuredArrow.proj (quotientMapQ P)
    (abelianExactStructure P.isoModSerre.Localization).qZero)).hom.comp
      (classifyingSpaceMap (serreToZeroComma P)).hom =
        (classifyingSpaceMap (Abelian.Devissage.mapQ P)).hom :=
  zeroCommaClassifying_projection P

example : serreToZeroStructuredComma P ⋙ StructuredArrow.proj
    (abelianExactStructure P.isoModSerre.Localization).qZero (quotientMapQ P) =
      Abelian.Devissage.mapQ P := rfl

example (M : C) (S : Subobject (P.isoModSerre.Q.obj M)) :
    Nonempty (ZeroLayerLift P M S) := inferInstance

example (M : C) (S : Subobject (P.isoModSerre.Q.obj M)) (A B : ZeroLayerLift P M S) :
    (A ⊔ B).val.lower = A.val.lower ⊓ B.val.lower ∧
      (A ⊔ B).val.upper = A.val.upper ⊔ B.val.upper := ⟨rfl, rfl⟩

example (X : ZeroStructuredComma P) :
    (zeroStructuredFiberEquivalence P X).functor = zeroLayerToStructuredFiber P X := rfl

example (X : ZeroStructuredComma P) :
    ContractibleSpace (ClassifyingSpace (CostructuredArrow (serreToZeroStructuredComma P) X)) :=
  zeroStructuredFiber_contractible P X

example : (zeroStructuredCommaClassifyingHomotopyEquiv P).toFun =
    (classifyingSpaceMap (serreToZeroStructuredComma P)).hom := rfl

variable {V : (abelianExactStructure P.isoModSerre.Localization).QCategory}
  (X : StructuredArrow V (quotientMapQ P))

example : Nonempty (IsoFiberIntervals P X) :=
  SubobjectIntervalLift.nonempty (QConstruction.arrowLower_le_upper X.hom)

example (A : IsoFiberIntervals P X) :
    QConstruction.arrowLower (isoFiberIntervalArrow P A) = A.lower ∧
      QConstruction.arrowUpper (isoFiberIntervalArrow P A) = A.upper :=
  ⟨isoFiberIntervalArrow_lower P A, isoFiberIntervalArrow_upper P A⟩

example (A : IsoFiberIntervals P X) :
    (isoFiberIntervalSourceIso P A).hom ≫ X.hom =
      (quotientMapQ P).map (isoFiberIntervalArrow P A) :=
  isoFiberIntervalSourceIso_hom_comp P A

example (A : IsoFiberIntervals P X) :
    (isoFiberIntervalObj P A).hom.right = isoFiberIntervalArrow P A := rfl

example : (intervalToIsoStructuredFiber P X).IsEquivalence := inferInstance

example : (isoStructuredFiberEquivalence P X).functor = intervalToIsoStructuredFiber P X := rfl

example : ContractibleSpace (ClassifyingSpace (CostructuredArrow
    (isoStructuredInclusion P V) X)) := isoStructuredFiber_contractible P X

example : (isoStructuredInclusionClassifyingHomotopyEquiv P V).toFun =
    (classifyingSpaceMap (isoStructuredInclusion P V)).hom := rfl

end Serre
