/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.ImageQuotientExact
public import Colib.KTheory.Waldhausen.Cofinality.ImageReflection
public import Colib.KTheory.Waldhausen.Cofinality.GeneralDenseKZero

/-! # Original objects and maps in the Waldhausen K-zero presentation -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
universe u v

namespace ColibTest.WaldhausenGrothendieck

section Small
variable {C : Type u} [SmallCategory C] (W : Structure C)

example : (grothendieckKZeroEquiv W : Multiplicative (AlgebraicGrothendieck.Group W) →*
    W.K 0) = grothendieckToKZero W := rfl

example : ((grothendieckKZeroEquiv W).symm : W.K 0 →*
    Multiplicative (AlgebraicGrothendieck.Group W)) = kZeroToGrothendieck W := rfl

example : grothendieckKZeroEquivOfAsSmall W = grothendieckKZeroEquiv W :=
  grothendieckKZeroEquivOfAsSmall_eq W
end Small

section General
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) {V : Structure D} (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

example (A : C) : objectClass W A =
    QuotientAddGroup.mk' (relations W) (FreeAbelianGroup.of A) := rfl

example (A : C) :
    grothendieckKZeroEquivOfAsSmall W (Multiplicative.ofAdd (objectClass W A)) =
      W.kZeroObjectClass A := grothendieckKZeroEquivOfAsSmall_objectClass W A

example (A : C) : KMap hF 0 (W.kZeroObjectClass A) = V.kZeroObjectClass (F.obj A) :=
  KMap_kZeroObjectClass hF A

example (A : D) : (imageQuotientGrading W F hF).value A =
    QuotientAddGroup.mk' (map W F hF).range (objectClass V A) := rfl

example : ApproximationImage.corestrict V F ⋙ (ApproximationImage.objects V F).ι = F := rfl

variable (T : FunctorialFactorization V.asSmall)

example : ((imageQuotientGrading W F hF).coarseKZeroValueMap T).comp
    (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0) =
      (QuotientAddGroup.mk' (map W F hF).range).toMultiplicative.comp
        (grothendieckKZeroEquivOfAsSmall V).symm.toMonoidHom :=
  imageQuotientKZeroMap_eq W F hF T

example : (KMap hF 0).range =
    (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0).ker ∧
    Function.Surjective
      (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0) :=
  ⟨imageQuotient_changeWeakKMap_range_ker W F hF T,
    imageQuotient_changeWeakKMap_surjective W F hF T⟩
end General

section Dense
variable {C : Type u} [Category.{v} C] {W : Structure C}
  [CategoryTheory.Limits.HasBinaryCoproducts C] {P : ObjectProperty C}
  (h : Cofinality.DenseCofiberData W P)
  (D : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))
  (hs : Fibration.RowFactorization.SecondEndpointSection (Fibration.NestedWeakEquivalences.refl W) D)

example : (h.coarseClassKZeroEquiv D : h.grading.coarseStructure.K 0 →*
    Multiplicative h.Classes) = h.coarseClassKZeroMap D := rfl

example (A : C) : h.classKZeroMapGeneral D (W.kZeroObjectClass A) =
    Multiplicative.ofAdd (h.classOf A) := h.classKZeroMapGeneral_objectClass D A

example : Function.Injective (KMap h.inclusion_exact 0) ∧
    (KMap h.inclusion_exact 0).range = (h.classKZeroMapGeneral D).ker ∧
    Function.Surjective (h.classKZeroMapGeneral D) := h.classKZero_exact_general D hs
end Dense

end ColibTest.WaldhausenGrothendieck
