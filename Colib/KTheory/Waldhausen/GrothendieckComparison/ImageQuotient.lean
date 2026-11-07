/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Cofinality.GeneralKZeroValue
public import Colib.KTheory.Waldhausen.GrothendieckGroup.Image

/-!
# The original image quotient is the actual coarse K-zero obstruction

The unchanged change-of-weak-equivalences KMap and the actual realized grading
map agree with the quotient by the original algebraic image, after the genuine
original Grothendieck K-zero comparison. Range inclusion and universe lowering
remain explicit in `coarseKZeroValueMap`.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/ImageQuotient.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u v
namespace CategoryTheory.Waldhausen.AlgebraicGrothendieck
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) {V : Structure D} (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Extending the original image-quotient object grading is the literal quotient map. -/
theorem lift_imageQuotientGrading :
    lift V (imageQuotientGrading W F hF) = QuotientAddGroup.mk' (map W F hF).range := by
  apply hom_ext V
  intro A
  exact lift_objectClass V (imageQuotientGrading W F hF) A

variable (T : FunctorialFactorization V.asSmall)

/-- The actual coarse object class retains the original Laurent or other target object grade. -/
theorem imageQuotient_coarseKZeroValueMap_objectClass (A : D) :
    (imageQuotientGrading W F hF).coarseKZeroValueMap T
      ((imageQuotientGrading W F hF).coarseStructure.kZeroObjectClass A) =
        Multiplicative.ofAdd
          (QuotientAddGroup.mk' (map W F hF).range (objectClass V A)) :=
  (imageQuotientGrading W F hF).coarseKZeroValueMap_objectClass T A

/-- On every original target K-zero class, the unchanged coarse obstruction equals the
original image quotient after the inverse of the genuine Grothendieck comparison. -/
@[colib_tag "COL-0270", colib_ref "ThomasonTrobaugh1990"
  "Sections 1.5.6-1.5.7, p. 261; Theorem 1.10.1, pp. 275-277" "adaptation"
  "The coarse K-zero obstruction is the actual exact-functor image quotient, with \
    the unchanged changeWeak KMap and explicit target factorization"]
theorem imageQuotientKZeroMap_eq :
    ((imageQuotientGrading W F hF).coarseKZeroValueMap T).comp
      (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0) =
        (QuotientAddGroup.mk' (map W F hF).range).toMultiplicative.comp
          (grothendieckKZeroEquivOfAsSmall V).symm.toMonoidHom := by
  rw [(imageQuotientGrading W F hF).coarseKZeroValueMap_comp_changeWeak T,
    lift_imageQuotientGrading]

/-- The same original coarse value map is bijective for the actual image quotient. -/
@[colib_tag "COL-0270"]
theorem imageQuotient_coarseKZeroValueMap_bijective :
    Function.Bijective ((imageQuotientGrading W F hF).coarseKZeroValueMap T) := by
  refine ⟨(imageQuotientGrading W F hF).coarseKZeroValueMap_injective T, ?_⟩
  intro a
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective (map W F hF).range a.toAdd
  refine ⟨KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0
    (grothendieckKZeroEquivOfAsSmall V (Multiplicative.ofAdd x)), ?_⟩
  have he := DFunLike.congr_fun (imageQuotientKZeroMap_eq W F hF T)
    (grothendieckKZeroEquivOfAsSmall V (Multiplicative.ofAdd x))
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    MulEquiv.symm_apply_apply] at he
  exact he.trans (congrArg Multiplicative.ofAdd hx)

/-- The original target object loop has its exact quotient class after the actual KMap. -/
theorem imageQuotientKZeroMap_objectClass (A : D) :
    (imageQuotientGrading W F hF).coarseKZeroValueMap T
      (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0
        (V.kZeroObjectClass A)) =
      Multiplicative.ofAdd
        (QuotientAddGroup.mk' (map W F hF).range (objectClass V A)) := by
  rw [KMap_kZeroObjectClass]
  exact imageQuotient_coarseKZeroValueMap_objectClass W F hF T A

end CategoryTheory.Waldhausen.AlgebraicGrothendieck
