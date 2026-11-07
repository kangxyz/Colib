/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.ImageQuotient

/-!
# Exactness of the unchanged image-quotient changeWeak K-map

The actual coarse value map is injective and its original composite is the
literal image quotient. Consequently the original exact-functor image is
precisely the kernel of the unchanged changeWeak KMap, and that KMap is
surjective. No additional localization-fibration hypothesis is supplied.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/ImageQuotientExact.lean`
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
  (T : FunctorialFactorization V.asSmall)

include T

/-- The original exact-functor image is the kernel of the same actual changeWeak KMap. -/
@[colib_tag "COL-0270"]
theorem imageQuotient_changeWeakKMap_range_ker :
    (KMap hF 0).range =
      (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0).ker := by
  let d := imageQuotientGrading W F hF
  let g := KMap (Fibration.changeWeak_exact d.nested) 0
  let c := d.coarseKZeroValueMap T
  have hq (x : V.K 0) : c (g x) =
      (QuotientAddGroup.mk' (map W F hF).range).toMultiplicative
        ((grothendieckKZeroEquivOfAsSmall V).symm x) :=
    DFunLike.congr_fun (imageQuotientKZeroMap_eq W F hF T) x
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change g (KMap hF 0 a) = 1
    apply d.coarseKZeroValueMap_injective T
    have hz : (QuotientAddGroup.mk' (map W F hF).range).toMultiplicative
        ((grothendieckKZeroEquivOfAsSmall V).symm (KMap hF 0 a)) = 1 := by
      rw [grothendieckKZeroEquivOfAsSmall_symm_natural W V F hF]
      apply congrArg Multiplicative.ofAdd
      exact (QuotientAddGroup.eq_zero_iff _).mpr
        ⟨((grothendieckKZeroEquivOfAsSmall W).symm a).toAdd, rfl⟩
    exact (hq (KMap hF 0 a)).trans (hz.trans (map_one c).symm)
  · intro hx
    change g x = 1 at hx
    have hz : QuotientAddGroup.mk' (map W F hF).range
        ((grothendieckKZeroEquivOfAsSmall V).symm x).toAdd = 0 := by
      have he := (hq x).symm.trans ((congrArg c hx).trans (map_one c))
      exact congrArg Multiplicative.toAdd he
    obtain ⟨a, ha⟩ := (QuotientAddGroup.eq_zero_iff _).mp hz
    refine ⟨grothendieckKZeroEquivOfAsSmall W (Multiplicative.ofAdd a), ?_⟩
    apply (grothendieckKZeroEquivOfAsSmall V).symm.injective
    rw [grothendieckKZeroEquivOfAsSmall_symm_natural W V F hF,
      MulEquiv.symm_apply_apply]
    exact congrArg Multiplicative.ofAdd ha

/-- Every original coarse K-zero class has a preimage under the unchanged changeWeak map. -/
@[colib_tag "COL-0270"]
theorem imageQuotient_changeWeakKMap_surjective :
    Function.Surjective
      (KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0) := by
  let d := imageQuotientGrading W F hF
  let c := d.coarseKZeroValueMap T
  intro y
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (map W F hF).range (c y).toAdd
  refine ⟨grothendieckKZeroEquivOfAsSmall V (Multiplicative.ofAdd a), ?_⟩
  apply d.coarseKZeroValueMap_injective T
  have he := DFunLike.congr_fun (imageQuotientKZeroMap_eq W F hF T)
    (grothendieckKZeroEquivOfAsSmall V (Multiplicative.ofAdd a))
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    MulEquiv.symm_apply_apply] at he
  exact he.trans (congrArg Multiplicative.ofAdd ha)

end CategoryTheory.Waldhausen.AlgebraicGrothendieck
