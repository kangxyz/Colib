/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Functor.QIsomorphisms
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExtension
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionQuotient
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionIsomorphism

/-!
# Compatibility of base change with the original direct-sum quotient

## Implementation provenance

Adapted from `Quillen/Algebra/Category/ModuleCat/FiniteProjectiveBaseChangeExtensionQuotient.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric inflationDirectSumAction
  rightBaseChangeMonoidal rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
variable (P : IsoCategory Rᵐᵒᵖ) (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal)

/-- The actual quotient isomorphism belonging to the extension tensorator. -/
def rightBaseChangeExtensionTensorQuotientIso :
    ((exactStructure Sᵐᵒᵖ).extensionQuotientData
      (directSumExtensionObject Sᵐᵒᵖ ((rightBaseChangeCore f).obj P)
        ((rightBaseChangeExtension f).obj x))).obj ≅
    ((exactStructure Sᵐᵒᵖ).extensionQuotientData
      ((rightBaseChangeExtension f).obj (directSumExtensionObject Rᵐᵒᵖ P x))).obj :=
  directSumExtensionQuotientIso Sᵐᵒᵖ ((rightBaseChangeCore f).obj P)
      ((rightBaseChangeExtension f).obj x) ≪≫
    ((rightBaseChangeExact f).extensionQuotientIso x).symm ≪≫
    (rightBaseChange f).mapIso (directSumExtensionQuotientIso Rᵐᵒᵖ P x).symm ≪≫
    (rightBaseChangeExact f).extensionQuotientIso (directSumExtensionObject Rᵐᵒᵖ P x)

/-- The coproduct tensorator and original quotient projections determine the same map. -/
theorem rightBaseChangeExtensionTensorQuotient_π_square :
    (rightBaseChangeTensorIso f P.of x.base.obj).hom ≫
      (rightBaseChange f).map ((exactStructure Rᵐᵒᵖ).extensionQuotientData
        (directSumExtensionObject Rᵐᵒᵖ P x)).π ≫
      (rightBaseChange f).map (directSumExtensionQuotientIso Rᵐᵒᵖ P x).hom ≫
      ((rightBaseChangeExact f).extensionQuotientIso x).hom =
    ((exactStructure Sᵐᵒᵖ).extensionQuotientData
      (directSumExtensionObject Sᵐᵒᵖ ((rightBaseChangeCore f).obj P)
        ((rightBaseChangeExtension f).obj x))).π ≫
      (directSumExtensionQuotientIso Sᵐᵒᵖ ((rightBaseChangeCore f).obj P)
        ((rightBaseChangeExtension f).obj x)).hom := by
  rw [← Functor.map_comp_assoc, directSumExtensionQuotientIso_π,
    directSumExtensionQuotientIso_π]
  apply coprod.hom_ext
  · rw [coprod.inl_desc]
    simp only [← Category.assoc, rightBaseChangeTensorIso_inl, ← Functor.map_comp,
      coprod.inl_desc, Functor.map_zero, zero_comp]
  · rw [coprod.inr_desc]
    simp only [← Category.assoc, rightBaseChangeTensorIso_inr, ← Functor.map_comp,
      coprod.inr_desc]
    exact (rightBaseChangeExact f).extensionQuotientIso_π x

/-- The canonical comparison has the exact middle-object tensorator as its quotient square. -/
theorem rightBaseChangeExtensionTensorQuotientIso_π :
    ((exactStructure Sᵐᵒᵖ).extensionQuotientData
      (directSumExtensionObject Sᵐᵒᵖ ((rightBaseChangeCore f).obj P)
        ((rightBaseChangeExtension f).obj x))).π ≫
      (rightBaseChangeExtensionTensorQuotientIso f P x).hom =
    (rightBaseChangeTensorIso f P.of x.base.obj).hom ≫
      ((exactStructure Sᵐᵒᵖ).extensionQuotientData
        ((rightBaseChangeExtension f).obj (directSumExtensionObject Rᵐᵒᵖ P x))).π := by
  let c := (rightBaseChangeExact f).extensionQuotientIso (directSumExtensionObject Rᵐᵒᵖ P x)
  let q := (rightBaseChange f).mapIso (directSumExtensionQuotientIso Rᵐᵒᵖ P x)
  let d := (rightBaseChangeExact f).extensionQuotientIso x
  let qS := directSumExtensionQuotientIso Sᵐᵒᵖ ((rightBaseChangeCore f).obj P)
    ((rightBaseChangeExtension f).obj x)
  change _ ≫ (qS.hom ≫ d.inv ≫ q.inv ≫ c.hom) = _
  have hd := rightBaseChangeExtensionTensorQuotient_π_square f P x
  change _ ≫ _ ≫ q.hom ≫ d.hom = _ ≫ qS.hom at hd
  rw [← Category.assoc, ← hd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg ((rightBaseChangeTensorIso f P.of x.base.obj).hom ≫ ·)
    ((rightBaseChangeExact f).extensionQuotientIso_π (directSumExtensionObject Rᵐᵒᵖ P x))

/-- The original Q projection of the extension lineator has its specified quotient isomorphism. -/
theorem rightBaseChangeExtensionTensorIso_projection :
    (exactStructure Sᵐᵒᵖ).extensionProjectionQMap
      (rightBaseChangeExtensionTensorIso f P x).hom =
    ((exactStructure Sᵐᵒᵖ).qIsoOfIso
      (rightBaseChangeExtensionTensorQuotientIso f P x)).hom := by
  let : Epi (Subdivision.domainMap (rightBaseChangeExtensionTensorIso f P x).hom).hom := by
    rw [rightBaseChangeExtensionTensorIso_domain]
    infer_instance
  apply (exactStructure Sᵐᵒᵖ).extensionProjectionQMap_eq_qIsoOfIso
  exact rightBaseChangeExtensionTensorQuotientIso_π f P x

private theorem qIso_symm_hom {A B : Category.{u, u} Sᵐᵒᵖ} (e : A ≅ B) :
    ((exactStructure Sᵐᵒᵖ).qIsoOfIso e.symm).hom =
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso e).inv := by
  apply (cancel_epi ((exactStructure Sᵐᵒᵖ).qIsoOfIso e).hom).1
  rw [Iso.hom_inv_id]
  have h := congrArg Iso.hom ((exactStructure Sᵐᵒᵖ).qIsoOfIso_trans e e.symm)
  simpa only [Iso.self_symm_id, CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_refl,
    Iso.refl_hom,
    Iso.trans_hom] using h.symm

/-- The actual quotient comparison intertwines the original direct-sum lineators in Q. -/
theorem rightBaseChangeExtensionProjection_lineator :
    (rightBaseChangeExact f).mapQ.map
        (((exactStructure Rᵐᵒᵖ).qIsoOfIso (directSumExtensionQuotientIso Rᵐᵒᵖ P x)).inv) ≫
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso
        ((rightBaseChangeExact f).extensionQuotientIso (directSumExtensionObject Rᵐᵒᵖ P x))).hom =
    ((exactStructure Sᵐᵒᵖ).qIsoOfIso ((rightBaseChangeExact f).extensionQuotientIso x)).hom ≫
      ((exactStructure Sᵐᵒᵖ).qIsoOfIso
        (directSumExtensionQuotientIso Sᵐᵒᵖ ((rightBaseChangeCore f).obj P)
          ((rightBaseChangeExtension f).obj x))).inv ≫
        (exactStructure Sᵐᵒᵖ).extensionProjectionQMap
          (rightBaseChangeExtensionTensorIso f P x).hom := by
  rw [rightBaseChangeExtensionTensorIso_projection]
  have hm := congrArg Iso.inv ((rightBaseChangeExact f).mapQ_qIsoOfIso
    (directSumExtensionQuotientIso Rᵐᵒᵖ P x))
  simp only [Functor.mapIso_inv] at hm
  erw [hm]
  simp only [rightBaseChangeExtensionTensorQuotientIso,
    CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_trans,
    Iso.trans_hom, Iso.inv_hom_id_assoc]
  rw [qIso_symm_hom, Iso.hom_inv_id_assoc, Functor.mapIso_symm, qIso_symm_hom]
  rfl

end ModuleCat.FiniteProjective
