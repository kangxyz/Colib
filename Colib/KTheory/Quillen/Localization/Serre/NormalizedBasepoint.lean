/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Localization.Serre.NormalizedStructuredComma
public import Colib.CategoryTheory.TheoremB.StructuredBasepoint

/-! # Exact zero identities for the normalized structured comparison

Adapted from the unconditional basepoint declarations of
`Quillen/Localization/Serre/StructuredComparisonWeak.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The conditional final bijectivity wrapper and
all localization adapter assumptions are omitted.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.ExactCategory.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

theorem quotientNormalized_obj_zero :
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ.obj (abelianExactStructure
      C).qZero =
      (abelianExactStructure P.isoModSerre.Localization).qZero := rebaseFunctor_obj_base _ _ _ _

theorem normalizedSerreToZeroStructuredComma_obj_zero :
    (normalizedSerreToZeroStructuredComma P).obj
      (abelianExactStructure P.FullSubcategory).qZero =
      StructuredArrow.mk (eqToHom (quotientNormalized_obj_zero P).symm) := by
  have hi : (ObjectProperty.exactInclusion P).normalizedQ.obj (abelianExactStructure
    P.FullSubcategory).qZero =
      (abelianExactStructure C).qZero :=
    rebaseFunctor_obj_base (Abelian.Devissage.mapQ P)
      (abelianExactStructure P.FullSubcategory).qZero (abelianExactStructure
        C).qZero
      ((abelianExactStructure C).qIsoOfIso (ObjectProperty.exactInclusion
        P).toFunctor.mapZeroObject)
  refine StructuredArrow.obj_ext _ _ hi ?_
  apply (cancel_mono (eqToHom (quotientNormalized_obj_zero P))).1
  exact ((abelianExactStructure P.isoModSerre.Localization).qHom_subsingleton_of_isZero _ _
    (isZero_zero _)).elim _ _

theorem normalizedSerreToZeroStructuredComma_map_basepoint :
    classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)
      (abelianExactStructure P.FullSubcategory).kBasepoint =
      classifyingSpacePoint (StructuredArrow.mk (eqToHom (quotientNormalized_obj_zero P).symm)) :=
  (classifyingSpaceMap_point (normalizedSerreToZeroStructuredComma P)
    (abelianExactStructure P.FullSubcategory).qZero).trans
      (congrArg classifyingSpacePoint (normalizedSerreToZeroStructuredComma_obj_zero P))

theorem normalizedStructuredFiberComparison_basepoint :
    normalizedStructuredFiberComparison P (abelianExactStructure P.FullSubcategory).kBasepoint =
      normalizedFiberBasepoint P :=
  ((normalizedStructuredFiberComparisonHomotopy P).map_one_left _).symm.trans
    (normalizedStructuredFiberComparisonHomotopy_based P 1)

end CategoryTheory.ExactCategory.SerreLocalization
