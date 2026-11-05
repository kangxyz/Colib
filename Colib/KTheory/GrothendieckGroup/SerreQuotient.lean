/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.GrothendieckGroup.SerreLocalization

/-!
# Algebraic K₀ of the canonical Serre quotient

These specializations retain the source restriction that the hom and object
universes of the source category coincide. The abelian instance on the quotient
is the upstream construction, used locally rather than installed globally.

Adapted from the canonical sections of Quillen's
`Localization/Serre/Localization.lean` and `Localization/Serre/GrothendieckExactness.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, and its
`Quillen/Aglib/CategoryTheory/Abelian/SerreClass/Annihilation.lean` instance.
-/

@[expose] public noncomputable section

universe u

namespace CategoryTheory.ExactCategory.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The upstream abelian structure on the actual canonical quotient. -/
@[instance_reducible]
local instance canonicalQuotientAbelian
    {C : Type u} [Category.{u} C] [Abelian C]
    (P : ObjectProperty C) [P.IsSerreClass] :
    Abelian P.isoModSerre.Localization :=
  ObjectProperty.SerreClassLocalization.abelian P.isoModSerre.Q P

variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The canonical quotient annihilates exactly the objects in the Serre class. -/
lemma quotient_isZero_obj_iff (X : C) : Limits.IsZero (P.isoModSerre.Q.obj X) ↔ P X :=
  ObjectProperty.SerreClassLocalization.isZero_obj_iff P.isoModSerre.Q P X

/-- The map induced by the actual canonical localization functor. -/
def quotientGrothendieckMap :
    (abelianExactStructure C).GrothendieckGroup →+
      (abelianExactStructure P.isoModSerre.Localization).GrothendieckGroup :=
  grothendieckMap P P.isoModSerre.Q

lemma quotientGrothendieckMap_class_eq_zero {X : C} (hX : P X) :
    quotientGrothendieckMap P ((abelianExactStructure C).grothendieckClass X) = 0 :=
  grothendieckMap_class_eq_zero P P.isoModSerre.Q hX

theorem quotientGrothendieckMap_surjective :
    Function.Surjective (quotientGrothendieckMap P) :=
  grothendieckMap_surjective P P.isoModSerre.Q

theorem quotientGrothendieckMap_ker :
    (quotientGrothendieckMap P).ker = serreSubgroup P :=
  grothendieckMap_ker P P.isoModSerre.Q

/-- The algebraic presentation of the canonical Serre quotient is the quotient
by the actual source Serre subgroup. -/
def quotientGrothendieckEquiv :
    (abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P ≃+
      (abelianExactStructure P.isoModSerre.Localization).GrothendieckGroup :=
  grothendieckModuloSerreEquiv P P.isoModSerre.Q

@[simp]
lemma quotientGrothendieckEquiv_class (X : C) :
    quotientGrothendieckEquiv P (classModuloSerre P X) =
      (abelianExactStructure P.isoModSerre.Localization).grothendieckClass
        (P.isoModSerre.Q.obj X) :=
  grothendieckModuloSerreEquiv_class P P.isoModSerre.Q X

end CategoryTheory.ExactCategory.SerreLocalization

attribute [colib_tag "COL-0029",
  stacks 02MX "(1), canonical quotient with equal source object and hom universes"]
  CategoryTheory.ExactCategory.SerreLocalization.quotientGrothendieckEquiv

attribute [colib_tag "COL-0029"]
  CategoryTheory.ExactCategory.SerreLocalization.quotientGrothendieckEquiv_class
  CategoryTheory.ExactCategory.SerreLocalization.quotientGrothendieckMap_ker
  CategoryTheory.ExactCategory.SerreLocalization.quotientGrothendieckMap_surjective

attribute [stacks 02MS "the canonical quotient annihilates exactly the Serre objects"]
  CategoryTheory.ExactCategory.SerreLocalization.quotient_isZero_obj_iff
