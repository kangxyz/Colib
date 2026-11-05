module

import Colib.KTheory.Waldhausen.ExactEquivalence
import all ColibTest.PerfectWaldhausen

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace GeometryKProbe

open PerfectWaldhausenProbe

variable (X : Scheme.{u}) [hD : ∀ U : X.Opens, HasDerivedCategory.{d} U.toScheme.Modules]

-- Consume the exact geometry construction, without copying its private predicates.
private def geometryKEquiv (n : ℕ) : (sourceWaldhausen X).K n ≃* (targetWaldhausen X).K n :=
  Waldhausen.KEquivOfExactEquivalence (comparison X)
    (comparison_exact X) (comparison_inverse_exact X) n

example (n : ℕ) : (geometryKEquiv X n).toMonoidHom =
    Waldhausen.KMap (comparison_exact X) n := rfl

example (n : ℕ) : (geometryKEquiv X n).symm.toMonoidHom =
    Waldhausen.KMap (comparison_inverse_exact X) n := rfl

example (n : ℕ) :
    (Waldhausen.KMap (comparison_inverse_exact X) n).comp
      (Waldhausen.KMap (comparison_exact X) n) = MonoidHom.id ((sourceWaldhausen X).K n) :=
  Waldhausen.KMap_inverse_comp_KMap (comparison X)
    (comparison_exact X) (comparison_inverse_exact X) n

example (n : ℕ) :
    (Waldhausen.KMap (comparison_exact X) n).comp
      (Waldhausen.KMap (comparison_inverse_exact X) n) =
        MonoidHom.id ((targetWaldhausen X).K n) :=
  Waldhausen.KMap_comp_KMap_inverse (comparison X)
    (comparison_exact X) (comparison_inverse_exact X) n

example (n : ℕ) (x : (sourceWaldhausen X).K n) :
    (geometryKEquiv X n).symm ((geometryKEquiv X n) x) = x :=
  (geometryKEquiv X n).symm_apply_apply x

example (n : ℕ) (x : (targetWaldhausen X).K n) :
    (geometryKEquiv X n) ((geometryKEquiv X n).symm x) = x :=
  (geometryKEquiv X n).apply_symm_apply x

example : (comparison X).functor.obj (sourceWaldhausen X).zero =
    (targetWaldhausen X).zero := rfl

example : (comparison X).inverse.obj (targetWaldhausen X).zero =
    (sourceWaldhausen X).zero := rfl

example (n : ℕ) : (geometryKEquiv X n).toMonoidHom =
    HomotopyGroup.piMap n (Waldhausen.deloopingMap (comparison_exact X)).hom
      (Waldhausen.deloopingMap_basepoint_of_zeroEq (comparison_exact X) rfl) :=
  Waldhausen.KMap_eq_piMap_of_zeroEq (comparison_exact X) rfl n

example (n : ℕ) : (geometryKEquiv X n).symm.toMonoidHom =
    HomotopyGroup.piMap n (Waldhausen.deloopingMap (comparison_inverse_exact X)).hom
      (Waldhausen.deloopingMap_basepoint_of_zeroEq (comparison_inverse_exact X) rfl) :=
  Waldhausen.KMap_eq_piMap_of_zeroEq (comparison_inverse_exact X) rfl n

-- In this geometry comparison the original maps already preserve the chosen zero strictly.
-- Thus the actual unit/counit cylinders have based, not merely free, realization homotopies.
private def geometryLeftBasedHomotopy :
    (Waldhausen.deloopingMap
      ((comparison_exact X).comp (comparison_inverse_exact X))).hom.HomotopyRel
        (Waldhausen.deloopingMap
          (Waldhausen.IsExact.id (sourceWaldhausen X).cof (sourceWaldhausen X).weq)).hom
        {(sourceWaldhausen X).kBasepoint} :=
  Waldhausen.weakNaturalTransformationBasedHomotopy (sourceWaldhausen X) (sourceWaldhausen X)
    ((comparison_exact X).comp (comparison_inverse_exact X))
    (Waldhausen.IsExact.id (sourceWaldhausen X).cof (sourceWaldhausen X).weq)
    (comparison X).unitIso.inv (fun _ => (sourceWaldhausen X).weq_iso _ inferInstance) rfl rfl

private def geometryRightBasedHomotopy :
    (Waldhausen.deloopingMap
      ((comparison_inverse_exact X).comp (comparison_exact X))).hom.HomotopyRel
        (Waldhausen.deloopingMap
          (Waldhausen.IsExact.id (targetWaldhausen X).cof (targetWaldhausen X).weq)).hom
        {(targetWaldhausen X).kBasepoint} :=
  Waldhausen.weakNaturalTransformationBasedHomotopy (targetWaldhausen X) (targetWaldhausen X)
    ((comparison_inverse_exact X).comp (comparison_exact X))
    (Waldhausen.IsExact.id (targetWaldhausen X).cof (targetWaldhausen X).weq)
    (comparison X).counitIso.hom (fun _ => (targetWaldhausen X).weq_iso _ inferInstance) rfl rfl

example : Waldhausen.deloopingMap (comparison_exact X) ≫
      Waldhausen.deloopingMap (comparison_inverse_exact X) =
    Waldhausen.deloopingMap ((comparison_exact X).comp (comparison_inverse_exact X)) :=
  Waldhausen.deloopingMap_comp_deloopingMap (comparison_exact X) (comparison_inverse_exact X)

example : Waldhausen.deloopingMap (comparison_inverse_exact X) ≫
      Waldhausen.deloopingMap (comparison_exact X) =
    Waldhausen.deloopingMap ((comparison_inverse_exact X).comp (comparison_exact X)) :=
  Waldhausen.deloopingMap_comp_deloopingMap (comparison_inverse_exact X) (comparison_exact X)

end GeometryKProbe

namespace GeometryKProbe

open PerfectWaldhausenProbe

local instance standardLocalModels (X : Scheme.{u}) :
    ∀ U : X.Opens, HasDerivedCategory.{u + 1} U.toScheme.Modules :=
  fun U => HasDerivedCategory.standard U.toScheme.Modules

-- The source's fixed standard-model convention is an actual specialization.
private def standardGeometryKEquiv (X : Scheme.{u}) (n : ℕ) :
    (sourceWaldhausen X).K n ≃* (targetWaldhausen X).K n := geometryKEquiv X n

example (X : Scheme.{u}) (n : ℕ) : (standardGeometryKEquiv X n).toMonoidHom =
    Waldhausen.KMap (comparison_exact X) n := rfl

end GeometryKProbe

/-- The generic equivalence reduces to the existing identity K-map, without a zero hypothesis. -/
theorem reflexive_KEquiv_toMonoidHom {C : Type u} [Category.{d} C]
    (W : Waldhausen.Structure C) (n : ℕ) :
    (Waldhausen.KEquivOfExactEquivalence (CategoryTheory.Equivalence.refl : C ≌ C)
      (Waldhausen.IsExact.id W.cof W.weq) (Waldhausen.IsExact.id W.cof W.weq) n).toMonoidHom =
        MonoidHom.id (W.K n) := Waldhausen.KMap_id W n
