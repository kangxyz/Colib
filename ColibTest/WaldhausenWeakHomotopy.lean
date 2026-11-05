import Colib.KTheory.Waldhausen.HomotopyMap
import Colib.KTheory.Waldhausen.WeakRowHomotopy

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial
universe u v
namespace WaldhausenWeakHomotopyTests
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))

example : SSet.Homotopy (sSetMap hF) (sSetMap hG) :=
  weakNaturalTransformationHomotopy V W hF hG η hη

example : (deloopingMap hF).hom.Homotopy (deloopingMap hG).hom :=
  weakNaturalTransformationRealizationHomotopy V W hF hG η hη

example : SSet.ι₀ ≫ weakNaturalTransformationCylinder V W hF hG η hη = sSetMap hF :=
  weakNaturalTransformationCylinder_zero V W hF hG η hη

example : SSet.ι₁ ≫ weakNaturalTransformationCylinder V W hF hG η hη = sSetMap hG :=
  weakNaturalTransformationCylinder_one V W hF hG η hη

example (n : SimplexCategory) (X : WeakRows V n) (p : Interval n) :
    ((weakRowsPostcomposeTransformation V W hF hG η hη n).app X).hom.hom.app p =
      η.app (X.obj.obj.obj p) := rfl

example (n : SimplexCategory) :
    (classifyingSpaceMap (weakRowsPostcompose V W hF n)).hom.Homotopy
      (classifyingSpaceMap (weakRowsPostcompose V W hG n)).hom :=
  weakRowRealizationHomotopy V W hF hG η hη n

example (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero) :
    (deloopingMap hF).hom.HomotopyRel (deloopingMap hG).hom {V.kBasepoint} :=
  weakNaturalTransformationBasedHomotopy V W hF hG η hη hF0 hG0

example (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero) (n : ℕ) :
    groupsMapOfZeroEq hF V.zero V.isZero W.zero W.isZero hF0 n =
      groupsMapOfZeroEq hG V.zero V.isZero W.zero W.isZero hG0 n :=
  groupsMapOfZeroEq_eq_of_weakNaturalTransformation V W hF hG η hη hF0 hG0 n

end WaldhausenWeakHomotopyTests
