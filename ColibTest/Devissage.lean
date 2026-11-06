/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Colib.KTheory.Quillen.Devissage.Theorem
public import Colib.KTheory.Quillen.Equivalence

/-! Actual-map regression tests for classical dévissage. The contexts below
intentionally contain no extension closure, no uniform filtration bound and
no assumed homotopy inverse. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.ObjectProperty CategoryTheory.Abelian.Devissage
open scoped ZeroObject

universe v u

section ArbitraryUniverses

variable {C : Type u} [Category.{v} C] [Abelian C]
attribute [local instance] Abelian.hasFiniteBiproducts

example (P : ObjectProperty C) : FiltrationHypothesis P ↔
    ∀ X : C, Nonempty ((abelianExactStructure C).Filtration P X) := Iff.rfl

example {X Y : C} (s : QConstruction.AbelianSpan X Y) : Epi s.l := inferInstance

example {X Y : C} (s : QConstruction.AbelianSpan X Y) : Mono s.r := inferInstance

example {X Y : (abelianExactStructure C).QCategory} (f : X ⟶ Y) : Mono f :=
  inferInstance

example {X Y Z : (abelianExactStructure C).QCategory} (f g : X ⟶ Y) (h : Y ⟶ Z)
    (w : f ≫ h = g ≫ h) : f = g := (cancel_mono h).mp w

variable (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts]

example : (mapQ P).Full := inferInstance

example : (mapQ P).Faithful := inferInstance

example : mapQ P = (exactInclusion P).mapQ := rfl

example (X : P.FullSubcategory) :
    (mapQ P).obj (QConstruction.of _ _ X) = QConstruction.of _ _ X.obj := rfl

example {X Y : P.FullSubcategory} (s : QConstruction.AbelianSpan X.obj Y.obj) :
    (exactInclusion P).toQCompatibleFunctor.mapSpan (liftSpan P s) = s := rfl

example {X M : C} (s : QConstruction.AbelianSpan X M) (hX : P X) :
    cokernel.π (Subobject.ofLE (spanLayer P s hX).lower (spanLayer P s hX).upper
      (spanLayer P s hX).le) ≫ (spanLayerQuotientIso P s hX).hom =
        (Subobject.underlyingIso s.r).hom ≫ s.l :=
  cokernel_π_spanLayerQuotientIso_hom P s hX

example (M : C) : Quiver.IsThin (QComma P M) := inferInstance

example (M : C) (L : Layer P M) :
    (layerToComma P M).obj L = L.comma := rfl

example (M : C) (L : Layer P M) :
    ((layerToComma P M).obj L).hom = QConstruction.mkHom _ _ L.span := rfl

example (M : C) (L K : Layer P M) : L ≤ K ↔ Nonempty (L.comma ⟶ K.comma) := by
  constructor
  · exact fun h => ⟨Layer.commaMap h⟩
  · rintro ⟨f⟩
    exact Layer.le_of_comma_hom f

example (M : C) : (layerCommaEquivalence P M).functor = layerToComma P M := rfl

example (M : C) (L K : Layer P M) (h : L ≤ K) :
    QConstruction.mkHom _ _ (Layer.mapSpan h) ≫ QConstruction.mkHom _ _ K.span =
      QConstruction.mkHom _ _ L.span := Layer.mapSpan_comp h

example {M : C} {A N : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    (Layer.supportedStepHomotopyEquiv hAN hA).toFun =
      (classifyingSpaceMap (Layer.supportedInclusion (P := P) hAN)).hom := rfl

example {M : C} {A N : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    (Layer.supportedStepHomotopyEquiv hAN hA).invFun =
      (classifyingSpaceMap (Layer.supportedRestriction (P := P) A N)).hom := rfl

example {X M : C} (F : (abelianExactStructure C).Filtration P X) (j : X ⟶ M)
    [Mono j] : ContractibleSpace
      (ClassifyingSpace (Layer.Supported (P := P) (Subobject.mk j))) :=
  Layer.supported_contractible_of_filtration F j

example {M : C} (F : (abelianExactStructure C).Filtration P M) :
    ContractibleSpace (ClassifyingSpace (Layer P M)) := Layer.contractible_of_filtration F

example (h : FiltrationHypothesis P) : Function.Surjective (grothendieckMap P) :=
  grothendieckMap_surjective P h

end ArbitraryUniverses

section Small

variable {C : Type u} [SmallCategory C] [Abelian C]
attribute [local instance] Abelian.hasFiniteBiproducts
variable (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts] (h : FiltrationHypothesis P)

example (M : C) : ContractibleSpace (ClassifyingSpace (QComma P M)) :=
  qComma_contractible P h M

example : (classifyingHomotopyEquiv P h).toFun =
    (classifyingSpaceMap (exactInclusion P).mapQ).hom := rfl

example : (pointedClassifyingHomotopyEquiv P h).toFun = pointedClassifyingMap P := rfl

example : pointedClassifyingMap P (abelianExactStructure P.FullSubcategory).kBasepoint =
    (abelianExactStructure C).kBasepoint := pointedClassifyingMap_basepoint P

example (n : ℕ) : (KEquiv P h n).toMonoidHom = (exactInclusion P).KMap n := rfl

example : Function.Bijective ((exactInclusion P).KMap 0) := KMap_bijective P h 0

example (n : ℕ) : Function.Bijective ((exactInclusion P).KMap (n + 1)) :=
  KMap_bijective P h (n + 1)

include h in
/-- The endpoint tests the actual native inclusion, without an inherited
extension-closed exact structure or a homotopy-inverse assumption. -/
theorem actualInclusionKMap_bijective (n : ℕ) :
    Function.Bijective ((exactInclusion P).KMap n) := KMap_bijective P h n

end Small
