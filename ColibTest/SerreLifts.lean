module

import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryLift

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Localization CategoryTheory.ExactCategory.SerreLocalization

universe v₁ v₂ u₁ u₂

section General
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (L : C ⥤ D) (V : D) (W : MorphismProperty C) [L.IsLocalization W]

example [W.HasLeftCalculusOfFractions] : IsFiltered (AuxiliaryLift L V) :=
  auxiliaryLift_isFiltered L V W

example [W.HasRightCalculusOfFractions] : IsCofiltered (AuxiliaryLift L V) :=
  auxiliaryLift_isCofiltered L V W
end General

section Serre
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (L : C ⥤ D) (P : ObjectProperty C)
  [P.IsSerreClass] [L.IsLocalization P.isoModSerre] [L.Additive]

example (M : C) : Function.Surjective (subobjectMap L P M) :=
  subobjectMap_surjective L P M

example {M : C} (S T : Subobject (L.obj M)) (h : S ≤ T) :
    Nonempty (SubobjectIntervalLift L P M S T) := SubobjectIntervalLift.nonempty h
end Serre
