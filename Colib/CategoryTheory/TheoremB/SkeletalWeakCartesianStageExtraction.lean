/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.SkeletalWeakCartesianCharts
public import Colib.CategoryTheory.TheoremB.SkeletalBoundary
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianAssembly

/-!
# Extracting original characteristic comparisons for coefficient transformations

For arbitrary diagrams and their natural transformation, the actual cell
coproduct inclusions are genuinely cartesian. Pasting them with a weak
whole-cell comparison gives the original individual characteristic chart.
Both coefficient diagrams remain unchanged; no point-augmentation coordinate
replacement or homotopy inverse of the weak whole-cell comparison is used.


Implementation provenance:
`Quillen/CategoryTheory/TheoremB/SkeletalWeakCartesianStageExtraction.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA


noncomputable section
open Topology TopCat SSet Topology.HomotopyPullback
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

/-- The original transformation carries each actual cell summand to its
corresponding summand in the second coefficient diagram. -/
theorem coefficientComponentCell_square {n : ℕ} (s : (nerve D).nonDegenerate n) :
    realizationFunctor.map (bisimplicialSigmaι (replacementCell H) s) ≫ cellProjection η n =
      realizationFunctor.map (outerProductCoefficientMap
        (K := (Δ[n] : SSet.{u})) (η.app (s.1.obj 0))) ≫
          realizationFunctor.map (bisimplicialSigmaι (replacementCell J) s) := by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  rfl

/-- Actual corresponding cofan inclusions are genuinely cartesian for an
arbitrary coefficient transformation, with no weakness assumption. -/
theorem coefficientComponentCell_cartesian (n : ℕ) (s : (nerve D).nonDegenerate n) :
    Cartesian (realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) (η.app (s.1.obj 0)))).hom
      (cellProjection η n).hom
      (realizationFunctor.map (bisimplicialSigmaι (replacementCell H) s)).hom
      (realizationFunctor.map (bisimplicialSigmaι (replacementCell J) s)).hom
      (congrArg TopCat.Hom.hom (coefficientComponentCell_square η s)) :=
  cartesianCofanComponent
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCell H s))
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCell J s))
    (realizedCofan (replacementCell H)) (realizedCofan (replacementCell J))
    (realizedBisimplicialSigmaIsColimit _) (realizedBisimplicialSigmaIsColimit _)
    (cellProjection η n)
    (fun s ↦ realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) (η.app (s.1.obj 0))))
    (fun s ↦ coefficientComponentCell_square η s) s

/-- The exact individual characteristic maps commute with the original
coefficient transformation before any comparison is formed. -/
theorem coefficientComponentCharacteristic_square {n : ℕ} (s : (nerve D).nonDegenerate n) :
    realizationFunctor.map (replacementCellCharacteristic H s) ≫ stageProjection η (n+1) =
      realizationFunctor.map (outerProductCoefficientMap
        (K := (Δ[n] : SSet.{u})) (η.app (s.1.obj 0))) ≫
          realizationFunctor.map (replacementCellCharacteristic J s) := by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg realizationFunctor.map
    (simplexChart_coefficient H η ((nerve D).skeleton (n+1)) s.1 ((nerve D).mem_skeleton s.1))

/-- Every individual original chart is weakly cartesian once the outgoing
whole-cell face is weakly cartesian. Genuine component cartesianness and weak
pasting retain the exact coefficient maps and characteristic paths. -/
theorem coefficientComponentCharacteristic_weakCartesian (n : ℕ)
    (h : WeakCartesian (cellProjection η n).hom (stageProjection η (n + 1)).hom
      (characteristicLeg H n).hom (characteristicLeg J n).hom
      (congrArg TopCat.Hom.hom (cellCharacteristicSquare η n)))
    (s : (nerve D).nonDegenerate n) :
    ChartWeakCartesian η ((nerve D).skeleton (n+1)) s.1 ((nerve D).mem_skeleton s.1) := by
  have hpaste := (coefficientComponentCell_cartesian η n s).weak.paste h
  have hf : realizationFunctor.map (bisimplicialSigmaι (replacementCell H) s) ≫
      characteristicLeg H n = realizationFunctor.map (replacementCellCharacteristic H s) := by
    change realizationFunctor.map _ ≫ realizationFunctor.map _ = realizationFunctor.map _
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  have hg : realizationFunctor.map (bisimplicialSigmaι (replacementCell J) s) ≫
      characteristicLeg J n = realizationFunctor.map (replacementCellCharacteristic J s) := by
    change realizationFunctor.map _ ≫ realizationFunctor.map _ = realizationFunctor.map _
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  exact hpaste.congr rfl rfl (congrArg TopCat.Hom.hom hf) (congrArg TopCat.Hom.hom hg)

end CategoryTheory.TheoremB.Skeletal
