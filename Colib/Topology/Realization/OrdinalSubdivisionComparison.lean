/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.OrdinalSubdivisionRealization
public import Colib.Topology.Realization.OrdinalSubdivisionConditional

/-! # The proved ordinary subdivision comparison and its actual bisimplicial maps

The explicit comparison data are filled by the proved global realization theorem,
not by an added hypothesis. All forward maps retain the source endpoint maps.
The bisimplicial interfaces adapt OrdinalSubdivisionBisimplicial.lean from Quillen
at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/
@[expose] public noncomputable section
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
namespace SSet.OrdinalSubdivision

/-- The required global data, constructed from the proved ordinary subdivision equivalence. -/
def realizationComparison : RealizationComparison.{u} where
  equiv := realizationHomotopyEquiv
  forward := realizationHomotopyEquiv_toFun

/-- The actual equivalence in double-diagonal coordinates. -/
def doubleDiagonalHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (horizontal (vertical X))| |diagonalSSet X| :=
  realizationComparison.doubleDiagonalHomotopyEquiv X

@[simp]
theorem doubleDiagonalHomotopyEquiv_toFun (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (doubleDiagonalHomotopyEquiv X).toFun =
      (SSet.toTop.map ((doubleDiagonalIso X).hom ≫ endpoint (diagonalSSet X))).hom :=
  realizationComparison.doubleDiagonalHomotopyEquiv_toFun X

/-- The genuine inner-direction comparison, with the actual endpoint forward map. -/
def verticalRealizationHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (vertical X)| |diagonalSSet X| :=
  realizationComparison.verticalRealizationHomotopyEquiv X

@[simp]
theorem verticalRealizationHomotopyEquiv_toFun (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (verticalRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (diagonalMap (verticalEndpoint X))).hom := rfl

/-- The genuine outer-direction comparison, with the actual endpoint forward map. -/
def horizontalRealizationHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (horizontal X)| |diagonalSSet X| :=
  realizationComparison.horizontalRealizationHomotopyEquiv X

@[simp]
theorem horizontalRealizationHomotopyEquiv_toFun (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (horizontalRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (diagonalMap (horizontalEndpoint X))).hom := rfl

/-- The actual first-index comparison retains outer subdivision. -/
def firstIndexRealizationHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv
      |diagonalSSet (δ.op ⋙ X ⋙ subdivisionFunctor)| |diagonalSSet (δ.op ⋙ X)| :=
  realizationComparison.firstIndexRealizationHomotopyEquiv X

@[simp]
theorem firstIndexRealizationHomotopyEquiv_toFun (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (firstIndexRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (diagonalMap
        (Functor.whiskerLeft (δ.op ⋙ X) endpointNatTrans))).hom := rfl

end SSet.OrdinalSubdivision
