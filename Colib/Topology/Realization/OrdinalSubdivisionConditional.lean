/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.OrdinalSubdivisionBisimplicial
public import Colib.Topology.Homotopy.Equiv.AdjacentComposites
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-! # Conditional transfer of an actual ordinary subdivision realization equivalence

Every conclusion in this file takes explicit global comparison data. This file does not
construct those data or assert that they exist. Adapted from
Quillen/Topology/Realization/OrdinalSubdivisionBisimplicial.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd, retaining each actual forward map.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
namespace SSet.OrdinalSubdivision

/-- The exact global comparison still needed for unconditional additivity. -/
structure RealizationComparison where
  /-- A genuine equivalence for every simplicial set, not just representables. -/
  equiv (X : SSet.{u}) : ContinuousMap.HomotopyEquiv |subdivision X| |X|
  /-- Its forward map is the actual first-half endpoint realization. -/
  forward (X : SSet.{u}) : (equiv X).toFun = (SSet.toTop.map (endpoint X)).hom

namespace RealizationComparison
variable (comparison : RealizationComparison.{u})

/-- The global ordinary twofold equivalence in double-diagonal coordinates. -/
def doubleDiagonalHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (horizontal (vertical X))| |diagonalSSet X| :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (doubleDiagonalIso X))).toHomotopyEquiv.trans
    (comparison.equiv (diagonalSSet X))

@[simp] theorem doubleDiagonalHomotopyEquiv_toFun (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (doubleDiagonalHomotopyEquiv comparison X).toFun =
      (SSet.toTop.map ((doubleDiagonalIso X).hom ≫ endpoint (diagonalSSet X))).hom := by
  change (comparison.equiv (diagonalSSet X)).toFun.comp
    (SSet.toTop.map (doubleDiagonalIso X).hom).hom = _
  rw [comparison.forward, Functor.map_comp]
  rfl

/-- Inner-direction subdivision preserves the actual diagonal realization homotopy type. -/
def verticalRealizationHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (vertical X)| |diagonalSSet X| :=
  ContinuousMap.HomotopyEquiv.ofAdjacentComposites
    (SSet.toTop.map (diagonalMap (verticalEndpoint X))).hom
    (SSet.toTop.map (diagonalMap (horizontalEndpoint (vertical X)))).hom
    (SSet.toTop.map
      (diagonalMap (Functor.whiskerLeft δ.op (verticalEndpoint (vertical X))))).hom
    (doubleDiagonalHomotopyEquiv comparison X) (doubleDiagonalHomotopyEquiv comparison (vertical X))
    (by rw [doubleDiagonalHomotopyEquiv_toFun comparison, ← horizontalEndpoint_verticalEndpoint,
          Functor.map_comp]; rfl)
    (by rw [doubleDiagonalHomotopyEquiv_toFun comparison, ← verticalEndpoint_horizontalEndpoint,
          Functor.map_comp]; rfl)

@[simp] theorem verticalRealizationHomotopyEquiv_toFun (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (verticalRealizationHomotopyEquiv comparison X).toFun =
      (SSet.toTop.map (diagonalMap (verticalEndpoint X))).hom := rfl

/-- Outer-direction subdivision likewise preserves diagonal realization. -/
def horizontalRealizationHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (horizontal X)| |diagonalSSet X| :=
  ContinuousMap.HomotopyEquiv.ofAdjacentComposites
    (SSet.toTop.map (diagonalMap (horizontalEndpoint X))).hom
    (SSet.toTop.map
      (diagonalMap (Functor.whiskerLeft δ.op (verticalEndpoint X)))).hom
    (SSet.toTop.map (diagonalMap (horizontalEndpoint (horizontal (vertical X))))).hom
    (doubleDiagonalHomotopyEquiv comparison X) (doubleDiagonalHomotopyEquiv comparison
      (horizontal X))
    (by rw [doubleDiagonalHomotopyEquiv_toFun comparison, ← verticalEndpoint_horizontalEndpoint,
          Functor.map_comp]; rfl)
    (by rw [doubleDiagonalHomotopyEquiv_toFun comparison, ← horizontalEndpoint_verticalEndpoint,
          Functor.map_comp]; rfl)

@[simp] theorem horizontalRealizationHomotopyEquiv_toFun
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (horizontalRealizationHomotopyEquiv comparison X).toFun =
      (SSet.toTop.map (diagonalMap (horizontalEndpoint X))).hom := rfl

/-- The first-index restriction retains the outer subdivision and restricts
the inner direction to its first half. -/
def firstIndexRealizationHomotopyEquiv (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv
      |diagonalSSet (δ.op ⋙ X ⋙ subdivisionFunctor)| |diagonalSSet (δ.op ⋙ X)| :=
  verticalRealizationHomotopyEquiv comparison (horizontal X)

@[simp] theorem firstIndexRealizationHomotopyEquiv_toFun
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (firstIndexRealizationHomotopyEquiv comparison X).toFun =
      (SSet.toTop.map (diagonalMap
        (Functor.whiskerLeft (δ.op ⋙ X) endpointNatTrans))).hom := rfl

end RealizationComparison
end SSet.OrdinalSubdivision
