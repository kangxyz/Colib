/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Colib.Topology.Realization.EdgewiseSubdivisionBisimplicial
import Colib.AlgebraicTopology.SimplicialSet.OrdinalSubdivision

noncomputable section

open CategoryTheory Opposite SSet
open scoped Simplicial Topology
universe u

namespace EdgewiseSubdivisionRegression
open SSet.EdgewiseSubdivision

example (X : SSet.{u}) : ContinuousMap.HomotopyEquiv |subdivision X| |X| :=
  realizationHomotopyEquiv X

example (X : SSet.{u}) :
    (realizationHomotopyEquiv X).toFun = (SSet.toTop.map (endpoint X)).hom := rfl

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    (realizationHomotopyEquiv Y).toFun.comp
      (SSet.toTop.map (subdivisionFunctor.map f)).hom =
      (SSet.toTop.map f).hom.comp (realizationHomotopyEquiv X).toFun :=
  realizationHomotopyEquiv_naturality f

example (X : SSet.{u}) (x : X _⦋0⦌) :
    realizationHomotopyEquiv X (realizationPoint (vertex x)) = realizationPoint x :=
  realizationHomotopyEquiv_vertex x

-- The reversed-edgewise endpoint of the identity edge is its second vertex.
example : (((endpoint (Δ[1] : SSet)).app (op ⦋0⦌)
    (ULift.up (𝟙 ⦋1⦌))).down.toOrderHom 0) = 1 := rfl

-- This coface distinguishes reversal from the ordinary twofold construction.
example : (ε.map (SimplexCategory.δ (n := 0) 1)).toOrderHom 0 = (1 : Fin 4) := rfl

example : (OrdinalSubdivision.δ.map (SimplexCategory.δ (n := 0) 1)).toOrderHom 0 =
    (0 : Fin 4) := rfl

example : (ε.map (SimplexCategory.δ (n := 0) 1)).toOrderHom 1 = (2 : Fin 4) := rfl

example {p q : SimplexCategory} (f : p ⟶ q) (i : Fin (p.len + 1)) :
    (ε.map f).toOrderHom ((OrdinalJoin.left p p).toOrderHom i) =
      (OrdinalJoin.left q q).toOrderHom ((f.toOrderHom i.rev).rev) := ε_map_left f i

example {p q r : SimplexCategory} (f : p ⟶ q)
    (s : ε.obj q ⟶ r) (t : q ⟶ ⦋1⦌) :
    contractOperator (ε.map f ≫ s) (f ≫ t) = ε.map f ≫ contractOperator s t :=
  contractOperator_naturality f s t

example (n : ℕ) : ContractibleSpace |subdivision (Δ[n] : SSet.{u})| :=
  contractibleSpace_simplex n

example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (verticalRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (diagonalMap (verticalEndpoint X))).hom := rfl

example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (horizontalRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (diagonalMap (horizontalEndpoint X))).hom := rfl

example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    ContinuousMap.HomotopyEquiv
      |diagonalSSet (ε.op ⋙ X ⋙ subdivisionFunctor)| |diagonalSSet (ε.op ⋙ X)| :=
  upperIndexRealizationHomotopyEquiv X

example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (upperIndexRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (diagonalMap
        (Functor.whiskerLeft (ε.op ⋙ X) endpointNatTrans))).hom := rfl

end EdgewiseSubdivisionRegression
