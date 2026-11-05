/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Colib.Topology.Realization.OrdinalSubdivisionRealization

noncomputable section

open CategoryTheory
open scoped Simplicial Topology
universe u

example (X : SSet.{u}) :
    ContinuousMap.HomotopyEquiv |SSet.OrdinalSubdivision.subdivision X| |X| :=
  SSet.OrdinalSubdivision.realizationHomotopyEquiv X

example (X : SSet.{u}) :
    (SSet.OrdinalSubdivision.realizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (SSet.OrdinalSubdivision.endpoint X)).hom := rfl

example (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.OrdinalSubdivision.realizationHomotopyEquiv X
      (SSet.realizationPoint (SSet.OrdinalSubdivision.vertex x)) =
        SSet.realizationPoint x :=
  SSet.OrdinalSubdivision.realizationHomotopyEquiv_vertex x

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    (SSet.OrdinalSubdivision.realizationHomotopyEquiv Y).toFun.comp
      (SSet.toTop.map (SSet.OrdinalSubdivision.subdivisionFunctor.map f)).hom =
    (SSet.toTop.map f).hom.comp (SSet.OrdinalSubdivision.realizationHomotopyEquiv X).toFun :=
  SSet.OrdinalSubdivision.realizationHomotopyEquiv_naturality f

-- The first-half endpoint of the actual subdivided identity edge picks vertex zero.
example :
    (((SSet.OrdinalSubdivision.endpoint (Δ[1] : SSet)).app (Opposite.op ⦋0⦌)
      (ULift.up (𝟙 ⦋1⦌))).down.toOrderHom 0) = 0 := rfl

-- Both halves retain their original order in the actual unreversed indexing functor.
example (i : Fin 2) :
    (SSet.OrdinalSubdivision.δ.map (𝟙 ⦋1⦌)).toOrderHom
      ((SSet.OrdinalJoin.left ⦋1⦌ ⦋1⦌).toOrderHom i) =
    (SSet.OrdinalJoin.left ⦋1⦌ ⦋1⦌).toOrderHom i :=
  SSet.OrdinalSubdivision.δ_map_left (𝟙 ⦋1⦌) i

example {A X : SSet.{u}} (i : A ⟶ X) [Mono i] :
    TopCat.HomotopyExtensionProperty (SSet.toTop.map i) :=
  SSet.homotopyExtensionProperty_realization_mono i
