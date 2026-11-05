/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References

public import Colib.Topology.Realization.OrdinalSubdivisionRepresentable
public import Colib.Topology.Realization.CellularComparison
public import Colib.Topology.Realization.EdgePath

/-! # The actual ordinary subdivision endpoint realizes to a homotopy equivalence

Adapted from `Quillen/Topology/Realization/OrdinalSubdivisionRealization.lean` at
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Ordinary subdivision uses
`[n] ↦ [n] ⋆ [n]` with neither half reversed. The actual first-half endpoint is
retained as the forward map, including its naturality and chosen-vertex equation.
-/
@[expose] public noncomputable section
open CategoryTheory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet.OrdinalSubdivision

/-- The canonical first-half endpoint realizes to a homotopy equivalence for
an arbitrary simplicial set, including infinite-dimensional ones. -/
theorem realizesEquiv_endpoint (X : SSet.{u}) :
    RealizationComparison.RealizesEquiv endpointNatTrans X :=
  RealizationComparison.realizesEquiv_all endpointNatTrans realizesEquiv_endpoint_simplex X

/-- Ordinary subdivision preserves the actual realization homotopy type.
Its forward map is exactly the realized first-half endpoint comparison. -/
def realizationHomotopyEquiv (X : SSet.{u}) :
    ContinuousMap.HomotopyEquiv |subdivision X| |X| := by
  let e : ContinuousMap.HomotopyEquiv |subdivision X| |X| :=
    (realizesEquiv_endpoint X).choose
  have he : e.toFun = (SSet.toTop.map (endpoint X)).hom :=
    (realizesEquiv_endpoint X).choose_spec
  exact {
    toFun := (SSet.toTop.map (endpoint X)).hom
    invFun := e.invFun
    left_inv := by rw [← he]; exact e.left_inv
    right_inv := by rw [← he]; exact e.right_inv }

@[simp] theorem realizationHomotopyEquiv_toFun (X : SSet.{u}) :
    (realizationHomotopyEquiv X).toFun = (SSet.toTop.map (endpoint X)).hom := rfl

/-- The forward realization equivalences commute with every simplicial map. -/
theorem realizationHomotopyEquiv_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    (realizationHomotopyEquiv Y).toFun.comp
      (SSet.toTop.map (subdivisionFunctor.map f)).hom =
    (SSet.toTop.map f).hom.comp (realizationHomotopyEquiv X).toFun := by
  exact congrArg TopCat.Hom.hom (RealizationComparison.realization_naturality endpointNatTrans f)

/-- The forward equivalence sends every subdivided vertex to its endpoint vertex. -/
theorem realizationHomotopyEquiv_point (X : SSet.{u})
    (x : (subdivision X) _⦋0⦌) :
    realizationHomotopyEquiv X (realizationPoint x) =
      realizationPoint ((endpoint X).app _ x) :=
  realizationPoint_naturality (endpoint X) x

/-- The canonical forward equivalence preserves the original chosen vertex. -/
theorem realizationHomotopyEquiv_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    realizationHomotopyEquiv X (realizationPoint (vertex x)) = realizationPoint x := by
  rw [realizationHomotopyEquiv_point, endpoint_vertex]

end SSet.OrdinalSubdivision

attribute [colib_tag "COL-0216",
  colib_ref "WeibelKBook" "IV, Characterization 3.1, page 24"
    "background"
    "Actual geometric realization; the unreversed ordinary endpoint comparison is proved here"]
  SSet.OrdinalSubdivision.realizationHomotopyEquiv
  SSet.OrdinalSubdivision.realizationHomotopyEquiv_toFun
  SSet.OrdinalSubdivision.realizationHomotopyEquiv_naturality
  SSet.OrdinalSubdivision.realizationHomotopyEquiv_vertex
