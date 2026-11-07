/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Realized vertices and interval endpoints

The actual realization of a vertex and the standard simplicial interval, with its unit-
interval parameter and exact endpoints. No product preservation or general realization-of-
homotopies theorem is asserted.

## Implementation provenance

Adapted from `Quillen/Topology/Realization/Homotopy.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The selected declarations retain the source
constructions and mathematical universe parameters. The endpoint proofs use the
pinned native `Convexity.StdSimplex` coordinate API. Namespace and dependency ownership
are changed to the underlying Mathlib objects.
-/
@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial Topology unitInterval

universe u v

namespace SSet

/-- The point represented by a vertex in a simplicial set. -/
def realizationPoint {X : SSet.{u}} (x : X _⦋0⦌) : |X| :=
  SSet.toTop.map (SSet.yonedaEquiv.symm x) default

/-- A point of the realized interval with its ordinary unit-interval parameter. -/
def realizationInterval (t : unitInterval) : |(Δ[1] : SSet.{u})| :=
  SSet.stdSimplex.toTopObjIsoI.inv (ULift.up t)

@[fun_prop]
theorem continuous_realizationInterval : Continuous (realizationInterval.{u}) := by
  unfold realizationInterval
  fun_prop

@[simp]
theorem realizationInterval_zero :
    realizationInterval.{u} 0 = SSet.toTop.map (SSet.stdSimplex.δ 1) default := by
  apply (SimplexCategory.toTopHomeo ⦋1⦌).injective
  change SimplexCategory.toTopHomeo ⦋1⦌
    ((SimplexCategory.toTopHomeo ⦋1⦌).symm (TopCat.stdSimplexHomeomorphI.{u}.symm 0)) = _
  rw [Homeomorph.apply_symm_apply]
  rw [TopCat.stdSimplexHomeomorphI_symm_zero]
  change Convexity.StdSimplex.single 0 = SimplexCategory.toTopHomeo ⦋1⦌
    (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.δ 1)) default)
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [Subsingleton.elim (SimplexCategory.toTopHomeo ⦋0⦌ default) (Convexity.StdSimplex.single 0),
    Convexity.StdSimplex.map_single]
  rfl

@[simp]
theorem realizationInterval_one :
    realizationInterval.{u} 1 = SSet.toTop.map (SSet.stdSimplex.δ 0) default := by
  apply (SimplexCategory.toTopHomeo ⦋1⦌).injective
  change SimplexCategory.toTopHomeo ⦋1⦌
    ((SimplexCategory.toTopHomeo ⦋1⦌).symm (TopCat.stdSimplexHomeomorphI.{u}.symm 1)) = _
  rw [Homeomorph.apply_symm_apply]
  rw [TopCat.stdSimplexHomeomorphI_symm_one]
  change Convexity.StdSimplex.single 1 = SimplexCategory.toTopHomeo ⦋1⦌
    (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.δ 0)) default)
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  rw [Subsingleton.elim (SimplexCategory.toTopHomeo ⦋0⦌ default) (Convexity.StdSimplex.single 0),
    Convexity.StdSimplex.map_single]
  rfl

end SSet

attribute [colib_tag "COL-0060",
  colib_ref "WeibelKBook" "IV, Characterization 3.1(2) and Definition 3.1.4" "background"
    "Vertex and interval background; the exact ULift and endpoint API is implemented here"]
  SSet.realizationPoint
  SSet.realizationInterval
  SSet.continuous_realizationInterval
  SSet.realizationInterval_zero
  SSet.realizationInterval_one
