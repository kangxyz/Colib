/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.Topology.Homotopy.Path

/-!
# Realized simplicial edges as actual paths

Extracted from `Quillen/Topology/Realization/Homotopy.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, endpoints,
relative homotopies, universe parameters and multiplication order are retained.
Only native namespace and import ownership change unless noted below.

-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Opposite
open scoped Simplicial Topology unitInterval

namespace SSet

/-- An edge realizes to a path with exactly its prescribed vertex endpoints. -/
def realizationEdgePath {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    Path (realizationPoint x) (realizationPoint y) where
  toFun t := SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) (realizationInterval t)
  continuous_toFun := by fun_prop
  source' := by
    rw [realizationInterval_zero]
    change (SSet.toTop.map (SSet.stdSimplex.δ 1) ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)) default = _
    rw [← Functor.map_comp, e.δ_one_yonedaEquiv_symm]
    rfl
  target' := by
    rw [realizationInterval_one]
    change (SSet.toTop.map (SSet.stdSimplex.δ 0) ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)) default = _
    rw [← Functor.map_comp, e.δ_zero_yonedaEquiv_symm]
    rfl

@[simp]
theorem realizationEdgePath_apply {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : X.Edge x y) (t : unitInterval) :
    realizationEdgePath e t =
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) (realizationInterval t) := rfl

@[simp]
theorem realizationPoint_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    SSet.toTop.map f (realizationPoint x) = realizationPoint (f.app _ x) := by
  change (SSet.toTop.map (SSet.yonedaEquiv.symm x) ≫ SSet.toTop.map f) default = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

/-- The realized edge map is natural at every interval parameter. -/
@[simp] theorem realizationEdgePath_naturality_apply {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} (e : X.Edge x y) (t : unitInterval) :
    SSet.toTop.map f
      (SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) (realizationInterval t)) =
        SSet.toTop.map (SSet.yonedaEquiv.symm (e.map f).edge) (realizationInterval t) := by
  change (SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) ≫ SSet.toTop.map f)
    (realizationInterval t) = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

@[simp]
theorem realizationEdgePath_id {X : SSet.{u}} (x : X _⦋0⦌) :
    realizationEdgePath (SSet.Edge.id x) = Path.refl (realizationPoint x) := by
  ext t
  change SSet.toTop.map (SSet.yonedaEquiv.symm (X.σ 0 x)) (realizationInterval t) = _
  rw [← SSet.stdSimplex.σ_comp_yonedaEquiv_symm, Functor.map_comp, TopCat.comp_app]
  rw [Subsingleton.elim (SSet.toTop.map (SSet.stdSimplex.σ 0) (realizationInterval t)) default]
  rfl

end SSet

attribute [colib_tag "COL-0081",
  colib_ref "WeibelKBook" "IV, Characterization 3.1(2) and Definition 3.1.4"
    "background"
    "Actual realized edge paths, interval parameters and vertex endpoints"]
  SSet.realizationEdgePath
  SSet.realizationEdgePath_naturality_apply
  SSet.realizationEdgePath_id
