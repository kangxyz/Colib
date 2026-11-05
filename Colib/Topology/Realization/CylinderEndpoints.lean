/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.Prism
public import Colib.Topology.Realization.Constant

/-! # Endpoints of the geometric realization cylinder comparison -/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/Realization/CylinderEndpoints.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The canonical maps, equality hypotheses,
endpoint orientation, independent universes and `ULift` direction are retained.
-/
@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial Topology unitInterval

universe u

namespace SSet

/-- The realized constant vertex is the corresponding interval endpoint. -/
@[simp] theorem realizationIntervalIso_zero_const :
    SSet.stdSimplex.toTopObjIsoI.{u}.hom
      (realizationPoint (SSet.stdSimplex.const 1 0 (op ⦋0⦌))) = (0 : TopCat.I) := by
  change SSet.stdSimplex.toTopObjIsoI.hom (SSet.toTop.map (SSet.yonedaEquiv.symm _) default) = _
  have hvertex : SSet.stdSimplex.δ 1 = SSet.const (SSet.stdSimplex.const 1 0 (op ⦋0⦌)) := by
    simpa only [SSet.stdSimplex.obj₀Equiv_symm_apply] using
      SSet.stdSimplex.δ_one_eq_const.{u}
  rw [SSet.yonedaEquiv_symm_zero, ← hvertex, ← realizationInterval_zero]
  exact ConcreteCategory.congr_hom SSet.stdSimplex.toTopObjIsoI.inv_hom_id _

/-- The realized constant vertex is the corresponding interval endpoint. -/
@[simp] theorem realizationIntervalIso_one_const :
    SSet.stdSimplex.toTopObjIsoI.{u}.hom
      (realizationPoint (SSet.stdSimplex.const 1 1 (op ⦋0⦌))) = (1 : TopCat.I) := by
  change SSet.stdSimplex.toTopObjIsoI.hom (SSet.toTop.map (SSet.yonedaEquiv.symm _) default) = _
  have hvertex : SSet.stdSimplex.δ 0 = SSet.const (SSet.stdSimplex.const 1 1 (op ⦋0⦌)) := by
    simpa only [SSet.stdSimplex.obj₀Equiv_symm_apply] using
      SSet.stdSimplex.δ_zero_eq_const.{u}
  rw [SSet.yonedaEquiv_symm_zero, ← hvertex, ← realizationInterval_one]
  exact ConcreteCategory.congr_hom SSet.stdSimplex.toTopObjIsoI.inv_hom_id _

/-- The zero endpoint of the simplicial cylinder is the zero endpoint of the topological cylinder.
-/
@[simp]
theorem realizationCylinderComparison_zero (X : SSet.{u}) :
    SSet.toTop.map (SSet.ι₀ (X := X)) ≫ realizationCylinderComparison X = TopCat.ι₀ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, realizationCylinderComparison_fst, ← Functor.map_comp]
    simp
  · rw [Category.assoc, realizationCylinderComparison_snd, ← Category.assoc,
      ← Functor.map_comp, SSet.ι₀_snd]
    ext x : 1
    change SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)) x) = 0
    rw [realization_const_apply]
    simpa only [SSet.stdSimplex.obj₀Equiv_symm_apply] using
      realizationIntervalIso_zero_const.{u}

/-- The one endpoint of the simplicial cylinder is the one endpoint of the topological cylinder. -/
@[simp]
theorem realizationCylinderComparison_one (X : SSet.{u}) :
    SSet.toTop.map (SSet.ι₁ (X := X)) ≫ realizationCylinderComparison X = TopCat.ι₁ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, realizationCylinderComparison_fst, ← Functor.map_comp]
    simp
  · rw [Category.assoc, realizationCylinderComparison_snd, ← Category.assoc,
      ← Functor.map_comp, SSet.ι₁_snd]
    ext x : 1
    change SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1)) x) = 1
    rw [realization_const_apply]
    simpa only [SSet.stdSimplex.obj₀Equiv_symm_apply] using
      realizationIntervalIso_one_const.{u}

end SSet

attribute [colib_tag "COL-0069",
  colib_ref "WeibelKBook" "IV, Characterization 3.1(2), interval and vertex special cases"
    "background" "Interval endpoints; these exact comparison-map identities are proved here"]
  SSet.realizationCylinderComparison_zero
  SSet.realizationCylinderComparison_one
