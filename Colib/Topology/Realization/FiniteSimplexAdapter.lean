/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Util.References
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-!
# Finite barycentric simplex compatibility

The pinned realization functor uses `Convexity.StdSimplex` with finitely
supported weights. This module compares it with Mathlib's function-subtype
`stdSimplex` for finite vertex sets.
The homeomorphism preserves each coordinate, every map of finite vertex sets,
vertices, and the orientation of the one-dimensional simplex. Realization
coordinates come directly from `SimplexCategory.toTopHomeo`.

## Implementation provenance and scope

This compatibility layer is a new coordinate comparison built from Mathlib
commit `16edf57de7933555826307a3d81b4391a3657a09`, specifically
`Analysis.Convex.StdSimplex`, `Geometry.Convex.ConvexSpace.Defs`,
`Geometry.Convex.ConvexSpace.Topology`,
`Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex`, and
`AlgebraicTopology.SimplicialSet.TopAdj`. It uses the finite-coordinate
embedding and `Finsupp.equivFunOnFinite`; it introduces no alternative
realization functor or additional axioms.

The intended consumer is the prism-coordinate construction in
`Quillen/Topology/Realization/Prism.lean` and `PrismGluing.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Those files use the newer
convex-space simplex at the realization boundary. This module supplies only
that coordinate comparison; the realization API now uses Mathlib's homeomorphism
directly.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial

namespace FiniteSimplexAdapter

variable {M N : Type*} [Fintype M] [Fintype N]

section LegacyCoordinates

-- These comparisons explicitly refer to Mathlib's legacy coordinate operations.
set_option linter.deprecated false

/-- Turn finite ordinary barycentric coordinates into finitely supported weights. -/
def toConvex (x : _root_.stdSimplex ℝ M) : Convexity.StdSimplex ℝ M where
  weights := Finsupp.equivFunOnFinite.symm x.val
  nonneg i := by simpa using x.property.1 i
  total := by simpa [Finsupp.sum_fintype] using x.property.2

/-- Forget finite support, retaining the barycentric coordinate conditions. -/
def toOld (x : Convexity.StdSimplex ℝ M) : _root_.stdSimplex ℝ M :=
  ⟨fun i ↦ x.weights i, x.weights_nonneg, x.total_of_fintype⟩

@[simp] lemma toConvex_weights (x : _root_.stdSimplex ℝ M) (i : M) :
    (toConvex x).weights i = x i := by
  simp [toConvex]
  rfl

@[simp] lemma toOld_apply (x : Convexity.StdSimplex ℝ M) (i : M) :
    toOld x i = x.weights i := rfl

@[simp] lemma toOld_toConvex (x : _root_.stdSimplex ℝ M) :
    toOld (toConvex x) = x := by
  ext i
  simp

@[simp] lemma toConvex_toOld (x : Convexity.StdSimplex ℝ M) :
    toConvex (toOld x) = x := by
  apply Convexity.StdSimplex.ext
  ext i
  simp

lemma continuous_toConvex : Continuous (toConvex (M := M)) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ M).continuous_iff]
  apply continuous_pi
  intro i
  simp only [Function.comp_apply, toConvex_weights]
  change Continuous (fun x : _root_.stdSimplex ℝ M ↦ x.val i)
  exact (continuous_apply i).comp continuous_subtype_val

lemma continuous_toOld : Continuous (toOld (M := M)) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i ↦ Convexity.StdSimplex.continuous_weights_apply ℝ i)

/-- The finite old/new simplex comparison, preserving each coordinate. -/
def homeomorph (M : Type*) [Fintype M] :
    _root_.stdSimplex ℝ M ≃ₜ Convexity.StdSimplex ℝ M where
  toFun := toConvex
  invFun := toOld
  left_inv := toOld_toConvex
  right_inv := toConvex_toOld
  continuous_toFun := continuous_toConvex
  continuous_invFun := continuous_toOld

@[simp] lemma homeomorph_apply (x : _root_.stdSimplex ℝ M) :
    homeomorph M x = toConvex x := rfl

@[simp] lemma homeomorph_symm_apply (x : Convexity.StdSimplex ℝ M) :
    (homeomorph M).symm x = toOld x := rfl

/-- Naturality holds for arbitrary maps between finite vertex sets. -/
lemma toConvex_map (f : M → N) (x : _root_.stdSimplex ℝ M) :
    toConvex (_root_.stdSimplex.map f x) = Convexity.StdSimplex.map f (toConvex x) := by
  classical
  apply Convexity.StdSimplex.ext
  ext j
  simp only [toConvex_weights, _root_.stdSimplex.map_coe,
    FunOnFinite.linearMap_apply_apply, Convexity.StdSimplex.weights_map,
    Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.single_apply, toConvex_weights]
  simp [Finset.sum_filter]

lemma toOld_map (f : M → N) (x : Convexity.StdSimplex ℝ M) :
    toOld (Convexity.StdSimplex.map f x) = _root_.stdSimplex.map f (toOld x) := by
  apply (homeomorph N).injective
  simpa using (toConvex_map f (toOld x)).symm

@[simp] lemma toConvex_vertex [DecidableEq M] (i : M) :
    toConvex (_root_.stdSimplex.vertex i) = Convexity.StdSimplex.single i := by
  apply Convexity.StdSimplex.ext
  ext j
  simp [toConvex_weights, _root_.stdSimplex.vertex_coe, Finsupp.single_apply,
    Pi.single_apply, eq_comm]

@[simp] lemma toOld_single [DecidableEq M] (i : M) :
    toOld (Convexity.StdSimplex.single i) = _root_.stdSimplex.vertex i := by
  apply (homeomorph M).injective
  simp

/-- The old and new interval parametrizations have the same orientation. -/
@[simp] lemma interval_compat (x : _root_.stdSimplex ℝ (Fin 2)) :
    Convexity.StdSimplex.homeomorphI (toConvex x) =
      stdSimplexHomeomorphUnitInterval x := by
  apply Subtype.ext
  rw [Convexity.StdSimplex.homeomorphI_apply_coe, toConvex_weights]
  rfl

/-- Compatibility including the universe lift used by `TopCat.I`. -/
lemma interval_ulift_compat (x : _root_.stdSimplex ℝ (Fin 2)) :
    (Homeomorph.ulift.symm : unitInterval ≃ₜ TopCat.I)
      (Convexity.StdSimplex.homeomorphI (toConvex x)) =
      (Homeomorph.ulift.symm : unitInterval ≃ₜ TopCat.I) (stdSimplexHomeomorphUnitInterval x) := by
  rw [interval_compat]

end LegacyCoordinates

/-- The realization homeomorphism in Mathlib's finitely supported coordinates. -/
def toTopHomeomorph (n : SimplexCategory) :
    |SSet.stdSimplex.obj n| ≃ₜ Convexity.StdSimplex ℝ (Fin (n.len + 1)) :=
  SimplexCategory.toTopHomeo n

lemma toTopHomeomorph_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : |SSet.stdSimplex.obj n|) :
    toTopHomeomorph m (SSet.toTop.map (SSet.stdSimplex.map f) x) =
      Convexity.StdSimplex.map f (toTopHomeomorph n x) :=
  SimplexCategory.toTopHomeo_naturality_apply f x

lemma toTopHomeomorph_symm_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    (toTopHomeomorph m).symm (Convexity.StdSimplex.map f x) =
    SSet.toTop.map (SSet.stdSimplex.map f) ((toTopHomeomorph n).symm x) :=
  SimplexCategory.toTopHomeo_symm_naturality_apply f x

lemma realization_interval_compat (x : |(Δ[1] : SSet)|) :
    (Homeomorph.ulift.symm : unitInterval ≃ₜ TopCat.I)
      (Convexity.StdSimplex.homeomorphI (toTopHomeomorph ⦋1⦌ x)) =
      SSet.stdSimplex.toTopObjIsoI.hom x := rfl

end FiniteSimplexAdapter

attribute [colib_tag "COL-0059",
  colib_ref "WeibelKBook" "IV, Characterization 3.1(2) and Definition 3.1.4" "background"
    "Standard-simplex realization background only, not this finite coordinate API comparison"]
  FiniteSimplexAdapter.homeomorph
  FiniteSimplexAdapter.toTopHomeomorph
  FiniteSimplexAdapter.realization_interval_compat
