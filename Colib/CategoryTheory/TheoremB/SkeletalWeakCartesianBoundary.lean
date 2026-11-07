/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.SkeletalWeakCartesianCharts
public import Colib.CategoryTheory.TheoremB.WeakCartesianProducts
public import Colib.Topology.Realization.WeakCartesianDomains
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianBoundary

/-! # Finite-face assembly for arbitrary coefficient transformations

Implementation provenance:
`Quillen/CategoryTheory/TheoremB/SkeletalWeakCartesianBoundary.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA


noncomputable section
open Topology TopCat SSet Topology.HomotopyPullback
  Topology.Realization.CartesianDomains
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

/-- Weak original transition squares and all actual face charts imply the
original comparison for a finite-dimensional restricted characteristic map. -/
theorem restrictedSimplexChart_weakCartesian (htrans : TransitionWeakCartesian η)
    (A : (nerve D).Subcomplex)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ A.obj (op ⦋k⦌)), ChartWeakCartesian η A v hv)
    {n : ℕ} (s : (nerve D).obj (op ⦋n⦌))
    (K : (Δ[n] : SSet.{u}).Subcomplex)
    (hs : ∀ (p : SimplexCategoryᵒᵖ) (a : K.obj p),
      (nerve D).map a.1.down.op s ∈ A.obj p)
    (N : ℕ) [SSet.HasDimensionLT (K : SSet.{u}) N] :
    WeakCartesian
      (realizationFunctor.map (outerProductCoefficientMap (K := K) (η.app (s.obj 0)))).hom
      (realizedRestrictionTransformation η A).hom
      (realizationFunctor.map (restrictedSimplexChart H A s K hs)).hom
      (realizationFunctor.map (restrictedSimplexChart J A s K hs)).hom
      (congrArg TopCat.Hom.hom
        (realizedRestrictedSimplexChart_coefficient_square η A s K hs)) := by
  apply finiteCoefficientDomain_weakCartesian (realizedRestrictionTransformation η A)
    (η.app (s.obj 0)) K (realizationFunctor.map (restrictedSimplexChart J A s K hs))
    (realizationFunctor.map (restrictedSimplexChart H A s K hs))
    (realizedRestrictedSimplexChart_coefficient_square η A s K hs) N
  intro k f
  obtain ⟨a, rfl⟩ := SSet.yonedaEquiv.symm.surjective f
  let : CompactSpace |(Δ[k] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋k⦌).symm.compactSpace
  let : T2Space |(Δ[k] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋k⦌).symm.t2Space
  let e := firstVertexEdge a.1.down.op s
  have hp := enrichedCoefficient_weakCartesian (𝟙 (Δ[k] : SSet.{u}))
    (η.app (s.obj 0)) (η.app (((nerve D).map a.1.down.op s).obj 0))
    (H.map e) (J.map e) (η.naturality e) (htrans e)
  have hh := hp.paste (hchart k ((nerve D).map a.1.down.op s) (hs _ a))
  have hf : SSet.toTop.map (enrichedMap (𝟙 (Δ[k] : SSet.{u})) (H.map e)) ≫
      realizationFunctor.map (simplexChart H A ((nerve D).map a.1.down.op s) (hs _ a)) =
    (realizedOuterProductFunctor (H.obj (s.obj 0))).map (SSet.yonedaEquiv.symm a) ≫
      realizationFunctor.map (restrictedSimplexChart H A s K hs) := by
    change SSet.toTop.map _ ≫ SSet.toTop.map _ = SSet.toTop.map _ ≫ SSet.toTop.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg SSet.toTop.map
      (congrArg diagonalMap (restrictedSimplexChart_yoneda H A s K hs a)).symm
  have hg : SSet.toTop.map (enrichedMap (𝟙 (Δ[k] : SSet.{u})) (J.map e)) ≫
      realizationFunctor.map (simplexChart J A ((nerve D).map a.1.down.op s) (hs _ a)) =
    (realizedOuterProductFunctor (J.obj (s.obj 0))).map (SSet.yonedaEquiv.symm a) ≫
      realizationFunctor.map (restrictedSimplexChart J A s K hs) := by
    change SSet.toTop.map _ ≫ SSet.toTop.map _ = SSet.toTop.map _ ≫ SSet.toTop.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg SSet.toTop.map
      (congrArg diagonalMap (restrictedSimplexChart_yoneda J A s K hs a)).symm
  exact hh.congr rfl rfl (congrArg TopCat.Hom.hom hf) (congrArg TopCat.Hom.hom hg)

/-- The incoming attaching comparison is obtained from all faces, including
empty zero-dimensional boundaries, with no extra attaching-map hypothesis. -/
theorem replacementCellAttaching_weakCartesian (htrans : TransitionWeakCartesian η)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartWeakCartesian η ((nerve D).skeleton n) v hv)
    (s : (nerve D).nonDegenerate n) :
    WeakCartesian
      (realizationFunctor.map (outerProductCoefficientMap (K := (∂Δ[n] : SSet.{u}))
        (η.app (s.1.obj 0)))).hom (stageProjection η n).hom
      (realizationFunctor.map (replacementCellAttaching H s)).hom
      (realizationFunctor.map (replacementCellAttaching J s)).hom
      (congrArg TopCat.Hom.hom
        (realizedRestrictedSimplexChart_coefficient_square η ((nerve D).skeleton n) s.1 ∂Δ[n]
          (fun _ a ↦ replacementBaseCell_boundary s a))) :=
  restrictedSimplexChart_weakCartesian η htrans ((nerve D).skeleton n) hchart
    s.1 ∂Δ[n] (fun _ a ↦ replacementBaseCell_boundary s a) n

end CategoryTheory.TheoremB.Skeletal
