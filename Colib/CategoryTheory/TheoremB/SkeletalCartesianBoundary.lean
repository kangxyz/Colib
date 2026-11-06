/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.CartesianDomains
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianCoordinates

/-! # Actual finite-face assembly of replacement boundary charts -/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremB/SkeletalCartesianBoundary.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd, retaining the actual replacement charts,
base restrictions and canonical comparisons. -/
@[expose] public section

open CategoryTheory.TheoremA SSet Topology.HomotopyPullback


noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremB.Skeletal
open TheoremA Topology.Realization.CartesianDomains
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The actual simplicial base map of an arbitrary restricted chart. -/
def restrictedBaseSimplexMap (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (K : (Δ[n] : SSet.{u}).Subcomplex)
    (hs : ∀ (p : SimplexCategoryᵒᵖ) (a : K.obj p),
      (nerve D).map a.1.down.op s ∈ A.obj p) : (K : SSet.{u}) ⟶ (A : SSet.{u}) where
  app p := ↾fun a ↦ ⟨(nerve D).map a.1.down.op s, hs p a⟩
  naturality _ _ _ := rfl

/-- Index projections commute with actual restricted characteristic maps. -/
theorem restrictedSimplexChart_projection (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (K : (Δ[n] : SSet.{u}).Subcomplex)
    (hs : ∀ (p : SimplexCategoryᵒᵖ) (a : K.obj p),
      (nerve D).map a.1.down.op s ∈ A.obj p) :
    diagonalMap (restrictedSimplexChart H A s K hs) ≫ restrictionProjection H A =
      outerProjection K (H.obj (s.obj 0)) ≫ restrictedBaseSimplexMap A s K hs := rfl

/-- The exact square of actual realized restricted charts. -/
theorem realizedRestrictedSimplexChart_square (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (K : (Δ[n] : SSet.{u}).Subcomplex)
    (hs : ∀ (p : SimplexCategoryᵒᵖ) (a : K.obj p),
      (nerve D).map a.1.down.op s ∈ A.obj p) :
    SSet.toTop.map (diagonalMap (restrictedSimplexChart H A s K hs)) ≫
      SSet.toTop.map (restrictionProjection H A) =
    domainProjection (H.obj (s.obj 0)) K ≫
      SSet.toTop.map (restrictedBaseSimplexMap A s K hs) := by
  change SSet.toTop.map _ ≫ SSet.toTop.map _ = SSet.toTop.map _ ≫ SSet.toTop.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Each genuine face chart factors through its diagram transition and
its actual (possibly degenerate) simplex chart in the target restriction. -/
theorem restrictedSimplexChart_yoneda (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (K : (Δ[n] : SSet.{u}).Subcomplex)
    (hs : ∀ (p : SimplexCategoryᵒᵖ) (a : K.obj p),
      (nerve D).map a.1.down.op s ∈ A.obj p)
    {k : ℕ} (a : K.obj (op ⦋k⦌)) :
    outerProductMap (SSet.yonedaEquiv.symm a) ≫ restrictedSimplexChart H A s K hs =
      outerProductCoefficientMap (K := Δ[k]) (H.map (firstVertexEdge a.1.down.op s)) ≫
        simplexChart H A ((nerve D).map a.1.down.op s) (hs _ a) := by
  ext p q x : 5
  change (⟨⟨(nerve D).map (a.1.down.op ≫ x.1.down.op) s, _⟩,
    (H.map (firstVertexEdge (a.1.down.op ≫ x.1.down.op) s)).app q x.2⟩ :
    ((replacementRestriction H A).obj p).obj q) = _
  rw [firstVertexEdge_comp, H.map_comp]
  rfl

/-- The base map of an individual restricted face is its actual simplex
characteristic map into the target subcomplex. -/
theorem restrictedBaseSimplexMap_yoneda (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (K : (Δ[n] : SSet.{u}).Subcomplex)
    (hs : ∀ (p : SimplexCategoryᵒᵖ) (a : K.obj p),
      (nerve D).map a.1.down.op s ∈ A.obj p)
    {k : ℕ} (a : K.obj (op ⦋k⦌)) :
    SSet.yonedaEquiv.symm a ≫ restrictedBaseSimplexMap A s K hs =
      baseSimplexMap A ((nerve D).map a.1.down.op s) (hs _ a) := rfl

/-- Actual finite-face assembly: if all characteristic charts in a target
restriction are cartesian and its diagram transitions are equivalences,
then every finite-dimensional restricted chart is cartesian. This proves
the entire boundary comparison from its faces rather than assuming it. -/
theorem restrictedSimplexChart_cartesian
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom)
    (A : (nerve D).Subcomplex)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ A.obj (op ⦋k⦌)), ChartCartesian H A v hv)
    {n : ℕ} (s : (nerve D).obj (op ⦋n⦌))
    (K : (Δ[n] : SSet.{u}).Subcomplex)
    (hs : ∀ (p : SimplexCategoryᵒᵖ) (a : K.obj p),
      (nerve D).map a.1.down.op s ∈ A.obj p)
    (N : ℕ) [SSet.HasDimensionLT (K : SSet.{u}) N] :
    Cartesian (domainProjection (H.obj (s.obj 0)) K).hom
      (SSet.toTop.map (restrictionProjection H A)).hom
      (SSet.toTop.map (diagonalMap (restrictedSimplexChart H A s K hs))).hom
      (SSet.toTop.map (restrictedBaseSimplexMap A s K hs)).hom
      (congrArg TopCat.Hom.hom (realizedRestrictedSimplexChart_square H A s K hs)) := by
  apply finiteDomain_cartesian (SSet.toTop.map (restrictionProjection H A))
    (H.obj (s.obj 0)) K
    (SSet.toTop.map (restrictedBaseSimplexMap A s K hs))
    (SSet.toTop.map (diagonalMap (restrictedSimplexChart H A s K hs)))
    (realizedRestrictedSimplexChart_square H A s K hs) N
  intro k f
  obtain ⟨a, rfl⟩ := SSet.yonedaEquiv.symm.surjective f
  let : CompactSpace |(Δ[k] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋k⦌).symm.compactSpace
  let : T2Space |(Δ[k] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋k⦌).symm.t2Space
  obtain ⟨e, he⟩ := htrans (firstVertexEdge a.1.down.op s)
  have hprod := enrichedMap_cartesian (𝟙 (Δ[k] : SSet.{u}))
    (H.map (firstVertexEdge a.1.down.op s)) e he
  have hpaste := hprod.paste (hchart k ((nerve D).map a.1.down.op s) (hs _ a))
  have hf : SSet.toTop.map (enrichedMap (𝟙 (Δ[k] : SSet.{u}))
      (H.map (firstVertexEdge a.1.down.op s))) ≫
      SSet.toTop.map (diagonalMap
        (simplexChart H A ((nerve D).map a.1.down.op s) (hs _ a))) =
    (realizedOuterProductFunctor (H.obj (s.obj 0))).map (SSet.yonedaEquiv.symm a) ≫
      SSet.toTop.map (diagonalMap (restrictedSimplexChart H A s K hs)) := by
    change SSet.toTop.map _ ≫ SSet.toTop.map _ = SSet.toTop.map _ ≫ SSet.toTop.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg SSet.toTop.map
      (congrArg diagonalMap (restrictedSimplexChart_yoneda H A s K hs a)).symm
  have hg : SSet.toTop.map (𝟙 (Δ[k] : SSet.{u})) ≫
      SSet.toTop.map (baseSimplexMap A ((nerve D).map a.1.down.op s) (hs _ a)) =
    SSet.toTop.map (SSet.yonedaEquiv.symm a) ≫
      SSet.toTop.map (restrictedBaseSimplexMap A s K hs) := by
    rw [← Functor.map_comp, Category.id_comp, ← restrictedBaseSimplexMap_yoneda A s K hs a,
      Functor.map_comp]
  change Cartesian _ _
    (SSet.toTop.map (enrichedMap (𝟙 (Δ[k] : SSet.{u}))
      (H.map (firstVertexEdge a.1.down.op s))) ≫
      SSet.toTop.map (diagonalMap
        (simplexChart H A ((nerve D).map a.1.down.op s) (hs _ a)))).hom
    (SSet.toTop.map (𝟙 (Δ[k] : SSet.{u})) ≫
      SSet.toTop.map (baseSimplexMap A ((nerve D).map a.1.down.op s) (hs _ a))).hom _ at hpaste
  exact hpaste.congr rfl rfl (congrArg TopCat.Hom.hom hf) (congrArg TopCat.Hom.hom hg)

/-- The actual attaching map of a nondegenerate simplex on the base. -/
abbrev boundaryBaseMap {n : ℕ} (s : (nerve D).nonDegenerate n) :
    (∂Δ[n] : SSet.{u}) ⟶ ((nerve D).skeleton n : SSet.{u}) :=
  restrictedBaseSimplexMap ((nerve D).skeleton n) s.1 ∂Δ[n]
    (fun _ a ↦ replacementBaseCell_boundary s a)

/-- The boundary-to-previous-skeleton cartesian comparison is derived by
finite face assembly under the simultaneous chart induction hypothesis. -/
theorem replacementCellAttaching_cartesian
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartCartesian H ((nerve D).skeleton n) v hv)
    (s : (nerve D).nonDegenerate n) :
    Cartesian (domainProjection (H.obj (s.1.obj 0)) (∂Δ[n] : SSet.{u})).hom
      (SSet.toTop.map (restrictionProjection H ((nerve D).skeleton n))).hom
      (SSet.toTop.map (diagonalMap (replacementCellAttaching H s))).hom
      (SSet.toTop.map (boundaryBaseMap s)).hom
      (congrArg TopCat.Hom.hom
        (realizedRestrictedSimplexChart_square H ((nerve D).skeleton n) s.1 ∂Δ[n]
          (fun _ a ↦ replacementBaseCell_boundary s a))) :=
  restrictedSimplexChart_cartesian H htrans ((nerve D).skeleton n) hchart
    s.1 ∂Δ[n] (fun _ a ↦ replacementBaseCell_boundary s a) n

end CategoryTheory.TheoremB.Skeletal
