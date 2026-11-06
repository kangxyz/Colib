/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.SkeletalCartesianCharts
public import Colib.CategoryTheory.TheoremB.ReplacementProjectionTower
public import Colib.Topology.Realization.CartesianProducts
public import Colib.Topology.HomotopyPullback.Symmetry

/-!
# Exact base coordinates and nondegenerate simplex-chart descent

Point-valued restricted replacements are identified with their actual base
subcomplexes. Every simplex chart is obtained from its nondegenerate ancestor
by a canonical enriched map with an invertible coefficient transition.
-/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremB/SkeletalCartesianCoordinates.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd, retaining the actual replacement charts,
base restrictions and canonical comparisons. -/
@[expose] public section

open CategoryTheory.TheoremA SSet Topology Topology.HomotopyPullback
open CategoryTheory.TheoremB


noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremB.Skeletal
open TheoremA TheoremB
variable {D : Type u} [SmallCategory D]

/-- The unique simplex in each degree of the zero-simplex, used in point-valued replacement
coordinates. -/
local instance pointSimplexUnique (p : SimplexCategoryᵒᵖ) :
    Unique ((Δ[0] : SSet.{u}).obj p) :=
  (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := p)).unique

/-- The point-valued restricted replacement is its actual base subcomplex. -/
def pointRestrictionIso (A : (nerve D).Subcomplex) :
    diagonalSSet (replacementRestriction pointDiagram A) ≅ A :=
  NatIso.ofComponents (fun p ↦ Equiv.toIso
    { toFun := fun x ↦ x.1
      invFun := fun a ↦ ⟨a, (default : (Δ[0] : SSet.{u}).obj p)⟩
      left_inv := fun x ↦ by
        rcases x with ⟨i, x⟩
        exact congrArg (Sigma.mk i)
          (@Subsingleton.elim ((Δ[0] : SSet.{u}).obj p) inferInstance _ _)
      right_inv := fun _ ↦ rfl }) (by
    intro p q α
    ext x : 3
    rfl)

@[simp] theorem pointRestrictionIso_hom (A : (nerve D).Subcomplex) :
    (pointRestrictionIso A).hom = restrictionProjection pointDiagram A := rfl

variable (H : D ⥤ SSet.{u})

/-- Base restriction inclusions commute with their actual projections. -/
@[reassoc] theorem restrictionProjection_inclusion {A B : (nerve D).Subcomplex}
    (h : A ≤ B) :
    diagonalMap (replacementRestrictionInclusion H h) ≫ restrictionProjection H B =
      restrictionProjection H A ≫ SSet.Subcomplex.homOfLE h := rfl

/-- Point-coordinate identifications commute with the exact restriction inclusions. -/
@[reassoc] theorem pointRestrictionIso_inclusion {A B : (nerve D).Subcomplex}
    (h : A ≤ B) :
    diagonalMap (replacementRestrictionInclusion pointDiagram h) ≫
      (pointRestrictionIso B).hom =
      (pointRestrictionIso A).hom ≫ SSet.Subcomplex.homOfLE h := rfl

/-- Point augmentation followed by the base coordinates is exactly the projection. -/
@[reassoc] theorem pointRestrictionIso_augmentation (A : (nerve D).Subcomplex) :
    diagonalMap (replacementRestrictionMap (replacementPointAugmentation H) A) ≫
      (pointRestrictionIso A).hom = restrictionProjection H A := rfl

/-- The prescribed characteristic simplex map to an actual base restriction. -/
def baseSimplexMap (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) : Δ[n] ⟶ A :=
  SSet.yonedaEquiv.symm ⟨s, hs⟩

/-- Exact projection square of every actual enriched simplex chart. -/
@[reassoc] theorem simplexChart_projection (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) :
    diagonalMap (simplexChart H A s hs) ≫ restrictionProjection H A =
      outerProjection Δ[n] (H.obj (s.obj 0)) ≫ baseSimplexMap A s hs := rfl

/-- The strict square obtained by realizing a simplex chart. -/
theorem realizedSimplexChart_square (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) :
    SSet.toTop.map (diagonalMap (simplexChart H A s hs)) ≫
        SSet.toTop.map (restrictionProjection H A) =
      SSet.toTop.map (outerProjection Δ[n] (H.obj (s.obj 0))) ≫
        SSet.toTop.map (baseSimplexMap A s hs) := by
  rw [← Functor.map_comp, ← Functor.map_comp, simplexChart_projection]

/-- The canonical constant-path comparison of one actual simplex chart is
an ordinary homotopy equivalence. -/
def ChartCartesian (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) : Prop :=
  Cartesian (SSet.toTop.map (outerProjection Δ[n] (H.obj (s.obj 0)))).hom
    (SSet.toTop.map (restrictionProjection H A)).hom
    (SSet.toTop.map (diagonalMap (simplexChart H A s hs))).hom
    (SSet.toTop.map (baseSimplexMap A s hs)).hom
    (congrArg TopCat.Hom.hom (realizedSimplexChart_square H A s hs))

/-- Base simplex operators preserve the prescribed characteristic map. -/
theorem baseSimplexMap_operator (A : (nerve D).Subcomplex) {n k : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌))
    (α : ⦋k⦌ ⟶ ⦋n⦌) :
    SSet.stdSimplex.map α ≫ baseSimplexMap A s hs =
      baseSimplexMap A ((nerve D).map α.op s) (A.map α.op hs) :=
  SSet.yonedaEquiv_symm_naturality_left _ _

/-- The inverse first-vertex coefficient transition expresses a degenerate
chart as the exact enriched map to its ancestor chart. -/
theorem simplexChart_epi_factor (A : (nerve D).Subcomplex) {n k : ℕ}
    (s : (nerve D).obj (op ⦋k⦌)) (hs : s ∈ A.obj (op ⦋k⦌))
    (α : ⦋n⦌ ⟶ ⦋k⦌) [Epi α] :
    enrichedMap (SSet.stdSimplex.map α) (simplexChartEpiCoefficientIso H α s).inv ≫
      diagonalMap (simplexChart H A s hs) =
    diagonalMap (simplexChart H A ((nerve D).map α.op s) (A.map α.op hs)) := by
  let e := simplexChartEpiCoefficientIso H α s
  have hi : outerProductCoefficientMap (K := Δ[n]) e.inv ≫
      outerProductCoefficientMap e.hom = 𝟙 _ := by
    ext p q x : 5
    apply congrArg (Sigma.mk x.1)
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id q) x.2
  have he := congrArg (fun f ↦ outerProductCoefficientMap (K := Δ[n]) e.inv ≫ f)
    (simplexChart_operator H A s hs α)
  change outerProductCoefficientMap e.inv ≫ outerProductMap (SSet.stdSimplex.map α) ≫
      simplexChart H A s hs = outerProductCoefficientMap e.inv ≫
      outerProductCoefficientMap e.hom ≫
        simplexChart H A ((nerve D).map α.op s) (A.map α.op hs) at he
  rw [← Category.assoc (outerProductCoefficientMap e.inv)
    (outerProductCoefficientMap e.hom), hi, Category.id_comp] at he
  change diagonalMap (outerProductCoefficientMap e.inv ≫
      outerProductMap (SSet.stdSimplex.map α) ≫ simplexChart H A s hs) = _
  exact congrArg diagonalMap he

/-- Cartesian ancestor charts give the genuine chart of every simplicial
degeneracy, with its prescribed coefficient and base maps. -/
theorem ChartCartesian.of_epi (A : (nerve D).Subcomplex) {n k : ℕ}
    (s : (nerve D).obj (op ⦋k⦌)) (hs : s ∈ A.obj (op ⦋k⦌))
    (α : ⦋n⦌ ⟶ ⦋k⦌) [Epi α] (h : ChartCartesian H A s hs) :
    ChartCartesian H A ((nerve D).map α.op s) (A.map α.op hs) := by
  let : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
  let : CompactSpace |(Δ[k] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋k⦌).symm.compactSpace
  let : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  let : T2Space |(Δ[k] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋k⦌).symm.t2Space
  let e := simplexChartEpiCoefficientIso H α s
  have hprod := enrichedMap_cartesian (SSet.stdSimplex.map α) e.inv
    (TopCat.homeoOfIso (SSet.toTop.mapIso e.symm)).toHomotopyEquiv rfl
  have hpaste := hprod.paste h
  have hf : SSet.toTop.map (enrichedMap (SSet.stdSimplex.map α) e.inv) ≫
      SSet.toTop.map (diagonalMap (simplexChart H A s hs)) =
      SSet.toTop.map (diagonalMap
        (simplexChart H A ((nerve D).map α.op s) (A.map α.op hs))) := by
    rw [← Functor.map_comp, simplexChart_epi_factor]
  have hg : SSet.toTop.map (SSet.stdSimplex.map α) ≫
      SSet.toTop.map (baseSimplexMap A s hs) =
      SSet.toTop.map (baseSimplexMap A ((nerve D).map α.op s) (A.map α.op hs)) := by
    rw [← Functor.map_comp, baseSimplexMap_operator]
  change Cartesian _ _
    (SSet.toTop.map (enrichedMap (SSet.stdSimplex.map α) e.inv) ≫
      SSet.toTop.map (diagonalMap (simplexChart H A s hs))).hom
    (SSet.toTop.map (SSet.stdSimplex.map α) ≫ SSet.toTop.map (baseSimplexMap A s hs)).hom _
    at hpaste
  simpa only [hf, hg, ChartCartesian] using hpaste

/-- Nondegenerate charts suffice for every simplex in the same actual
restriction; no additional cartesian conclusion is assumed. -/
theorem chartCartesian_of_nondegenerate (A : (nerve D).Subcomplex)
    (h : ∀ (k : ℕ) (t : (nerve D).nonDegenerate k)
      (ht : t.1 ∈ A.obj (op ⦋k⦌)), ChartCartesian H A t.1 ht)
    {n : ℕ} (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) :
    ChartCartesian H A s hs := by
  obtain ⟨k, α, hα, t, ht, rfl⟩ := exists_nondegenerate_in_restriction A s hs
  exact ChartCartesian.of_epi H A t.1 ht α (h k t ht)

/-- Actual base coordinates for a point-valued restricted realization. -/
def pointRestrictionHomeomorph (A : (nerve D).Subcomplex) :
    |diagonalSSet (replacementRestriction pointDiagram A)| ≃ₜ |(A : SSet.{u})| :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (pointRestrictionIso A))

/-- The tower augmentation is exactly the base projection in these coordinates. -/
@[reassoc] theorem pointRestrictionIso_projectionTower (n : ℕ) :
    (replacementProjectionTowerMap H).app n ≫
      (SSet.toTop.mapIso (pointRestrictionIso ((nerve D).skeleton n))).hom =
      SSet.toTop.map (restrictionProjection H ((nerve D).skeleton n)) := by
  change SSet.toTop.map _ ≫ SSet.toTop.map _ = _
  rw [← Functor.map_comp]
  exact congrArg SSet.toTop.map (pointRestrictionIso_augmentation H ((nerve D).skeleton n))

/-- The base tower transition is the actual skeleton inclusion in point coordinates. -/
@[reassoc] theorem pointRestrictionIso_baseTower {k n : ℕ} (h : k ≤ n) :
    (realizedReplacementSkeleton (pointDiagram (D := D))).map (homOfLE h) ≫
      (SSet.toTop.mapIso (pointRestrictionIso ((nerve D).skeleton n))).hom =
      (SSet.toTop.mapIso (pointRestrictionIso ((nerve D).skeleton k))).hom ≫
        SSet.toTop.map (SSet.Subcomplex.homOfLE ((nerve D).skeleton.monotone h)) := by
  change SSet.toTop.map _ ≫ SSet.toTop.map _ = SSet.toTop.map _ ≫ SSet.toTop.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg SSet.toTop.map (pointRestrictionIso_inclusion ((nerve D).skeleton.monotone h))

/-- The strict realized square of a base-restriction inclusion. -/
theorem realizedRestriction_square {A B : (nerve D).Subcomplex} (h : A ≤ B) :
    SSet.toTop.map (diagonalMap (replacementRestrictionInclusion H h)) ≫
      SSet.toTop.map (restrictionProjection H B) =
    SSet.toTop.map (restrictionProjection H A) ≫
      SSet.toTop.map (SSet.Subcomplex.homOfLE h) := by
  rw [← Functor.map_comp, ← Functor.map_comp, restrictionProjection_inclusion]

/-- Canonical cartesianness of an inclusion over its actual base subcomplexes. -/
def RestrictionCartesian {A B : (nerve D).Subcomplex} (h : A ≤ B) : Prop :=
  Cartesian (SSet.toTop.map (restrictionProjection H A)).hom
    (SSet.toTop.map (restrictionProjection H B)).hom
    (SSet.toTop.map (diagonalMap (replacementRestrictionInclusion H h))).hom
    (SSet.toTop.map (SSet.Subcomplex.homOfLE h)).hom
    (congrArg TopCat.Hom.hom (realizedRestriction_square H h))

/-- Base characteristic maps are unchanged by enlarging their restriction. -/
@[reassoc] theorem baseSimplexMap_inclusion {A B : (nerve D).Subcomplex} (h : A ≤ B)
    {n : ℕ} (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) :
    baseSimplexMap A s hs ≫ SSet.Subcomplex.homOfLE h =
      baseSimplexMap B s (h _ hs) := rfl

/-- Old canonical charts propagate through a canonical cartesian restriction inclusion. -/
theorem ChartCartesian.enlarge {A B : (nerve D).Subcomplex} (h : A ≤ B)
    {n : ℕ} (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌))
    (hc : ChartCartesian H A s hs) (hi : RestrictionCartesian H h) :
    ChartCartesian H B s (h _ hs) := by
  have hpaste := hc.paste hi
  have hf : SSet.toTop.map (diagonalMap (simplexChart H A s hs)) ≫
      SSet.toTop.map (diagonalMap (replacementRestrictionInclusion H h)) =
      SSet.toTop.map (diagonalMap (simplexChart H B s (h _ hs))) := by
    rw [← Functor.map_comp]
    rfl
  have hg : SSet.toTop.map (baseSimplexMap A s hs) ≫
      SSet.toTop.map (SSet.Subcomplex.homOfLE h) =
      SSet.toTop.map (baseSimplexMap B s (h _ hs)) := by
    rw [← Functor.map_comp, baseSimplexMap_inclusion]
  change Cartesian _ _
    (SSet.toTop.map (diagonalMap (simplexChart H A s hs)) ≫
      SSet.toTop.map (diagonalMap (replacementRestrictionInclusion H h))).hom
    (SSet.toTop.map (baseSimplexMap A s hs) ≫
      SSet.toTop.map (SSet.Subcomplex.homOfLE h)).hom _ at hpaste
  simpa only [hf, hg, ChartCartesian] using hpaste

/-- Canonical restriction comparisons compose over the actual base inclusions. -/
theorem RestrictionCartesian.trans {A B C : (nerve D).Subcomplex}
    {h : A ≤ B} {h' : B ≤ C} (hc : RestrictionCartesian H h)
    (hc' : RestrictionCartesian H h') : RestrictionCartesian H (h.trans h') := by
  have hpaste := hc.paste hc'
  have hf : SSet.toTop.map (diagonalMap (replacementRestrictionInclusion H h)) ≫
      SSet.toTop.map (diagonalMap (replacementRestrictionInclusion H h')) =
      SSet.toTop.map (diagonalMap (replacementRestrictionInclusion H (h.trans h'))) := by
    rw [← Functor.map_comp]
    rfl
  have hg : SSet.toTop.map (SSet.Subcomplex.homOfLE h) ≫
      SSet.toTop.map (SSet.Subcomplex.homOfLE h') =
      SSet.toTop.map (SSet.Subcomplex.homOfLE (h.trans h')) := by
    rw [← Functor.map_comp]
    rfl
  change Cartesian _ _
    (SSet.toTop.map (diagonalMap (replacementRestrictionInclusion H h)) ≫
      SSet.toTop.map (diagonalMap (replacementRestrictionInclusion H h'))).hom
    (SSet.toTop.map (SSet.Subcomplex.homOfLE h) ≫
      SSet.toTop.map (SSet.Subcomplex.homOfLE h')).hom _ at hpaste
  simpa only [hf, hg, RestrictionCartesian] using hpaste

/-- A restriction is canonically cartesian over itself. -/
theorem RestrictionCartesian.refl (A : (nerve D).Subcomplex) :
    RestrictionCartesian H (le_refl A) := by
  change Cartesian (SSet.toTop.map (restrictionProjection H A)).hom
    (SSet.toTop.map (restrictionProjection H A)).hom
    (SSet.toTop.map (𝟙 _)).hom (SSet.toTop.map (𝟙 _)).hom _
  let p := (SSet.toTop.map (restrictionProjection H A)).hom
  have hc : Cartesian p p (ContinuousMap.id _) (ContinuousMap.id _) rfl := by
    refine ⟨(HomotopyPullback.identityHomotopyEquiv p).trans
      (HomotopyPullback.symmetryHomeomorph (ContinuousMap.id _) p).toHomotopyEquiv, ?_⟩
    rfl
  exact hc.congr rfl rfl (by simp) (by simp)

end CategoryTheory.TheoremB.Skeletal
