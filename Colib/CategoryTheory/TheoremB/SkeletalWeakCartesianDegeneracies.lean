/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.SkeletalWeakCartesianCharts
public import Colib.CategoryTheory.TheoremB.WeakCartesianProducts

/-! # Degenerate characteristic charts for arbitrary coefficient transformations

Implementation provenance:
`Quillen/CategoryTheory/TheoremB/SkeletalWeakCartesianDegeneracies.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA


noncomputable section
open Topology TopCat SSet Topology.HomotopyPullback
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

/-- The two genuine inverse coefficient isomorphisms commute with η. -/
theorem simplexChartEpiCoefficientIso_naturality {n k : ℕ} (α : ⦋n⦌ ⟶ ⦋k⦌) [Epi α]
    (s : (nerve D).obj (op ⦋k⦌)) :
    (simplexChartEpiCoefficientIso H α s).inv ≫ η.app (s.obj 0) =
      η.app (((nerve D).map α.op s).obj 0) ≫ (simplexChartEpiCoefficientIso J α s).inv := by
  let eH := simplexChartEpiCoefficientIso H α s
  let eJ := simplexChartEpiCoefficientIso J α s
  have hn : eH.hom ≫ η.app (((nerve D).map α.op s).obj 0) =
      η.app (s.obj 0) ≫ eJ.hom := η.naturality (firstVertexEdge α.op s)
  apply (cancel_mono eJ.hom).1
  change eH.inv ≫ η.app (s.obj 0) ≫ eJ.hom =
    (η.app (((nerve D).map α.op s).obj 0) ≫ eJ.inv) ≫ eJ.hom
  rw [← hn, eH.inv_hom_id_assoc, Category.assoc, eJ.inv_hom_id, Category.comp_id]

/-- An ancestor chart gives each original degenerate chart. The required
horizontal coefficient maps are actual inverse isomorphisms, so no transition
weakness is assumed for this descent. -/
theorem ChartWeakCartesian.of_epi (A : (nerve D).Subcomplex) {n k : ℕ}
    (s : (nerve D).obj (op ⦋k⦌)) (hs : s ∈ A.obj (op ⦋k⦌))
    (α : ⦋n⦌ ⟶ ⦋k⦌) [Epi α] (h : ChartWeakCartesian η A s hs) :
    ChartWeakCartesian η A ((nerve D).map α.op s) (A.map α.op hs) := by
  let : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
  let : CompactSpace |(Δ[k] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋k⦌).symm.compactSpace
  let : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  let : T2Space |(Δ[k] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋k⦌).symm.t2Space
  let eH := simplexChartEpiCoefficientIso H α s
  let eJ := simplexChartEpiCoefficientIso J α s
  have hw : SSet.toTop.map eH.inv ≫ SSet.toTop.map (η.app (s.obj 0)) =
      SSet.toTop.map (η.app (((nerve D).map α.op s).obj 0)) ≫ SSet.toTop.map eJ.inv := by
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp,
      simplexChartEpiCoefficientIso_naturality]
  have hc := (cartesianOfHorizontalHomeomorphs
    (SSet.toTop.map (η.app (((nerve D).map α.op s).obj 0))).hom
    (SSet.toTop.map (η.app (s.obj 0))).hom
    (TopCat.homeoOfIso (SSet.toTop.mapIso eH.symm))
    (TopCat.homeoOfIso (SSet.toTop.mapIso eJ.symm))
    (congrArg TopCat.Hom.hom hw)).weak
  have hp := enrichedCoefficient_weakCartesian (SSet.stdSimplex.map α)
    (η.app (((nerve D).map α.op s).obj 0)) (η.app (s.obj 0)) eH.inv eJ.inv
    (simplexChartEpiCoefficientIso_naturality η α s) hc
  have hh := hp.paste h
  have hf : SSet.toTop.map (enrichedMap (SSet.stdSimplex.map α) eH.inv) ≫
      realizationFunctor.map (simplexChart H A s hs) =
      realizationFunctor.map (simplexChart H A ((nerve D).map α.op s) (A.map α.op hs)) := by
    change SSet.toTop.map _ ≫ SSet.toTop.map _ = SSet.toTop.map _
    rw [← SSet.toTop.map_comp]
    exact congrArg SSet.toTop.map (simplexChart_epi_factor H A s hs α)
  have hg : SSet.toTop.map (enrichedMap (SSet.stdSimplex.map α) eJ.inv) ≫
      realizationFunctor.map (simplexChart J A s hs) =
      realizationFunctor.map (simplexChart J A ((nerve D).map α.op s) (A.map α.op hs)) := by
    change SSet.toTop.map _ ≫ SSet.toTop.map _ = SSet.toTop.map _
    rw [← SSet.toTop.map_comp]
    exact congrArg SSet.toTop.map (simplexChart_epi_factor J A s hs α)
  exact hh.congr rfl rfl (congrArg TopCat.Hom.hom hf) (congrArg TopCat.Hom.hom hg)

/-- Nondegenerate characteristic comparisons suffice in each actual restriction. -/
theorem chartWeakCartesian_of_nondegenerate (A : (nerve D).Subcomplex)
    (h : ∀ (k : ℕ) (t : (nerve D).nonDegenerate k)
      (ht : t.1 ∈ A.obj (op ⦋k⦌)), ChartWeakCartesian η A t.1 ht)
    {n : ℕ} (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) :
    ChartWeakCartesian η A s hs := by
  obtain ⟨k, α, hα, t, ht, rfl⟩ := exists_nondegenerate_in_restriction A s hs
  exact ChartWeakCartesian.of_epi η A t.1 ht α (h k t ht)

end CategoryTheory.TheoremB.Skeletal
