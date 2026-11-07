/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.PrismCoordinates
public import Colib.Topology.Realization.Simplex
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

/-!
# Cells of the realized standard prism

This file constructs the canonical continuous cylinder comparison and the
realized maximal prism cells. The cells cover the entire realization, and
adjacent cells agree on their common simplicial face.
-/
/-!
Adapted from Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The target uses the pinned native standard simplex and actual Mathlib prism cells.
The implementation retains the source maps, coordinates and universe parameters.
-/
@[expose] public section

noncomputable section

open stdSimplex CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory Opposite
open scoped Simplicial Topology unitInterval

universe u

namespace SSet

/-- The canonical continuous map from the realized simplicial cylinder to
the topological cylinder. -/
def realizationCylinderComparison (X : SSet.{u}) : |X ⊗ Δ[1]| ⟶ |X| ⊗ TopCat.I :=
  lift (SSet.toTop.map (fst X Δ[1]))
    (SSet.toTop.map (snd X Δ[1]) ≫ SSet.stdSimplex.toTopObjIsoI.hom)

@[simp]
theorem realizationCylinderComparison_fst (X : SSet.{u}) :
    realizationCylinderComparison X ≫ fst _ _ = SSet.toTop.map (fst X Δ[1]) := by
  simp [realizationCylinderComparison]

@[simp]
theorem realizationCylinderComparison_snd (X : SSet.{u}) :
    realizationCylinderComparison X ≫ snd _ _ =
      SSet.toTop.map (snd X Δ[1]) ≫ SSet.stdSimplex.toTopObjIsoI.hom := by
  simp [realizationCylinderComparison]

/-- Cylinder comparison is natural in the simplicial set. -/
theorem realizationCylinderComparison_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map (f ▷ Δ[1]) ≫ realizationCylinderComparison Y =
      realizationCylinderComparison X ≫ (SSet.toTop.map f ▷ TopCat.I) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [realizationCylinderComparison, ← Category.assoc, ← Functor.map_comp]

/-- A maximal cell in the standard simplicial prism, after geometric realization. -/
def realizationPrismCell {n : ℕ} (i : Fin (n + 1)) :
    |(Δ[n + 1] : SSet.{u})| ⟶ |(Δ[n] ⊗ Δ[1] : SSet.{u})| :=
  SSet.toTop.map (SSet.yonedaEquiv.symm
    (SSet.prodStdSimplex.nonDegenerateEquiv₁ i).val)

/-- The prism comparison in ordinary barycentric simplex and interval coordinates. -/
def realizationPrismCoordinates (n : ℕ) :
    C(|(Δ[n] ⊗ Δ[1] : SSet.{u})|, _root_.stdSimplex ℝ (Fin (n + 1)) × unitInterval) where
  toFun x := (SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (fst Δ[n] Δ[1]) x),
    stdSimplexHomeomorphUnitInterval
      (SimplexCategory.toTopHomeo ⦋1⦌ (SSet.toTop.map (snd Δ[n] Δ[1]) x)))
  continuous_toFun := by fun_prop

@[simp]
theorem realizationPrismCell_fst {n : ℕ} (i : Fin (n + 1)) :
    realizationPrismCell.{u} i ≫ SSet.toTop.map (fst Δ[n] Δ[1]) =
      SSet.toTop.map (SSet.stdSimplex.σ i) := by
  unfold realizationPrismCell
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

@[simp]
theorem realizationPrismCell_snd {n : ℕ} (i : Fin (n + 1)) :
    realizationPrismCell.{u} i ≫ SSet.toTop.map (snd Δ[n] Δ[1]) =
      SSet.toTop.map (SSet.stdSimplex.map
        (SSet.stdSimplex.objEquiv.{u} (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc))) := by
  unfold realizationPrismCell
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

/-- The first prism coordinate collapses the two copies of the split vertex. -/
theorem realizationPrismCoordinates_cell_fst {n : ℕ} (i : Fin (n + 1))
    (v : _root_.stdSimplex ℝ (Fin (n + 2))) :
    (realizationPrismCoordinates n (realizationPrismCell.{u} i
      ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm v))).1 = _root_.stdSimplex.map i.predAbove v := by
  change SimplexCategory.toTopHomeo ⦋n⦌ ((realizationPrismCell i ≫
    SSet.toTop.map (fst Δ[n] Δ[1])) _) = _
  rw [realizationPrismCell_fst]
  change SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map
    (SSet.stdSimplex.map (SimplexCategory.σ i)) _) = _
  rw [SimplexCategory.toTopHomeo_naturality_apply, Homeomorph.apply_symm_apply]
  rfl

/-- The second prism coordinate is the total mass above the cut. -/
theorem realizationPrismCoordinates_cell_snd {n : ℕ} (i : Fin (n + 1))
    (v : _root_.stdSimplex ℝ (Fin (n + 2))) :
    ((realizationPrismCoordinates n (realizationPrismCell.{u} i
      ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm v))).2 : ℝ) = prismHeight i v := by
  change (stdSimplexHomeomorphUnitInterval (SimplexCategory.toTopHomeo ⦋1⦌
    ((realizationPrismCell i ≫ SSet.toTop.map (snd Δ[n] Δ[1])) _)) : ℝ) = _
  rw [realizationPrismCell_snd, SimplexCategory.toTopHomeo_naturality_apply,
    Homeomorph.apply_symm_apply]
  change (FunOnFinite.linearMap ℝ ℝ
    (SSet.stdSimplex.objMk₁.{u} i.succ.castSucc) (v : Fin (n + 2) → ℝ)) 1 = _
  classical
  rw [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  unfold prismHeight
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [SSet.stdSimplex.objMk₁_apply_eq_one_iff]
  simp only [Fin.castSucc_le_castSucc_iff]
  rfl

/-- Every simplex in a standard prism is a face or degeneracy of a maximal prism cell. -/
theorem prism_simplex_factors {n : ℕ} {m : SimplexCategoryᵒᵖ}
    (s : (Δ[n] ⊗ Δ[1] : SSet.{u}).obj m) :
    ∃ (i : Fin (n + 1)) (f : m.unop ⟶ ⦋n + 1⦌),
      (Δ[n] ⊗ Δ[1]).map f.op (SSet.prodStdSimplex.nonDegenerateEquiv₁ i).val = s := by
  obtain ⟨d, f, _, y, hy⟩ := (Δ[n] ⊗ Δ[1] : SSet.{u}).exists_nonDegenerate s
  obtain ⟨z, hz⟩ := SSet.prodStdSimplex.exists_nonDegenerate_max_dim y rfl
  obtain ⟨i, rfl⟩ := SSet.prodStdSimplex.nonDegenerateEquiv₁.surjective z
  obtain ⟨g, hg⟩ := (SSet.Subcomplex.mem_ofSimplex_obj_iff _ _).mp hz
  refine ⟨i, f ≫ g, ?_⟩
  rw [op_comp, Functor.map_comp]
  change (Δ[n] ⊗ Δ[1]).map f.op ((Δ[n] ⊗ Δ[1]).map g.op _) = s
  rw [hg]
  exact hy.symm

/-- The finitely many maximal realized cells cover the standard prism. -/
theorem realizationPrismCell_jointly_surjective {n : ℕ}
    (x : |(Δ[n] ⊗ Δ[1] : SSet.{u})|) :
    ∃ (i : Fin (n + 1)) (t : |(Δ[n + 1] : SSet.{u})|), realizationPrismCell i t = x := by
  obtain ⟨m, f, t, rfl⟩ := realization_exists_simplex x
  obtain ⟨i, g, hg⟩ := prism_simplex_factors (SSet.yonedaEquiv f)
  refine ⟨i, SSet.toTop.map (SSet.stdSimplex.map g) t, ?_⟩
  change (SSet.toTop.map (SSet.stdSimplex.map g) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm _)) t = _
  rw [← Functor.map_comp]
  have heq : SSet.stdSimplex.map g ≫ SSet.yonedaEquiv.symm
      (SSet.prodStdSimplex.nonDegenerateEquiv₁ i).val = f := by
    apply SSet.yonedaEquiv.injective
    exact hg
  rw [heq]

/-- The realized standard prism is compact, as a finite union of compact maximal cells. -/
instance realizationPrism_compactSpace (n : ℕ) :
    CompactSpace |(Δ[n] ⊗ Δ[1] : SSet.{u})| := by
  let f : (Σ _ : Fin (n + 1), |(Δ[n + 1] : SSet.{u})|) →
      |(Δ[n] ⊗ Δ[1] : SSet.{u})| := fun z ↦ realizationPrismCell z.1 z.2
  have hf : Continuous f := by
    apply continuous_sigma
    intro i
    exact (realizationPrismCell i).hom.continuous
  exact Function.Surjective.compactSpace hf (fun x ↦ by
    obtain ⟨i, t, ht⟩ := realizationPrismCell_jointly_surjective x
    exact ⟨⟨i, t⟩, ht⟩)

/-- The actual enumerated staircase simplices share their adjacent face.
This replaces the two face formulas unavailable in the pinned Mathlib. -/
theorem prism_adjacent_simplex_face {n : ℕ} (i : Fin n) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}).δ i.castSucc.succ
        (SSet.prodStdSimplex.nonDegenerateEquiv₁ i.castSucc).val =
      (Δ[n] ⊗ Δ[1] : SSet.{u}).δ i.succ.castSucc
        (SSet.prodStdSimplex.nonDegenerateEquiv₁ i.succ).val := by
  apply Prod.ext
  · change (Δ[n] : SSet.{u}).δ i.castSucc.succ
        (SSet.stdSimplex.objEquiv.symm (SimplexCategory.σ i.castSucc)) =
      (Δ[n] : SSet.{u}).δ i.succ.castSucc
        (SSet.stdSimplex.objEquiv.symm (SimplexCategory.σ i.succ))
    simp only [SSet.stdSimplex.δ_objEquiv_symm_apply,
      SimplexCategory.δ_comp_σ_succ, SimplexCategory.δ_comp_σ_self]
  · change (Δ[1] : SSet.{u}).δ i.castSucc.succ
        (SSet.stdSimplex.objMk₁ i.castSucc.succ.castSucc) =
      (Δ[1] : SSet.{u}).δ i.succ.castSucc
        (SSet.stdSimplex.objMk₁ i.succ.succ.castSucc)
    rw [SSet.stdSimplex.δ_objMk₁_of_le _ _ (by exact le_rfl),
      SSet.stdSimplex.δ_objMk₁_of_lt _ _ (by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        omega)]
    congr 1

/-- Adjacent realized prism cells agree on their shared codimension-one face. -/
theorem realizationPrismCell_adjacent_face {n : ℕ} (i : Fin n) :
    SSet.toTop.map (SSet.stdSimplex.δ i.castSucc.succ) ≫
        realizationPrismCell.{u} i.castSucc =
      SSet.toTop.map (SSet.stdSimplex.δ i.succ.castSucc) ≫
        realizationPrismCell.{u} i.succ := by
  unfold realizationPrismCell
  rw [← Functor.map_comp, ← Functor.map_comp,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    prism_adjacent_simplex_face]

end SSet

attribute [colib_tag "COL-0066",
  colib_ref "HatcherAT" "Section 2.1, proof of Theorem 2.10, prism subdivision, page 112"
    "background" "Prism background for the continuous comparison; no general invertibility claim"]
  SSet.realizationCylinderComparison
  SSet.realizationCylinderComparison_naturality

attribute [colib_tag "COL-0066",
  colib_ref "HatcherAT" "Section 2.1, proof of Theorem 2.10, prism subdivision, page 112"
    "adaptation" "Cover and adjacent shared faces of the actual realized standard prism cells"]
  SSet.realizationPrismCell_jointly_surjective
  SSet.realizationPrismCell_adjacent_face
