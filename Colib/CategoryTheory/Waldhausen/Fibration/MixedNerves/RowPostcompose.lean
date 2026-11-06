/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.MixedNerves.PostcomposeNerves
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.NestedWeakEquivalences

/-! # The original inner-row restriction acts on the mixed nerves

All three original predicates are preserved by the genuine quotient-row
restriction. Consequently the mixed diagrams form actual functors in the
inner row degree. The original inclusion is strictly natural before any
realization or choice of inverse.


Implementation provenance:
`Quillen/Waldhausen/Fibration/MixedNerves/RowPostcompose.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.MixedNerves

/-- Preservation proofs do not change equality of the original compatible functors. -/
@[ext] theorem CompatibleFunctor.ext {C D : Type u} [Category.{v} C] [Category.{v} D]
    {V : Structure C} {W : Structure D} {N : NestedWeakEquivalences V} {M :
      NestedWeakEquivalences W}
    {F G : CompatibleFunctor N M} (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- Genuine inner row reindexing preserves all three unchanged original predicates. -/
def rowReindexCompatible {m n : SimplexCategory} (α : m ⟶ n) :
    CompatibleFunctor (RowWeakEquivalences.nested N n) (RowWeakEquivalences.nested N m) where
  toFunctor := QuotientRows.reindex V α
  fine := (QuotientRows.reindex_exact V α).weak
  cof := (QuotientRows.reindex_exact V α).cofibration
  coarse := (RowWeakEquivalences.reindex_coarse_exact N α).weak

@[simp] theorem rowReindexCompatible_toFunctor {m n : SimplexCategory} (α : m ⟶ n) :
    (rowReindexCompatible N α).toFunctor = QuotientRows.reindex V α := rfl
@[simp] theorem rowReindexCompatible_id (n : SimplexCategory) :
    rowReindexCompatible N (𝟙 n) = CompatibleFunctor.id (RowWeakEquivalences.nested N n) := by
  apply CompatibleFunctor.ext
  exact QuotientRows.reindex_id V n
@[simp] theorem rowReindexCompatible_comp {l m n : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n) :
    rowReindexCompatible N (α ≫ β) = (rowReindexCompatible N β).comp (rowReindexCompatible N α)
      := by
  apply CompatibleFunctor.ext
  exact QuotientRows.reindex_comp V α β

/-- The original mixed coarse/fine nerves, now varying in the inner row degree. -/
def coarseRowNerves : SimplexCategoryᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{max u v}) where
  obj m := coarseChainNerve (RowWeakEquivalences.nested N m.unop)
  map α := coarseNerveMap (rowReindexCompatible N α.unop)
  map_id m := by
    change coarseNerveMap (rowReindexCompatible N (𝟙 m.unop)) = _
    rw [rowReindexCompatible_id, coarseNerveMap_id]
  map_comp α β := by
    change coarseNerveMap (rowReindexCompatible N (β.unop ≫ α.unop)) = _
    rw [rowReindexCompatible_comp, coarseNerveMap_comp]

/-- The same actual row diagram retains the genuine coarse-cofibration chains. -/
def cofRowNerves : SimplexCategoryᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{max u v}) where
  obj m := cofChainNerve (RowWeakEquivalences.nested N m.unop)
  map α := cofNerveMap (rowReindexCompatible N α.unop)
  map_id m := by
    change cofNerveMap (rowReindexCompatible N (𝟙 m.unop)) = _
    rw [rowReindexCompatible_id, cofNerveMap_id]
  map_comp α β := by
    change cofNerveMap (rowReindexCompatible N (β.unop ≫ α.unop)) = _
    rw [rowReindexCompatible_comp, cofNerveMap_comp]

/-- The original transposed mixed nerves, varying in the same inner row degree. -/
def horizontalRowNerves : SimplexCategoryᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{max u v}) where
  obj m := horizontalNerve (RowWeakEquivalences.nested N m.unop)
  map α := horizontalNerveMap (rowReindexCompatible N α.unop)
  map_id m := by
    change horizontalNerveMap (rowReindexCompatible N (𝟙 m.unop)) = _
    rw [rowReindexCompatible_id, horizontalNerveMap_id]
  map_comp α β := by
    change horizontalNerveMap (rowReindexCompatible N (β.unop ≫ α.unop)) = _
    rw [rowReindexCompatible_comp, horizontalNerveMap_comp]

/-- The corresponding original pointwise weak-cofibration nerve diagram. -/
def horizontalCofRowNerves : SimplexCategoryᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{max u v}) where
  obj m := horizontalCofNerve (RowWeakEquivalences.nested N m.unop)
  map α := horizontalCofNerveMap (rowReindexCompatible N α.unop)
  map_id m := by
    change horizontalCofNerveMap (rowReindexCompatible N (𝟙 m.unop)) = _
    rw [rowReindexCompatible_id, horizontalCofNerveMap_id]
  map_comp α β := by
    change horizontalCofNerveMap (rowReindexCompatible N (β.unop ≫ α.unop)) = _
    rw [rowReindexCompatible_comp, horizontalCofNerveMap_comp]

/-- The original mixed inclusion is strictly natural also in the inner row degree. -/
def rowChainInclusion : cofRowNerves N ⟶ coarseRowNerves N where
  app m := chainInclusion (RowWeakEquivalences.nested N m.unop)
  naturality _ _ α := (chainInclusion_naturality (rowReindexCompatible N α.unop)).symm

/-- The original transposed inclusion has the same third-index naturality. -/
def rowHorizontalInclusion : horizontalCofRowNerves N ⟶ horizontalRowNerves N where
  app m := horizontalNerveInclusion (RowWeakEquivalences.nested N m.unop)
  naturality _ _ α := (horizontalNerveInclusion_naturality (rowReindexCompatible N α.unop)).symm

/-- Actual diagonal mixed nerves in each original inner row degree. -/
def coarseRowDiagonals : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  coarseRowNerves N ⋙ SSet.diagonalFunctor
/-- Actual cofibration-diagonal mixed nerves in each original inner row degree. -/
def cofRowDiagonals : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  cofRowNerves N ⋙ SSet.diagonalFunctor
/-- The original diagonal inclusion, before realizing any of its three indices. -/
def rowDiagonalInclusion : cofRowDiagonals N ⟶ coarseRowDiagonals N :=
  Functor.whiskerRight (rowChainInclusion N) SSet.diagonalFunctor

@[simp] theorem rowDiagonalInclusion_app (m : SimplexCategory) :
    (rowDiagonalInclusion N).app (op m) =
      SSet.diagonalMap (chainInclusion (RowWeakEquivalences.nested N m)) := rfl

end CategoryTheory.Waldhausen.Fibration.MixedNerves
