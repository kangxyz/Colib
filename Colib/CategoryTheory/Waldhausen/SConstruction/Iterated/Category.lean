/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Functoriality
public import Colib.CategoryTheory.Waldhausen.AsSmall.Basic
public import Colib.CategoryTheory.Waldhausen.SmallCategory
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# The exact category of models for iterated S-constructions

The objects are actual small Waldhausen categories. Morphisms are exact functors together
with equality of the chosen zero objects. Actual quotient rows, ordinal reindexing, and the
original diagonal S-construction produce all finite stages by recursive prolongation.
The genuine small-model construction handles independent original object and morphism universes.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/Category.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, assumptions,
chosen zero objects and universe parameters are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite MonoidalCategory SSet
open scoped Simplicial
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory

/-- Actual quotient rows are functorial on the genuine zero-preserving exact category. -/
def rows (n : SimplexCategory) :
    WideSubcategory preservesZero.{u} ⥤ WideSubcategory preservesZero.{u} where
  obj W := ⟨{
    Obj := QuotientRows.Obj W.obj.waldhausen n
    waldhausen := QuotientRows.waldhausenStructure W.obj.waldhausen n }⟩
  map F := ⟨⟨QuotientRows.postcompose _ _ F.hom.isExact n,
    QuotientRows.postcompose_exact _ _ F.hom.isExact n⟩,
    postcompose_zero _ _ F.hom.isExact F.property n⟩
  map_id W := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact QuotientRows.postcompose_id _ n
  map_comp F G := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact (QuotientRows.postcompose_comp_postcompose _ _ F.hom.isExact _ G.hom.isExact n).symm

/-- The original ordinal restrictions, with their proved exactness and original zero equality. -/
def rowsReindex {m n : SimplexCategory} (α : m ⟶ n) : rows n ⟶ rows m where
  app W := ⟨⟨QuotientRows.reindex W.obj.waldhausen α,
    QuotientRows.reindex_exact W.obj.waldhausen α⟩,
    QuotientRows.reindex_zero W.obj.waldhausen α⟩
  naturality V W F := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact QuotientRows.postcompose_reindex V.obj.waldhausen W.obj.waldhausen F.hom.isExact α

/-- All actual row categories and exact ordinal maps form one simplicial diagram. -/
def rowDiagram (W : WideSubcategory preservesZero.{u}) :
    SimplexCategoryᵒᵖ ⥤ WideSubcategory preservesZero.{u} where
  obj n := (rows n.unop).obj W
  map α := (rowsReindex α.unop).app W
  map_id n := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact QuotientRows.reindex_id _ _
  map_comp α β := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact QuotientRows.reindex_comp _ _ _

/-- Exact zero-preserving functors act on every original row simultaneously. -/
def rowDiagramFunctor :
    WideSubcategory preservesZero.{u} ⥤
      (SimplexCategoryᵒᵖ ⥤ WideSubcategory preservesZero.{u}) where
  obj := rowDiagram
  map F := {
    app n := (rows n.unop).map F
    naturality n m α := ((rowsReindex α.unop).naturality F).symm }
  map_id W := by ext n : 1; exact (rows n.unop).map_id W
  map_comp F G := by ext n : 1; exact (rows n.unop).map_comp F G

/-- The original diagonal S-construction, retaining its exact original maps. -/
def initialS : WideSubcategory preservesZero.{u} ⥤ SSet.{u} where
  obj W := sSet W.obj.waldhausen.cof W.obj.waldhausen.weq
  map F := sSetMap F.hom.isExact
  map_id W := by ext n A; rfl
  map_comp F G := by ext n A; rfl

/-- Iterate a genuine simplicial invariant by the actual quotient-row construction. -/
def prolong (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u}) :
    WideSubcategory preservesZero.{u} ⥤ SSet.{u} :=
  rowDiagramFunctor ⋙ (whiskeringRight _ _ _).obj H ⋙ SSet.diagonalFunctor

/-- Every finite iterated S-stage is constructed by actual rows, nerves and diagonals. -/
def stages (r : ℕ) : WideSubcategory preservesZero.{u} ⥤ SSet.{u} :=
  Nat.rec initialS (fun _ H ↦ prolong H) r

/-- The original one-row insertion, as an actual natural transformation. -/
def insertion {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    𝟭 (WideSubcategory preservesZero.{u}) ⟶ rows n where
  app W := ⟨⟨suspensionRow W.obj.waldhausen τ, suspensionRow_exact W.obj.waldhausen τ⟩,
    suspensionRow_zero_obj W.obj.waldhausen τ⟩
  naturality V W F := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact (suspensionRow_postcompose V.obj.waldhausen W.obj.waldhausen
      F.hom.isExact F.property τ).symm

lemma insertion_reindex {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌)
    (W : WideSubcategory preservesZero.{u}) :
    (insertion (α ≫ τ)).app W = (insertion τ).app W ≫ (rowsReindex α).app W := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  exact suspensionRow_reindex W.obj.waldhausen α τ

/-- This bundle retains the actual accepted small-model equivalence for arbitrary original
universes. -/
def asSmallCategory {C : Type*} [Category C] (W : Structure C) :
    WideSubcategory preservesZero :=
  ⟨{ Obj := AsSmall.{0} C, waldhausen := W.asSmall }⟩

end CategoryTheory.Waldhausen.IteratedS
