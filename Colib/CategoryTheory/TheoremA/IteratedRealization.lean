/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.Coend
public import Colib.Topology.Realization.ProductSimplex

/-! Source: Quillen/CategoryTheory/TheoremA/IteratedRealization.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universal properties retained. -/

/-!
# Diagonal and iterated realization agree

The geometric realization of a simplicial topological space is defined by
the actual coend of its product with the standard topological simplices.
For a bisimplicial set, realizing the rows and then forming this coend is
canonically homeomorphic to realizing its diagonal. The proof transports
the checked simplicial co-Yoneda colimit along geometric realization and
the proved product-with-simplex homeomorphisms.
-/
@[expose] public section

noncomputable section

open SSet CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

/-- The usual product-with-simplex bifunctor defining geometric realization
of a simplicial topological space. -/
def iteratedRealizationBifunctor (Y : SimplexCategoryᵒᵖ ⥤ TopCat.{u}) :
    SimplexCategoryᵒᵖ ⥤ SimplexCategory ⥤ TopCat.{u} where
  obj p := SSet.stdSimplex ⋙ SSet.toTop ⋙ tensorLeft (Y.obj p)
  map α :=
    { app n := Y.map α ▷ |SSet.stdSimplex.obj n|
      naturality n m f := by simp [whisker_exchange] }
  map_id p := by ext n; simp
  map_comp α β := by ext n; simp

/-- The genuine topological coend realization of a simplicial space. -/
def iteratedRealization (Y : SimplexCategoryᵒᵖ ⥤ TopCat.{u}) : TopCat.{u} :=
  coend (iteratedRealizationBifunctor Y)

/-- A simplicial continuous map induces the canonical map of coend diagrams. -/
def iteratedRealizationBifunctorMap
    {Y Z : SimplexCategoryᵒᵖ ⥤ TopCat.{u}} (η : Y ⟶ Z) :
    iteratedRealizationBifunctor Y ⟶ iteratedRealizationBifunctor Z where
  app p :=
    { app n := η.app p ▷ |SSet.stdSimplex.obj n|
      naturality n m f := by
        dsimp [iteratedRealizationBifunctor]
        exact (whisker_exchange (η.app p) (SSet.toTop.map (SSet.stdSimplex.map f))).symm }
  naturality p q α := by
    apply NatTrans.ext
    funext n
    change (Y.map α ▷ |SSet.stdSimplex.obj n|) ≫ (η.app q ▷ |SSet.stdSimplex.obj n|) =
      (η.app p ▷ |SSet.stdSimplex.obj n|) ≫ (Z.map α ▷ |SSet.stdSimplex.obj n|)
    rw [← comp_whiskerRight, ← comp_whiskerRight, η.naturality]

/-- The canonical continuous map of realizations induced by a map of simplicial spaces. -/
def iteratedRealizationMap {Y Z : SimplexCategoryᵒᵖ ⥤ TopCat.{u}} (η : Y ⟶ Z) :
    iteratedRealization Y ⟶ iteratedRealization Z :=
  coend.map (iteratedRealizationBifunctorMap η)

variable (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})

/-- The defining coend diagrams are isomorphic by the canonical product comparisons. -/
def realizationCoendDiagramIso :
    (multispanIndexCoend (diagonalCoendBifunctor X)).multispan ⋙ SSet.toTop ≅
      (multispanIndexCoend (iteratedRealizationBifunctor (X ⋙ SSet.toTop))).multispan :=
  NatIso.ofComponents
    (fun j ↦ match j with
      | .left f => asIso (CartesianMonoidalCategory.prodComparison SSet.toTop
          (X.obj (op f.right)) (SSet.stdSimplex.obj f.left))
      | .right n => asIso (CartesianMonoidalCategory.prodComparison SSet.toTop
          (X.obj (op n)) (SSet.stdSimplex.obj n)))
    (by
      intro a b f
      cases f with
      | id a => simp
      | fst f =>
        change SSet.toTop.map (X.map f.hom.op ▷ SSet.stdSimplex.obj f.left) ≫
          CartesianMonoidalCategory.prodComparison SSet.toTop (X.obj (op f.left))
            (SSet.stdSimplex.obj f.left) =
          CartesianMonoidalCategory.prodComparison SSet.toTop (X.obj (op f.right))
            (SSet.stdSimplex.obj f.left) ≫
            (SSet.toTop.map (X.map f.hom.op) ▷ |SSet.stdSimplex.obj f.left|)
        exact prodComparison_natural_whiskerRight SSet.toTop (X.map f.hom.op)
      | snd f =>
        change SSet.toTop.map (X.obj (op f.right) ◁ SSet.stdSimplex.map f.hom) ≫
          CartesianMonoidalCategory.prodComparison SSet.toTop (X.obj (op f.right))
            (SSet.stdSimplex.obj f.right) =
          CartesianMonoidalCategory.prodComparison SSet.toTop (X.obj (op f.right))
            (SSet.stdSimplex.obj f.left) ≫
            (|X.obj (op f.right)| ◁ SSet.toTop.map (SSet.stdSimplex.map f.hom))
        exact prodComparison_natural_whiskerLeft SSet.toTop (SSet.stdSimplex.map f.hom))

/-- Realization of the diagonal is canonically isomorphic to the iterated
realization. This is an actual topological isomorphism, not only a weak equivalence. -/
def diagonalIteratedRealizationIso :
    |diagonalSSet X| ≅ iteratedRealization (X ⋙ SSet.toTop) :=
  IsColimit.coconePointsIsoOfNatIso
    (isColimitOfPreserves SSet.toTop (diagonalCowedgeIsColimit X))
    (colimit.isColimit _)
    (realizationCoendDiagramIso X)

/-- The comparison isomorphism respects the canonical simplex inclusions. -/
@[reassoc]
theorem diagonalIteratedRealizationIso_ι (n : SimplexCategory) :
    SSet.toTop.map (diagonalEvaluation X n) ≫ (diagonalIteratedRealizationIso X).hom =
      CartesianMonoidalCategory.prodComparison SSet.toTop (X.obj (op n)) (SSet.stdSimplex.obj n) ≫
        coend.ι (iteratedRealizationBifunctor (X ⋙ SSet.toTop)) n :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom
    (isColimitOfPreserves SSet.toTop (diagonalCowedgeIsColimit X))
    (colimit.isColimit _)
    (realizationCoendDiagramIso X) (.right n)

/-- Realized row evaluations jointly determine a continuous map out of the diagonal. -/
theorem realizedDiagonal_hom_ext {Z : TopCat.{u}} {f g : |diagonalSSet X| ⟶ Z}
    (h : ∀ n : SimplexCategory,
      SSet.toTop.map (diagonalEvaluation X n) ≫ f =
        SSet.toTop.map (diagonalEvaluation X n) ≫ g) : f = g := by
  apply (isColimitOfPreserves SSet.toTop (diagonalCowedgeIsColimit X)).hom_ext
  intro j
  cases j with
  | right n => exact h n
  | left a =>
    change SSet.toTop.map ((X.map a.hom.op ▷ SSet.stdSimplex.obj a.left) ≫
      diagonalEvaluation X a.left) ≫ f =
        SSet.toTop.map ((X.map a.hom.op ▷ SSet.stdSimplex.obj a.left) ≫
          diagonalEvaluation X a.left) ≫ g
    rw [Functor.map_comp, Category.assoc, Category.assoc, h]

/-- The diagonal/iterated comparison preserves the actual map induced by a
map of bisimplicial sets. -/
theorem diagonalIteratedRealizationIso_naturality
    {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) :
    SSet.toTop.map (diagonalMap η) ≫ (diagonalIteratedRealizationIso Y).hom =
      (diagonalIteratedRealizationIso X).hom ≫
        iteratedRealizationMap (Functor.whiskerRight η SSet.toTop) := by
  apply realizedDiagonal_hom_ext X
  intro n
  calc
    SSet.toTop.map (diagonalEvaluation X n) ≫
        (SSet.toTop.map (diagonalMap η) ≫ (diagonalIteratedRealizationIso Y).hom) =
      SSet.toTop.map (η.app (op n) ▷ SSet.stdSimplex.obj n) ≫
        (SSet.toTop.map (diagonalEvaluation Y n) ≫ (diagonalIteratedRealizationIso Y).hom) := by
          rw [← Functor.map_comp_assoc, ← diagonalEvaluation_naturality, Functor.map_comp_assoc]
    _ = SSet.toTop.map (η.app (op n) ▷ SSet.stdSimplex.obj n) ≫
        CartesianMonoidalCategory.prodComparison SSet.toTop (Y.obj (op n)) (SSet.stdSimplex.obj n) ≫
          coend.ι (iteratedRealizationBifunctor (Y ⋙ SSet.toTop)) n := by
      rw [diagonalIteratedRealizationIso_ι]
    _ = CartesianMonoidalCategory.prodComparison SSet.toTop (X.obj (op n)) (SSet.stdSimplex.obj n) ≫
        (SSet.toTop.map (η.app (op n)) ▷ |SSet.stdSimplex.obj n|) ≫
          coend.ι (iteratedRealizationBifunctor (Y ⋙ SSet.toTop)) n := by
      rw [← Category.assoc, prodComparison_natural_whiskerRight, Category.assoc]
    _ = CartesianMonoidalCategory.prodComparison SSet.toTop (X.obj (op n)) (SSet.stdSimplex.obj n) ≫
        coend.ι (iteratedRealizationBifunctor (X ⋙ SSet.toTop)) n ≫
          iteratedRealizationMap (Functor.whiskerRight η SSet.toTop) := by
      rw [iteratedRealizationMap, coend.ι_map]
      rfl
    _ = SSet.toTop.map (diagonalEvaluation X n) ≫
        ((diagonalIteratedRealizationIso X).hom ≫
          iteratedRealizationMap (Functor.whiskerRight η SSet.toTop)) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ iteratedRealizationMap (Functor.whiskerRight η SSet.toTop))
        (diagonalIteratedRealizationIso_ι X n).symm

end CategoryTheory.TheoremA
