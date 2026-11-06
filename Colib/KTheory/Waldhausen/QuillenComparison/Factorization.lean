/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.QuillenComparison.BisimplicialMap
public import Colib.Topology.Realization.EdgewiseSubdivisionBisimplicial

/-! # Exact-map factorization of the canonical Q/S comparison

The direct comparison is precisely the composition of the original-model
identification, upper-nerve restriction, rowwise Q comparison and native
chain-core diagonal evaluation. All model changes
apart from the still-separate rowwise equivalence are already genuine
realization homotopy equivalences.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/QuillenComparison/Factorization.lean at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual native weak rows,
   chain-core nerve and prescribed comparison map are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuillenComparison
open QuotientRows SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- The canonical model-identification and upper-index restriction. -/
def subdivisionToRows :
    EdgewiseSubdivision.subdivision (sSet E.inflation (MorphismProperty.isomorphisms C)) ⟶
    diagonalSSet (EdgewiseSubdivision.ε.op ⋙ weakRowNerve (ofExactCategory E)) :=
  EdgewiseSubdivision.subdivisionFunctor.map (sSetWeakRowDiagonalIso (ofExactCategory E)).hom ≫
    (EdgewiseSubdivision.doubleDiagonalIso (weakRowNerve (ofExactCategory E))).inv ≫
      diagonalMap (Functor.whiskerLeft
        (EdgewiseSubdivision.ε.op ⋙ weakRowNerve (ofExactCategory E))
        EdgewiseSubdivision.endpointNatTrans)

/-- The actual Q comparison in row-groupoid coordinates. -/
def rowsToQ : diagonalSSet (EdgewiseSubdivision.ε.op ⋙ weakRowNerve (ofExactCategory E)) ⟶
    nerve (QConstruction E.deflation E.inflation) :=
  diagonalMap (rowChainNerveMap E) ≫
    SSet.ChainCore.evaluation (QConstruction E.deflation E.inflation)

/-- This is an equality of the actual simplicial maps, not only a comparison
of abstract homotopy types. -/
theorem comparisonMap_factorization :
    subdivisionToRows E ≫ rowsToQ E = comparisonMap E := by
  ext n F
  rfl

/-- All model changes before the rowwise comparison already realize to an
actual homotopy equivalence. -/
def subdivisionToRowsHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      |EdgewiseSubdivision.subdivision (sSet E.inflation (MorphismProperty.isomorphisms C))|
      |diagonalSSet (EdgewiseSubdivision.ε.op ⋙ weakRowNerve (ofExactCategory E))| :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (EdgewiseSubdivision.subdivisionFunctor.mapIso
    (sSetWeakRowDiagonalIso (ofExactCategory E))))).toHomotopyEquiv.trans
    ((TopCat.homeoOfIso (SSet.toTop.mapIso
      (EdgewiseSubdivision.doubleDiagonalIso
        (weakRowNerve (ofExactCategory E))).symm)).toHomotopyEquiv.trans
      (EdgewiseSubdivision.upperIndexRealizationHomotopyEquiv (weakRowNerve (ofExactCategory E))))

@[simp]
theorem subdivisionToRowsHomotopyEquiv_toFun :
    (subdivisionToRowsHomotopyEquiv E).toFun = (SSet.toTop.map (subdivisionToRows E)).hom := by
  simp only [subdivisionToRowsHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans,
    EdgewiseSubdivision.upperIndexRealizationHomotopyEquiv_toFun, subdivisionToRows,
    Functor.map_comp]
  rfl

end CategoryTheory.Waldhausen.QuillenComparison
