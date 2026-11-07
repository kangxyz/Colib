/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.QuillenComparison.Indices

/-! # The canonical simplicial Q/S comparison map

The edgewise subdivision of the genuine diagonal S-construction maps to the
nerve of the existing Q-category. The i-th vertex is the quotient indexed by
[n-i,n+1+i] in nerve row n+1+i. All simplicial identities follow from the
strict reindexing theorem and the genuine reversed-first-half edgewise indices.
The map uses the existing `sSetWeakRowDiagonalIso` and original `WeakRows`.

Adapted from `Quillen/Waldhausen/QuillenComparison/SimplicialMap.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, without introducing the source Row model.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial CategoryTheory.Prod
universe v u

namespace CategoryTheory.Waldhausen.QuillenComparison
open QuotientRows SSet

@[simp]
theorem centralInterval_naturality {n m : SimplexCategory} (α : n ⟶ m)
    (i : Fin (n.len + 1)) :
    (nestedIntervalMap (EdgewiseSubdivision.ε.map α)).obj (centralInterval n i) =
      centralInterval m (α.toOrderHom i) := by
  apply Subtype.ext
  apply Prod.ext
  · exact lowerIndex_naturality α i
  · exact upperIndex_naturality α i

/-- Naturality of the central interval and nerve indices together. -/
theorem comparisonIndices_naturality {n m : SimplexCategory} (α : n ⟶ m) :
    comparisonIndices n ⋙
      ((SimplexCategory.toCat.map (EdgewiseSubdivision.ε.map α)).toFunctor.prod
        (nestedIntervalMap (EdgewiseSubdivision.ε.map α))) =
      (SimplexCategory.toCat.map α).toFunctor ⋙ comparisonIndices m := by
  apply CategoryTheory.Functor.ext
    (fun i ↦ Prod.ext (upperIndex_naturality α i) (centralInterval_naturality α i))

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- The original S-simplex, presented by its existing weak-row nerve, yields a Q-grid. -/
def gridQFunctor {n : SimplexCategory}
    (F : (sSet E.inflation (MorphismProperty.isomorphisms C)).obj (op n)) :
    Fin (n.len + 1) × NestedInterval n ⥤ QConstruction E.deflation E.inflation :=
  weakChainQFunctor E ((sSetWeakRowDiagonalIso (ofExactCategory E)).hom.app (op n) F)

/-- Original simultaneous ordinal restriction commutes with the actual Q-grid. -/
theorem gridQFunctor_precomp {m n : SimplexCategory} (α : m ⟶ n)
    (F : (sSet E.inflation (MorphismProperty.isomorphisms C)).obj (op n)) :
    gridQFunctor E ((sSet E.inflation (MorphismProperty.isomorphisms C)).map α.op F) =
      ((SimplexCategory.toCat.map α).toFunctor.prod (nestedIntervalMap α)) ⋙
        gridQFunctor E F := by
  change weakChainQFunctor E (gridToWeakChain (ofExactCategory E)
    (gridMap₂ α α ⋙ F.val)
    (((isSimplex₂_diagonal_iff E.inflation (MorphismProperty.isomorphisms C) F.val).2
      F.property).precomp E.inflation (MorphismProperty.isomorphisms C) α α)) = _
  rw [gridToWeakChain_reindex (ofExactCategory E) α α F.val
    ((isSimplex₂_diagonal_iff E.inflation (MorphismProperty.isomorphisms C) F.val).2
      F.property), weakChainQFunctor_reindex]
  rfl

/-- An edgewise S-simplex gives an actual chain of Q-arrows. -/
def comparisonSimplex {n : SimplexCategory}
    (F : (sSet E.inflation (MorphismProperty.isomorphisms C)).obj
      (op (EdgewiseSubdivision.ε.obj n))) :
    (nerve (QConstruction E.deflation E.inflation)).obj (op n) :=
  comparisonIndices n ⋙ gridQFunctor E F

/-- The i-th comparison vertex is the original central quotient in nerve row n+1+i. -/
@[simp] theorem comparisonSimplex_obj {n : SimplexCategory}
    (F : (sSet E.inflation (MorphismProperty.isomorphisms C)).obj
      (op (EdgewiseSubdivision.ε.obj n))) (i : Fin (n.len + 1)) :
    (comparisonSimplex E F).obj i =
      QConstruction.of E.deflation E.inflation
        (F.val.obj (grid (upperIndex n i) (lowerIndex n i) (upperIndex n i)
          (lowerIndex_le_upperIndex n i i))) := rfl

/-- The comparison chain commutes with every face and degeneracy. -/
theorem comparisonSimplex_naturality {n m : SimplexCategory} (α : n ⟶ m)
    (F : (sSet E.inflation (MorphismProperty.isomorphisms C)).obj
      (op (EdgewiseSubdivision.ε.obj m))) :
    comparisonSimplex E ((sSet E.inflation (MorphismProperty.isomorphisms C)).map
      (EdgewiseSubdivision.ε.map α).op F) =
      (nerve (QConstruction E.deflation E.inflation)).map α.op (comparisonSimplex E F) := by
  change comparisonIndices n ⋙ gridQFunctor E
      ((sSet E.inflation (MorphismProperty.isomorphisms C)).map
        (EdgewiseSubdivision.ε.map α).op F) =
    (SimplexCategory.toCat.map α).toFunctor ⋙ comparisonIndices m ⋙ gridQFunctor E F
  rw [gridQFunctor_precomp, ← Functor.assoc, comparisonIndices_naturality, Functor.assoc]

/-- The canonical simplicial comparison from the edgewise S-model to Q. -/
def comparisonMap :
    EdgewiseSubdivision.subdivision (sSet E.inflation (MorphismProperty.isomorphisms C)) ⟶
      nerve (QConstruction E.deflation E.inflation) where
  app n := ↾fun F ↦ comparisonSimplex E F
  naturality n m α := by
    ext F
    exact comparisonSimplex_naturality E α.unop F

end CategoryTheory.Waldhausen.QuillenComparison

attribute [colib_tag "COL-0243",
  colib_ref "quillen" "Quillen/Waldhausen/QuillenComparison/SimplicialMap.lean"
    "adaptation" "Canonical reversed-edgewise comparison using the existing native weak rows"]
  CategoryTheory.Waldhausen.QuillenComparison.comparisonMap
  CategoryTheory.Waldhausen.QuillenComparison.comparisonSimplex_obj
  CategoryTheory.Waldhausen.QuillenComparison.comparisonSimplex_naturality
