/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Waldhausen.QuillenComparison.RowEssentialSurjective

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.QuillenComparison
open scoped Simplicial
universe u v

noncomputable section
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactCategory.ExactStructure C)

example (n : SimplexCategory) :
    (rowChainEquivalence E n).functor = rowChainComparison E n := rfl

example (n : SimplexCategory) : (rowChainComparison E n).Full := inferInstance
example (n : SimplexCategory) : (rowChainComparison E n).Faithful := inferInstance
example (n : SimplexCategory) : (rowChainComparison E n).EssSurj := inferInstance
example (n : SimplexCategory) : (rowChainComparison E n).IsEquivalence := inferInstance

example (n : ℕ) (G : ComposableArrows (QConstruction E.deflation E.inflation) n) :
    ∃ F : Obj (ofExactCategory E) (SSet.EdgewiseSubdivision.ε.obj ⦋n⦌),
      Nonempty (((rowChainComparison E ⦋n⦌).obj ⟨F⟩).of ≅ G) :=
  exists_row_of_chain E n G

example (n : SimplexCategory)
    (F : WeakRows (ofExactCategory E) (SSet.EdgewiseSubdivision.ε.obj n))
    (i : Fin (n.len + 1)) :
    ((rowChainComparison E n).obj F).of.obj i =
      QConstruction.of E.deflation E.inflation
        (F.obj.obj.obj (interval (lowerIndex n i) (upperIndex n i)
          (lowerIndex_le_upperIndex n i i))) := rfl

example (n : SimplexCategory)
    (F : WeakRows (ofExactCategory E) (SSet.EdgewiseSubdivision.ε.obj n))
    {i j : Fin (n.len + 1)} (h : i ≤ j) :
    ((rowChainComparison E n).obj F).of.map (homOfLE h) =
      QConstruction.mkHom E.deflation E.inflation
        (intervalSpan E F.obj (show centralInterval n i ≤ centralInterval n j from
          ⟨lowerIndex_antitone n h, upperIndex_monotone n h⟩)) := rfl

example (n : SimplexCategory)
    {F G : WeakRows (ofExactCategory E) (SSet.EdgewiseSubdivision.ε.obj n)}
    (η : F ⟶ G) (i : Fin (n.len + 1)) :
    ((rowChainComparison E n).map η).iso.hom.app i =
      (E.qIsoOfIso ((weakRowIso E η).app
        (interval (lowerIndex n i) (upperIndex n i) (lowerIndex_le_upperIndex n i i)))).hom := rfl
