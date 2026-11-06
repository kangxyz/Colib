/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.QuillenComparison.SimplicialMap
public import Colib.CategoryTheory.Waldhausen.Rows.NerveFunctoriality
public import Colib.CategoryTheory.ExactCategory.Functor.Waldhausen
public import Colib.CategoryTheory.ExactCategory.Functor.QIsomorphisms

/-! # Exact-functor naturality of the actual simplicial Q/S comparison

The maps are the existing `sSetMap` and `ExactFunctor.mapQ`. Preservation of
admissible pushouts is proved from additive exactness, not an extra hypothesis.
No separate exact-category S-map or row model is introduced.

Adapted from `Quillen/Waldhausen/QuillenComparison/Functoriality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, directly on the native weak rows.
This is simplicial naturality, not the later identity between canonical K-maps.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial CategoryTheory.Prod
universe v u
namespace CategoryTheory.Waldhausen.QuotientRows

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactCategory.ExactStructure C} {ED : ExactCategory.ExactStructure D}
  (F : ExactCategory.ExactFunctor EC ED)

/-- Exact functors retain the actual component isomorphisms of original weak row maps. -/
theorem weakRowIso_app_postcompose {n : SimplexCategory}
    {A B : WeakRows (ofExactCategory EC) n} (η : A ⟶ B) (p : Interval n) :
    (weakRowIso ED
      ((weakRowsPostcompose (ofExactCategory EC) (ofExactCategory ED) F.waldhausenExact n).map
        η)).app p = F.toFunctor.mapIso ((weakRowIso EC η).app p) := by
  apply Iso.ext
  rfl

/-- The canonical subquotient span is sent termwise to the existing Q-map's span. -/
theorem intervalSpan_postcompose {n : SimplexCategory}
    (A : Obj (ofExactCategory EC) n) {p q : NestedInterval n} (h : p ≤ q) :
    intervalSpan ED
      ((postcompose (ofExactCategory EC) (ofExactCategory ED) F.waldhausenExact n).obj A) h =
      F.toQCompatibleFunctor.mapSpan (intervalSpan EC A h) := rfl

/-- Both directions of the original weak-row grid are natural for the genuine exact functor. -/
theorem weakChainQFunctor_postcompose {n k : SimplexCategory}
    (A : ComposableArrows (WeakRows (ofExactCategory EC) n) k.len) :
    weakChainQFunctor ED
      (A ⋙ weakRowsPostcompose (ofExactCategory EC) (ofExactCategory ED) F.waldhausenExact n) =
      weakChainQFunctor EC A ⋙ F.mapQ := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro p q f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (ED.qIsoOfIso ((weakRowIso ED
    ((weakRowsPostcompose (ofExactCategory EC) (ofExactCategory ED) F.waldhausenExact n).map
      (A.map f.1))).app _)).hom ≫
    QConstruction.mkHom _ _ (intervalSpan ED
      ((postcompose (ofExactCategory EC) (ofExactCategory ED) F.waldhausenExact n).obj
        (A.obj q.1).obj) _) =
    F.mapQ.map ((EC.qIsoOfIso ((weakRowIso EC (A.map f.1)).app _)).hom ≫
      QConstruction.mkHom _ _ (intervalSpan EC (A.obj q.1).obj _))
  rw [Functor.map_comp, weakRowIso_app_postcompose, intervalSpan_postcompose]
  congr 1
  exact congrArg Iso.hom (F.mapQ_qIsoOfIso _).symm

end CategoryTheory.Waldhausen.QuotientRows

namespace CategoryTheory.Waldhausen.QuillenComparison
open QuotientRows
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactCategory.ExactStructure C} {ED : ExactCategory.ExactStructure D}
  (F : ExactCategory.ExactFunctor EC ED)

/-- The actual Q-valued grid is natural for the original S-construction map. -/
theorem gridQFunctor_postcompose {n : SimplexCategory}
    (A : (sSet EC.inflation (MorphismProperty.isomorphisms C)).obj (op n)) :
    gridQFunctor ED ((sSetMap F.waldhausenExact).app (op n) A) =
      gridQFunctor EC A ⋙ F.mapQ := by
  change weakChainQFunctor ED (gridToWeakChain (ofExactCategory ED) (A.val ⋙ F.toFunctor)
    (((isSimplex₂_diagonal_iff EC.inflation (MorphismProperty.isomorphisms C) A.val).2
      A.property).postcomp EC.inflation (MorphismProperty.isomorphisms C) F.waldhausenExact)) = _
  rw [gridToWeakChain_postcompose (ofExactCategory EC) (ofExactCategory ED) F.waldhausenExact
    A.val ((isSimplex₂_diagonal_iff EC.inflation (MorphismProperty.isomorphisms C) A.val).2
      A.property), weakChainQFunctor_postcompose]
  rfl

/-- The prescribed simplicial Q/S map commutes with both original exact-functor maps. -/
theorem comparisonMap_naturality :
    SSet.EdgewiseSubdivision.subdivisionFunctor.map (sSetMap F.waldhausenExact) ≫
        comparisonMap ED = comparisonMap EC ≫ nerveMap F.mapQ := by
  ext n A
  change comparisonIndices n.unop ⋙
      gridQFunctor ED ((sSetMap F.waldhausenExact).app _ A) =
    (comparisonIndices n.unop ⋙ gridQFunctor EC A) ⋙ F.mapQ
  rw [gridQFunctor_postcompose, Functor.assoc]

end CategoryTheory.Waldhausen.QuillenComparison

attribute [colib_tag "COL-0243",
  colib_ref "quillen" "Quillen/Waldhausen/QuillenComparison/Functoriality.lean"
    "adaptation" "Simplicial naturality with the original sSetMap and exact-functor mapQ"]
  CategoryTheory.Waldhausen.QuillenComparison.comparisonMap_naturality
