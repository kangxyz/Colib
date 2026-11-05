/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.WeakNaturalTransformation
public import Colib.Topology.Realization.HomotopyBridge

/-! # The realization homotopy of the actual weak-row functors

This degreewise homotopy uses the actual weak-row natural transformation.
The diagonal S-map homotopy is separately constructed by the coherent grid cylinder;
degreewise homotopies alone are not asserted to supply diagonal coherence.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe v u
namespace CategoryTheory.Waldhausen.QuotientRows

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))

/-- Weak transformations induce a simplicial homotopy on each actual row nerve. -/
def weakRowNerveHomotopy (n : SimplexCategory) :
    SSet.Homotopy (nerveMap (weakRowsPostcompose V W hF n))
      (nerveMap (weakRowsPostcompose V W hG n)) :=
  naturalTransformationNerveHomotopy (weakRowsPostcomposeTransformation V W hF hG η hη n)

/-- The corresponding topological homotopy has the actual row functor endpoints. -/
def weakRowRealizationHomotopy (n : SimplexCategory) :
    (classifyingSpaceMap (weakRowsPostcompose V W hF n)).hom.Homotopy
      (classifyingSpaceMap (weakRowsPostcompose V W hG n)).hom :=
  classifyingSpaceNaturalTransformationHomotopy
    (weakRowsPostcomposeTransformation V W hF hG η hη n)

end CategoryTheory.Waldhausen.QuotientRows

attribute [colib_tag "COL-0156",
  colib_ref "Waldhausen1985" "Section 1.3, pp. 328-330" "background"
    "Background for the stated unnormalized IsZero model; not a strict-model identification"]
  CategoryTheory.Waldhausen.QuotientRows.weakRowRealizationHomotopy
