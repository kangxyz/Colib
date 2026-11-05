/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.QIsomorphisms
public import Colib.CategoryTheory.ExactCategory.Functor.QConstruction

/-!
# Exact functors preserve the specified Q-isomorphisms

Extracted from `mapQ_qIsoOfIso` in `Quillen/KTheory/Map/CoherenceData.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The categorical
argument works with independent source and target universes; the original
shared-universe statement is its specialization.
All constructions retain the actual objects, span legs and canonical maps.
No balancedness, ambient abelian structure or arbitrary pullback hypothesis is added.
This module makes no assertion about classifying spaces or homotopy K-groups.
-/

@[expose] public noncomputable section

universe v v' u u'

open CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- An exact functor's Q-functor takes the Q-isomorphism of an original
isomorphism to the Q-isomorphism of its image. -/
@[simp]
theorem mapQ_qIsoOfIso (F : ExactFunctor EC ED)
    {X Y : C} (e : X ≅ Y) :
    F.mapQ.mapIso (EC.qIsoOfIso e) = ED.qIsoOfIso (F.toFunctor.mapIso e) := by
  apply Iso.ext
  apply Quotient.sound
  refine ⟨Span.mkIso (Iso.refl _) ?_ ?_⟩
  · change 𝟙 (F.toFunctor.obj X) ≫ 𝟙 (F.toFunctor.obj X) = F.toFunctor.map (𝟙 X)
    simp
  · change 𝟙 (F.toFunctor.obj X) ≫ F.toFunctor.map e.hom = F.toFunctor.map e.hom
    simp


end CategoryTheory.ExactCategory.ExactFunctor

attribute [colib_tag "COL-0050",
  colib_ref "WeibelKBook" "IV, Subobjects 6.1.2 and paragraph following Definition 6.3" "adaptation"
    "Compatibility of the actual induced Q-functor with the specified Q-isomorphism map"]
  CategoryTheory.ExactCategory.ExactFunctor.mapQ_qIsoOfIso
