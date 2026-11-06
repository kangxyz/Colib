/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Functor.QConstruction

/-!
# Fully faithful exact functors induce faithful Q-functors

This is the common restricted-span lifting argument used by exact equivalences
and dévissage. It needs no essential surjectivity or topological constructions.

Implementation provenance: extracted without changing its statement or proof
from `Colib/KTheory/Quillen/Equivalence.lean` at Colib
`439de508c89c315ff8c7ec4d787d032797cef84b`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- An ordinary fully faithful exact functor induces a faithful Q-functor. -/
theorem mapQ_faithful_of_fullyFaithful [F.toFunctor.Full] [F.toFunctor.Faithful] :
    F.mapQ.Faithful where
  map_injective := by
    rintro X Y ⟨s⟩ ⟨t⟩ h
    change QConstruction.mkHom _ _ (F.toQCompatibleFunctor.mapSpan s) =
      QConstruction.mkHom _ _ (F.toQCompatibleFunctor.mapSpan t) at h
    obtain ⟨e, hl, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ _ _).1 h
    apply QConstruction.mkHom_eq_of_apexIso _ _ s t (F.toFunctor.preimageIso e)
    · apply F.toFunctor.map_injective
      simpa only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage] using
        (show e.hom ≫ F.toFunctor.map t.l = F.toFunctor.map s.l from hl)
    · apply F.toFunctor.map_injective
      simpa only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage] using
        (show e.hom ≫ F.toFunctor.map t.r = F.toFunctor.map s.r from hr)

end CategoryTheory.ExactCategory.ExactFunctor
