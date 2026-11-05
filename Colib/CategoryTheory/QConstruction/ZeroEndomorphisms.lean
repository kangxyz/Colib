/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.QConstruction.Connected

/-! # Endomorphisms of the distinguished zero vertex

The distinguished Q-object has only its identity endomorphism. This is much
weaker than being initial, terminal, or a zero object in Q, none of which is
asserted here. The proof uses that a span apex admitting a monomorphism to the
original zero object must itself be zero.

## Implementation provenance

Adapted from `Quillen/CategoryTheory/QConstruction/ZeroEndomorphisms.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original selected exact structure,
object and morphism universes, distinguished vertex and actual span maps are retained.

-/
@[expose] public noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- Every endomorphism of the distinguished zero Q-vertex is the identity. -/
theorem qZero_endomorphism_eq_id (f : E.qZero ⟶ E.qZero) : f = 𝟙 E.qZero := by
  refine Quotient.inductionOn f (fun s => ?_)
  have : Mono s.r := E.mono_of_inflation s.wr
  have hz : IsZero s.apex := IsZero.of_mono s.r (isZero_zero C)
  exact CategoryTheory.QConstruction.mkHom_eq_of_apexIso E.deflation E.inflation s (Span.id (0 : C))
    (hz.iso (isZero_zero C)) ((isZero_zero C).eq_of_tgt _ _) ((isZero_zero C).eq_of_tgt _ _)

instance qZero_endomorphisms_subsingleton : Subsingleton (E.qZero ⟶ E.qZero) where
  allEq f g := (E.qZero_endomorphism_eq_id f).trans (E.qZero_endomorphism_eq_id g).symm

/-- In particular, a comparison isomorphism at the zero vertex is unique. -/
instance qZero_automorphisms_subsingleton : Subsingleton (E.qZero ≅ E.qZero) where
  allEq _ _ := Iso.ext (Subsingleton.elim _ _)

/-- Every Q-hom set with an original zero object as target is a subsingleton.
Existence is not asserted for arbitrary source objects. -/
theorem qHom_subsingleton_of_isZero (X Y : E.QCategory) (hY : IsZero Y.obj.of) :
    Subsingleton (X ⟶ Y) where
  allEq f g := by
    refine Quotient.inductionOn₂ f g (fun s t => ?_)
    have hs : Mono s.r := E.mono_of_inflation s.wr
    have ht : Mono t.r := E.mono_of_inflation t.wr
    have hS : IsZero s.apex := IsZero.of_mono s.r hY
    have hT : IsZero t.apex := IsZero.of_mono t.r hY
    exact CategoryTheory.QConstruction.mkHom_eq_of_apexIso E.deflation E.inflation s t
      (hS.iso hT) (hS.eq_of_src _ _) (hS.eq_of_src _ _)

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0040",
  colib_ref "WeibelKBook" "IV, Definition 6.1 and Subobjects 6.1.2" "adaptation"
    "Derived uniqueness for zero-target spans; existence for arbitrary sources is not asserted"]
  CategoryTheory.ExactCategory.ExactStructure.qHom_subsingleton_of_isZero
  CategoryTheory.ExactCategory.ExactStructure.qZero_endomorphism_eq_id
