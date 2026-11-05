/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq

/-!
# Split biproduct conflations in an exact category

In every selected exact structure, both binary biproduct inclusions are admissible,
and the two standard split short complexes are conflations. The statements concern
the actual canonical inclusions and projections. No ambient abelian category or
closure under arbitrary kernels or cokernels is assumed.

## Implementation provenance

Extracted from the first five declarations of
`Aglib/CategoryTheory/ExactCategory/BaseChange.lean` at Aglib commit
`2c34f185fa859e862661f939cd216b07bcccfb26`. The original category universes,
selected exact structure and short-complex maps are retained. The two pushout
calculations directly reuse Mathlib's `IsPushout.of_has_biproduct`.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Any chosen cokernel of an admissible inclusion belongs to the exact
structure, by uniqueness of cokernels. -/
lemma conflation_of_inflation_of_isCokernel {S : ShortComplex C}
    (hf : E.inflation S.f) (hg : IsColimit (CokernelCofork.ofπ S.g S.zero)) :
    E.conflation S := by
  obtain ⟨Z, p, hp, hT⟩ := hf
  let hTg := E.cokernel (ShortComplex.mk S.f p hp) hT
  let e := hTg.coconePointUniqueUpToIso hg
  let eS : ShortComplex.mk S.f p hp ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by
      simpa using (hTg.comp_coconePointUniqueUpToIso_hom hg WalkingParallelPair.one).symm)
  exact E.iso_closed eS hT

/-- The biproduct inclusions are admissible in every exact structure. -/
lemma inflation_biprod_inl (X Y : C) : E.inflation (biprod.inl : X ⟶ X ⊞ Y) :=
  E.inflation.of_isPushout (IsPushout.of_has_biproduct X Y) (E.inflation_zero Y)

/-- The second biproduct inclusion is admissible as well. -/
lemma inflation_biprod_inr (X Y : C) : E.inflation (biprod.inr : Y ⟶ X ⊞ Y) :=
  E.inflation.of_isPushout (IsPushout.of_has_biproduct X Y).flip (E.inflation_zero X)

/-- The standard split short complex is a conflation in every exact category. -/
lemma conflation_biprod_inl_snd (X Y : C) :
    E.conflation (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) biprod.snd (by simp)) :=
  E.conflation_of_inflation_of_isCokernel (E.inflation_biprod_inl X Y)
    (biprod.isCokernelInlCokernelFork X Y)

/-- The reverse-order split short complex is also a conflation. -/
lemma conflation_biprod_inr_fst (X Y : C) :
    E.conflation (ShortComplex.mk (biprod.inr : Y ⟶ X ⊞ Y) biprod.fst (by simp)) :=
  E.conflation_of_inflation_of_isCokernel (E.inflation_biprod_inr X Y)
    (biprod.isCokernelInrCokernelFork X Y)

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0073",
  colib_ref "BuhlerExactCategories" "Lemma 2.7 and its proof" "adaptation"
    "Canonical biproduct inclusions and split conflations, also with the summands interchanged"]
  CategoryTheory.ExactCategory.ExactStructure.inflation_biprod_inl
  CategoryTheory.ExactCategory.ExactStructure.inflation_biprod_inr
  CategoryTheory.ExactCategory.ExactStructure.conflation_biprod_inl_snd
  CategoryTheory.ExactCategory.ExactStructure.conflation_biprod_inr_fst

attribute [colib_ref "BuhlerExactCategories" "Definition 2.1 and proof of Lemma 2.7"
    "ingredient" "Cokernel uniqueness and isomorphism closure for a specified admissible monic"]
  CategoryTheory.ExactCategory.ExactStructure.conflation_of_inflation_of_isCokernel
