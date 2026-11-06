/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.KTheory.Quillen.Localization.Serre.Basic
public import Colib.KTheory.Quillen.Devissage.Basic
public import Colib.KTheory.GrothendieckComparison.Naturality
public import Colib.KTheory.GrothendieckComparison.Injectivity

/-!
# Right exactness of actual homotopical K-zero under Serre localization

The original exact-functor K-maps intertwine the proved Grothendieck–Quillen
comparison. Thus Stacks 02MX gives exactness at K₀(C) and the actual surjection
onto K₀(C/P), not merely a statement about a replacement algebraic model.

These are the final two assertions of
`Quillen/Localization/Serre/LocalizationTheorem.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, with their original maps. The proof
uses the independent K-zero comparison. It does not establish a higher-K
fiber equivalence, the K₁ boundary, or the other exactness positions.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Abelian C] [Abelian D] (P : ObjectProperty C) [P.IsSerreClass]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]

/-- The original exact inclusion has precisely the object-generated Serre image. -/
lemma inclusionGrothendieckMap_range :
    (Abelian.Devissage.grothendieckMap P).range = serreSubgroup P := by
  apply AddSubgroup.map_injective (f := (abelianGrothendieckEquiv C).toAddMonoidHom)
    (abelianGrothendieckEquiv C).injective
  rw [map_serreSubgroup_eq_range_of_isSerreClass, ← AddMonoidHom.range_comp]
  change ((abelianGrothendieckEquiv C).toAddMonoidHom.comp
    (P.exactInclusion).grothendieckMap).range = _
  rw [(P.exactInclusion).abelianGrothendieckEquiv_naturality,
    AddMonoidHom.range_comp]
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (abelianGrothendieckEquiv P.FullSubcategory).surjective y, rfl⟩

/-- Naturality retains the original quotient K-map and original comparison maps. -/
theorem KZeroMap_grothendieckToKZero :
    (KMap P L 0).comp (abelianExactStructure C).grothendieckToKZero =
      (abelianExactStructure D).grothendieckToKZero.comp
        (grothendieckMap P L).toMultiplicative :=
  (ExactFunctor.serreLocalization P L).grothendieckToKZero_naturality

/-- The actual localization homomorphism is surjective in homotopical K-zero. -/
theorem KZeroMap_surjective : Function.Surjective (KMap P L 0) := by
  intro y
  obtain ⟨a, rfl⟩ := (abelianExactStructure D).grothendieckToKZero_surjective y
  obtain ⟨b, hb⟩ := grothendieckMap_surjective P L a.toAdd
  refine ⟨(abelianExactStructure C).grothendieckToKZero (Multiplicative.ofAdd b), ?_⟩
  have h := DFunLike.congr_fun (KZeroMap_grothendieckToKZero P L) (Multiplicative.ofAdd b)
  exact h.trans (congrArg (abelianExactStructure D).grothendieckToKZero
    (congrArg Multiplicative.ofAdd hb))

/-- Inclusion and localization are right exact on the original homotopical K-zero. -/
theorem inclusionKZero_range_eq_ker :
    (Abelian.Devissage.KMap P 0).range = (KMap P L 0).ker := by
  ext a
  obtain ⟨x, rfl⟩ := (abelianExactStructure C).grothendieckToKZero_surjective a
  have hι := (P.exactInclusion).grothendieckToKZero_naturality
  have hL := KZeroMap_grothendieckToKZero P L
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨y, rfl⟩ :=
      (abelianExactStructure P.FullSubcategory).grothendieckToKZero_surjective b
    have hy : (Abelian.Devissage.grothendieckMap P) y.toAdd = x.toAdd := by
      apply Multiplicative.ofAdd.injective
      apply (abelianExactStructure C).grothendieckToKZero_injective
      exact (DFunLike.congr_fun hι y).symm.trans hb
    have hx : x.toAdd ∈ (grothendieckMap P L).ker := by
      rw [grothendieckMap_ker, ← inclusionGrothendieckMap_range]
      exact ⟨y.toAdd, hy⟩
    change KMap P L 0 ((abelianExactStructure C).grothendieckToKZero x) = 1
    have hLx := DFunLike.congr_fun hL x
    change KMap P L 0 ((abelianExactStructure C).grothendieckToKZero x) =
      (abelianExactStructure D).grothendieckToKZero
        (Multiplicative.ofAdd (grothendieckMap P L x.toAdd)) at hLx
    rw [hLx]
    change (abelianExactStructure D).grothendieckToKZero
      (Multiplicative.ofAdd (grothendieckMap P L x.toAdd)) = 1
    change grothendieckMap P L x.toAdd = 0 at hx
    rw [hx]
    exact map_one _
  · intro ha
    have hx : x.toAdd ∈ (grothendieckMap P L).ker := by
      change grothendieckMap P L x.toAdd = 0
      apply Multiplicative.ofAdd.injective
      apply (abelianExactStructure D).grothendieckToKZero_injective
      change KMap P L 0 ((abelianExactStructure C).grothendieckToKZero x) = 1 at ha
      exact ((DFunLike.congr_fun hL x).symm.trans ha).trans (map_one _).symm
    rw [grothendieckMap_ker, ← inclusionGrothendieckMap_range] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨(abelianExactStructure P.FullSubcategory).grothendieckToKZero
      (Multiplicative.ofAdd y), ?_⟩
    exact (DFunLike.congr_fun hι (Multiplicative.ofAdd y)).trans
      (congrArg (abelianExactStructure C).grothendieckToKZero
        (congrArg Multiplicative.ofAdd hy))

section CanonicalQuotient

attribute [local instance] canonicalQuotientAbelian

variable {A : Type u} [Category.{u} A] [Abelian A]
  (S : ObjectProperty A) [S.IsSerreClass]

/-- The original canonical Serre quotient map is surjective on genuine K-zero. -/
theorem quotientKZero_surjective : Function.Surjective (quotientKMap S 0) :=
  KZeroMap_surjective S S.isoModSerre.Q

/-- Exactness at the ambient K-zero term for the original canonical inclusion and quotient. -/
theorem inclusion_range_eq_quotientKZero_ker :
    (Abelian.Devissage.KMap S 0).range = (quotientKMap S 0).ker :=
  inclusionKZero_range_eq_ker S S.isoModSerre.Q

end CanonicalQuotient

end CategoryTheory.ExactCategory.SerreLocalization

attribute [stacks 02MX
  "(1), transported to actual homotopical K-zero through the natural canonical comparison",
  colib_ref "WeibelKBook" "V, Theorem 5.1, final K-zero tail, page 35" "adaptation"
    "Only right exactness at K-zero and the terminal surjection; no higher localization claim"]
  CategoryTheory.ExactCategory.SerreLocalization.KZeroMap_surjective
  CategoryTheory.ExactCategory.SerreLocalization.inclusionKZero_range_eq_ker
  CategoryTheory.ExactCategory.SerreLocalization.quotientKZero_surjective
  CategoryTheory.ExactCategory.SerreLocalization.inclusion_range_eq_quotientKZero_ker

attribute [colib_tag "COL-0250"]
  CategoryTheory.ExactCategory.SerreLocalization.quotientKZero_surjective
  CategoryTheory.ExactCategory.SerreLocalization.inclusion_range_eq_quotientKZero_ker
