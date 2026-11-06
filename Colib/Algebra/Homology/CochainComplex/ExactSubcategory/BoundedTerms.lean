/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedAcyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Actual bounded complexes with terms in an inherited exact subcategory

This is the ambient bounded termwise-P category, without an acyclicity
condition. Its inherited exact structure, shifts, and actual mapping cones
are supplied by proved closure properties. Kernel closure is not required.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedTerms`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped ZeroObject
universe v u
namespace CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Actual term bounds and actual membership of every term, with no homology condition. -/
def boundedTerms (P : ObjectProperty A) : ObjectProperty (CochainComplex A ℤ) := fun K ↦
  TermBounded K ∧ ∀ n : ℤ, P (K.X n)

variable (P : ObjectProperty A)

/-- Every integer shift retains boundedness and all actual term memberships. -/
theorem boundedTerms_shift {K : CochainComplex A ℤ} (hK : boundedTerms P K) (s : ℤ) :
    boundedTerms P (K⟦s⟧) := by
  obtain ⟨⟨a, b, hab⟩, hterms⟩ := hK
  refine ⟨⟨a - s, b - s, fun i hi ↦ ?_⟩, fun i ↦ hterms (i + s)⟩
  change IsZero (K.X (i + s))
  exact hab (i + s) (by omega)

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- Genuine zero complexes are bounded and termwise in P. -/
theorem boundedTerms_of_isZero {K : CochainComplex A ℤ} (hK : IsZero K) : boundedTerms P K := by
  have hz (n : ℤ) := (eval A (ComplexShape.up ℤ) n).map_isZero hK
  exact ⟨⟨0, 0, fun n _ ↦ hz n⟩, fun n ↦ P.prop_of_isZero (hz n)⟩

instance boundedTerms_containsZero : (boundedTerms P).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, boundedTerms_of_isZero P (isZero_zero _)⟩

instance boundedTerms_closedUnderIsomorphisms : (boundedTerms P).IsClosedUnderIsomorphisms where
  of_iso e hK := by
    obtain ⟨⟨a, b, hab⟩, hterms⟩ := hK
    let en (n : ℤ) := (eval A (ComplexShape.up ℤ) n).mapIso e
    exact ⟨⟨a, b, fun n hn ↦ (hab n hn).of_iso (en n).symm⟩,
      fun n ↦ P.prop_of_iso (en n) (hterms n)⟩

variable [(abelianExactStructure A).IsExtensionClosed P]

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
/-- Actual degreewise short exact extensions preserve bounds and term membership. -/
theorem boundedTerms_of_shortExact {S : ShortComplex (CochainComplex A ℤ)}
    (hS : S.ShortExact) (h₁ : boundedTerms P S.X₁) (h₃ : boundedTerms P S.X₃) :
    boundedTerms P S.X₂ := by
  obtain ⟨⟨a, b, hab⟩, ht₁⟩ := h₁
  obtain ⟨⟨c, d, hcd⟩, ht₃⟩ := h₃
  have hs (n : ℤ) := (shortExact_iff_degreewise_shortExact S).1 hS n
  refine ⟨⟨min a c, max b d, fun n hn ↦ ?_⟩, fun n ↦ ?_⟩
  · have hz₁ := hab n (hn.elim
      (fun h ↦ Or.inl (lt_of_lt_of_le h (min_le_left _ _)))
      (fun h ↦ Or.inr (lt_of_le_of_lt (le_max_left _ _) h)))
    have hz₃ := hcd n (hn.elim
      (fun h ↦ Or.inl (lt_of_lt_of_le h (min_le_right _ _)))
      (fun h ↦ Or.inr (lt_of_le_of_lt (le_max_right _ _) h)))
    exact (hs n).exact.isZero_X₂ (hz₁.eq_of_src _ _) (hz₃.eq_of_tgt _ _)
  · exact CategoryTheory.ExactCategory.ExactStructure.IsExtensionClosed.prop_middle (E :=
    abelianExactStructure A)
      (hs n) (ht₁ n) (ht₃ n)

instance boundedTerms_extensionClosed :
    (abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed (boundedTerms P) where
  prop_middle := boundedTerms_of_shortExact P

instance boundedTerms_closedUnderFiniteProducts : (boundedTerms P).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex A ℤ)).extensionClosed_finiteProducts (boundedTerms P)

/-- The actual inherited exact structure on all bounded termwise-P complexes. -/
def boundedTermsExactStructure :=
  ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A ℤ)) (boundedTerms P)

omit [P.ContainsZero] in
/-- The actual mapping cone of any chain map remains bounded and termwise in P. -/
theorem boundedTerms_mappingCone {K L : CochainComplex A ℤ}
    (hK : boundedTerms P K) (hL : boundedTerms P L) (f : K ⟶ L) :
    boundedTerms P (mappingCone f) := by
  obtain ⟨⟨a, b, hab⟩, htK⟩ := hK
  obtain ⟨⟨c, d, hcd⟩, htL⟩ := hL
  refine ⟨⟨min (a - 1) c, max (b - 1) d, fun n hn ↦ ?_⟩, fun n ↦ ?_⟩
  · exact (mappingCone.isZero_X_iff f n).2
      ⟨hab (n + 1) (by omega), hcd n (by omega)⟩
  · let e := homotopyCofiber.XIsoBiprod f n (n + 1) rfl
    exact P.prop_of_iso e.symm ((abelianExactStructure A).prop_biprod P (htK (n + 1)) (htL n))

end CochainComplex
