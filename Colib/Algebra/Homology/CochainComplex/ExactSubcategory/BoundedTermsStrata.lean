/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.StupidTruncationFixedBounds
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedStrata

/-! # Actual increasing strata of bounded termwise complexes

Every finite family of actual bounded termwise-P complexes has a common
symmetric term bound. Canonical increasing inclusions are exact and reflect
inherited inflations by actual quotient bounds. No kernel closure or
uniform bound on the whole category is required.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedTermsStrata`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u w
namespace CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

variable (P : ObjectProperty A)

/-- The actual symmetric fixed-bound predicate inside the bounded termwise category. -/
abbrev boundedTermsStratum (N : ℕ) : ObjectProperty (boundedTerms P).FullSubcategory :=
  fixedTermsBounds P (-(N : ℤ)) N

/-- The actual strata form an increasing system. -/
theorem boundedTermsStratum_mono {N M : ℕ} (h : N ≤ M) : boundedTermsStratum P N ≤
    boundedTermsStratum P M := by
  intro K hK
  exact hK.mono (by omega) (by omega)

/-- Coverage is objectwise; no common bound is postulated for the whole category. -/
theorem boundedTermsStratum_covers (K : (boundedTerms P).FullSubcategory) :
    ∃ N : ℕ, boundedTermsStratum P N K := K.property.1.exists_symmetric

/-- A genuinely finite family has one common actual term bound. -/
theorem boundedTermsStratum_covers_finite {I : Type w} [Finite I]
    (K : I → (boundedTerms P).FullSubcategory) :
    ∃ N : ℕ, ∀ i, boundedTermsStratum P N (K i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose n hn using fun i ↦ boundedTermsStratum_covers P (K i)
  refine ⟨Finset.univ.sup n, fun i ↦ ?_⟩
  exact boundedTermsStratum_mono P (Finset.le_sup (Finset.mem_univ i)) _ (hn i)

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The inherited exact structure at a specified symmetric bound. -/
abbrev boundedTermsStratumExactStructure (N : ℕ) := fixedTermsExactStructure P (-(N : ℤ)) N

/-- The actual canonical inclusion from one bound to a larger one. -/
def boundedTermsStratumTransition {N M : ℕ} (h : N ≤ M) :
    (boundedTermsStratum P N).FullSubcategory ⥤ (boundedTermsStratum P M).FullSubcategory :=
  ObjectProperty.ιOfLE (boundedTermsStratum_mono P h)

instance boundedTermsStratumTransition_additive {N M : ℕ} (h : N ≤ M) :
    (boundedTermsStratumTransition P h).Additive where
  map_add := by intros; rfl

/-- Every canonical increasing inclusion is genuinely exact. -/
def boundedTermsStratumTransitionExact {N M : ℕ} (h : N ≤ M) :
    ExactFunctor (boundedTermsStratumExactStructure P N) (boundedTermsStratumExactStructure P M)
      where
  toFunctor := boundedTermsStratumTransition P h
  map_conflation _ hS := hS

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsExtensionClosed P] in
/-- These are strict transition functors, not merely chosen categorical equivalences. -/
@[simp]
theorem boundedTermsStratumTransition_id (N : ℕ) : boundedTermsStratumTransition P (le_refl N) =
    𝟭 _ := rfl

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsExtensionClosed P] in
@[simp]
theorem boundedTermsStratumTransition_comp {N M L : ℕ} (h : N ≤ M) (h' : M ≤ L) :
    boundedTermsStratumTransition P h ⋙ boundedTermsStratumTransition P h' =
      boundedTermsStratumTransition P (h.trans h') := rfl

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsExtensionClosed P] in
@[simp]
theorem boundedTermsStratumTransition_inclusion {N M : ℕ} (h : N ≤ M) :
    boundedTermsStratumTransition P h ⋙ (boundedTermsStratum P M).ι = (boundedTermsStratum P
      N).ι := rfl

/-- The actual bounded stratum reflects inherited inflations: an admissible
quotient of a bounded target has the same strict term bounds. -/
theorem boundedTermsStratum_inflation_iff (N : ℕ)
    {X Y : (boundedTermsStratum P N).FullSubcategory} (f : X ⟶ Y) :
    (boundedTermsStratumExactStructure P N).inflation f ↔
      (boundedTermsExactStructure P).inflation f.hom := by
  constructor
  · exact (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).map_inflation f
  · intro hf
    obtain ⟨Z, p, w, hS⟩ := hf
    apply (ExactSubcategory.inflation_iff (boundedTermsExactStructure P)
      (boundedTermsStratum P N) f).2
    refine ⟨Z, ?_, p, w, hS⟩
    intro i hi
    have hs := (shortExact_iff_degreewise_shortExact
      ((ShortComplex.mk f.hom p w).map (boundedTerms P).ι)).1 hS i
    let : Epi (p.hom.f i) := hs.epi_g
    exact IsZero.of_epi (p.hom.f i) (Y.property i hi)

end CochainComplex
