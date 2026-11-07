/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.Embedding.StupidTrunc.Maps
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.StupidTruncationExact
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.FixedBounds

/-! # Actual fixed-term-bound brutal truncation endpoints

A fixed stratum consists of genuine bounded termwise-P complexes with the
specified actual zero terms. Original brutal truncation is zero strictly above
the upper bound and is the original inclusion below the lower bound. No
acyclicity, kernel closure, projectivity, or globally uniform bound is assumed.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.StupidTruncationFixedBounds`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CochainComplex


open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
universe v u
namespace CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The actual brutal truncation is zero above a specified upper term bound. -/
theorem stupidTruncGE_isZero_above_bound (K : CochainComplex A ℤ) (a b n : ℤ)
    (hK : HasTermBounds K a b) (hn : b < n) : IsZero (stupidTruncGE K n) := by
  rw [IsZero.iff_id_eq_zero]
  ext i
  by_cases hi : n ≤ i
  · let : IsSplitMono ((stupidTruncGEInclusion K n).f i) :=
      stupidTruncGEInclusion_degreewiseSplitMono K n i
    exact (IsZero.of_mono ((stupidTruncGEInclusion K n).f i)
      (hK i (Or.inr (by omega)))).eq_of_src _ _
  · exact (stupidTruncGE_isZero_X K n i (by omega)).eq_of_src _ _

/-- The original brutal inclusion is invertible below a specified lower term bound. -/
theorem stupidTruncGEInclusion_isIso_below_bound (K : CochainComplex A ℤ) (a b n : ℤ)
    (hK : HasTermBounds K a b) (hn : n ≤ a) : IsIso (stupidTruncGEInclusion K n) := by
  have (i : ℤ) : IsIso ((stupidTruncGEInclusion K n).f i) := by
    by_cases hi : n ≤ i
    · rw [stupidTruncGEInclusion_f_of_le K n i hi]
      infer_instance
    · exact (stupidTruncGE_isZero_X K n i (by omega)).isIso
        (hK i (Or.inl (by omega))) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- A specified actual term-bound stratum of the ambient bounded-term category. -/
def fixedTermsBounds (P : ObjectProperty A) (a b : ℤ) :
    ObjectProperty (boundedTerms P).FullSubcategory := fun K ↦ HasTermBounds K.obj a b

/-- Increasing the actual allowed interval gives the original full-subcategory inclusion. -/
theorem fixedTermsBounds_mono (P : ObjectProperty A) {a b a' b' : ℤ}
    (ha : a' ≤ a) (hb : b ≤ b') : fixedTermsBounds P a b ≤ fixedTermsBounds P a' b' :=
  fun _ hK i hi ↦ hK i (by rcases hi with hi | hi <;> omega)

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

instance fixedTermsBounds_containsZero (a b : ℤ) : (fixedTermsBounds P a b).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun i _ ↦
    (eval A (ComplexShape.up ℤ) i).map_isZero ((boundedTerms P).ι.map_isZero (isZero_zero _))⟩

instance fixedTermsBounds_closedUnderIsomorphisms (a b : ℤ) :
    (fixedTermsBounds P a b).IsClosedUnderIsomorphisms where
  of_iso e hK i hi := (hK i hi).of_iso
    (((boundedTerms P).ι ⋙ eval A (ComplexShape.up ℤ) i).mapIso e).symm

/-- Above the upper bound, the original restricted brutal functor is naturally zero. -/
def fixedTermsStupidTruncGEZeroIso (a b n : ℤ) (hn : b < n) :
    (fixedTermsBounds P a b).ι ⋙ boundedTermsStupidTruncGEFunctor P n ≅
      (Functor.const (fixedTermsBounds P a b).FullSubcategory).obj
        (0 : (boundedTerms P).FullSubcategory) :=
  NatIso.ofComponents (fun K ↦ (boundedTerms P).isoMk
    ((stupidTruncGE_isZero_above_bound K.obj.obj a b n K.property hn).iso
      ((boundedTerms P).ι.map_isZero (isZero_zero _)))) (by
        intro K L f
        apply ObjectProperty.hom_ext
        exact (stupidTruncGE_isZero_above_bound K.obj.obj a b n K.property hn).eq_of_src _ _)

/-- Below the lower bound, its actual inclusion is a natural isomorphism. -/
def fixedTermsStupidTruncGEIdentityIso (a b n : ℤ) (hn : n ≤ a) :
    (fixedTermsBounds P a b).ι ⋙ boundedTermsStupidTruncGEFunctor P n ≅
      (fixedTermsBounds P a b).ι :=
  NatIso.ofComponents (fun K ↦ by
    let := stupidTruncGEInclusion_isIso_below_bound K.obj.obj a b n K.property hn
    exact (boundedTerms P).isoMk (asIso (stupidTruncGEInclusion K.obj.obj n))) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact stupidTruncGEInclusion_naturality f.hom.hom n)

/-- The forward endpoint map is exactly the original brutal inclusion. -/
@[simp]
theorem fixedTermsStupidTruncGEIdentityIso_hom (a b n : ℤ) (hn : n ≤ a)
    (K : (fixedTermsBounds P a b).FullSubcategory) :
    (((fixedTermsStupidTruncGEIdentityIso P a b n hn).hom.app K).hom) =
      stupidTruncGEInclusion K.obj.obj n := rfl

variable [(abelianExactStructure A).IsExtensionClosed P]

instance fixedTermsBounds_extensionClosed (a b : ℤ) :
    (boundedTermsExactStructure P).IsExtensionClosed (fixedTermsBounds P a b) where
  prop_middle {S} hS h₁ h₃ i hi := by
    have hsi := (shortExact_iff_degreewise_shortExact (S.map (boundedTerms P).ι)).1 hS i
    exact hsi.exact.isZero_X₂ ((h₁ i hi).eq_of_src _ _) ((h₃ i hi).eq_of_tgt _ _)

instance fixedTermsBounds_closedUnderFiniteProducts (a b : ℤ) :
    (fixedTermsBounds P a b).IsClosedUnderFiniteProducts :=
  (boundedTermsExactStructure P).extensionClosed_finiteProducts (fixedTermsBounds P a b)

/-- The actual inherited exact structure on each specified term-bound stratum. -/
def fixedTermsExactStructure (a b : ℤ) :=
  ExactSubcategory.exactStructure (boundedTermsExactStructure P) (fixedTermsBounds P a b)

/-- The original inclusion of a fixed term-bound stratum is genuinely exact. -/
def fixedTermsInclusionExactFunctor (a b : ℤ) :
    ExactFunctor (fixedTermsExactStructure P a b) (boundedTermsExactStructure P) :=
  ExactSubcategory.exactInclusion (boundedTermsExactStructure P) (fixedTermsBounds P a b)

/-- The original brutal functor restricted to each specified stratum is genuinely exact. -/
def fixedTermsStupidTruncGEExactFunctor (a b n : ℤ) :
    ExactFunctor (fixedTermsExactStructure P a b) (boundedTermsExactStructure P) :=
  (fixedTermsInclusionExactFunctor P a b).comp (boundedTermsStupidTruncGEExactFunctor P n)

/-- The actual single-term layer restricted to the same stratum is genuinely exact. -/
def fixedTermsStupidLayerExactFunctor (a b n : ℤ) :
    ExactFunctor (fixedTermsExactStructure P a b) (boundedTermsExactStructure P) :=
  (fixedTermsInclusionExactFunctor P a b).comp (boundedTermsStupidLayerExactFunctor P n)

end CochainComplex
