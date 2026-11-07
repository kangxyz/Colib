/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.Embedding.StupidTrunc.Maps
public import Colib.Algebra.Homology.Embedding.StupidTrunc.Transition
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.Embedding.StupidTrunc.Layer
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedTerms

/-!
# Exact brutal truncations and actual bounded-term layer sequences

Original brutal truncations and single-term layers preserve bounded termwise-P
complexes and inherited conflations. The adjacent natural maps are the actual
ambient layer sequence. No kernel closure or quasi-isomorphism preservation is
added.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.StupidTruncationExact`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

instance stupidTruncGEFunctor_additive (n : ℤ) : (stupidTruncGEFunctor (A := A) n).Additive :=
  inferInstanceAs (Functor.Additive ((ComplexShape.embeddingUpIntGE n).restrictionFunctor A ⋙
    (ComplexShape.embeddingUpIntGE n).extendFunctor A))

instance stupidTruncGELayerFunctor_additive (n : ℤ) :
    (stupidTruncGELayerFunctor (A := A) n).Additive := inferInstance

/-- In a retained degree the original brutal evaluation is naturally unchanged. -/
def stupidTruncGEEvalIso (n i : ℤ) (hi : n ≤ i) :
    stupidTruncGEFunctor (A := A) n ⋙ eval A (ComplexShape.up ℤ) i ≅
      eval A (ComplexShape.up ℤ) i :=
  NatIso.ofComponents (fun K ↦ stupidTruncGEXIso K n i hi) (by
    intro K L f
    simpa only [Functor.comp_map, eval_map, comp_f, stupidTruncGEInclusion_f_of_le K n i hi,
      stupidTruncGEInclusion_f_of_le L n i hi] using
      congrArg (fun t ↦ t.f i) (stupidTruncGEInclusion_naturality f n))

/-- Brutal truncation preserves actual short exact sequences without acyclicity. -/
theorem stupidTruncGE_shortExact (S : ShortComplex (CochainComplex A ℤ))
    (hS : S.ShortExact) (n : ℤ) : (S.map (stupidTruncGEFunctor n)).ShortExact := by
  apply (shortExact_iff_degreewise_shortExact _).2
  intro i
  change (S.map (stupidTruncGEFunctor n ⋙ eval A (ComplexShape.up ℤ) i)).ShortExact
  by_cases hi : n ≤ i
  · exact (ShortComplex.shortExact_iff_of_iso (S.mapNatIso (stupidTruncGEEvalIso n i hi))).2
      ((shortExact_iff_degreewise_shortExact S).1 hS i)
  · exact {
      mono_f := (stupidTruncGE_isZero_X S.X₁ n i (by omega)).mono _
      epi_g := (stupidTruncGE_isZero_X S.X₃ n i (by omega)).epi _
      exact := ShortComplex.exact_of_isZero_X₂ _ (stupidTruncGE_isZero_X S.X₂ n i (by omega)) }

/-- The original single-term layer functor preserves actual short exactness. -/
theorem stupidTruncGELayer_shortExact (S : ShortComplex (CochainComplex A ℤ))
    (hS : S.ShortExact) (n : ℤ) : (S.map (stupidTruncGELayerFunctor n)).ShortExact := by
  apply (shortExact_iff_degreewise_shortExact _).2
  intro i
  change ((S.map (eval A (ComplexShape.up ℤ) n)).map
    (single A (ComplexShape.up ℤ) n ⋙ eval A (ComplexShape.up ℤ) i)).ShortExact
  by_cases hi : i = n
  · subst i
    exact (ShortComplex.shortExact_iff_of_iso
      ((S.map (eval A (ComplexShape.up ℤ) n)).mapNatIso
        (singleCompEvalIsoSelf A (ComplexShape.up ℤ) n))).2
      ((shortExact_iff_degreewise_shortExact S).1 hS n)
  · exact {
      mono_f := (isZero_single_obj_X (ComplexShape.up ℤ) n (S.X₁.X n) i hi).mono _
      epi_g := (isZero_single_obj_X (ComplexShape.up ℤ) n (S.X₃.X n) i hi).epi _
      exact := ShortComplex.exact_of_isZero_X₂ _
        (isZero_single_obj_X (ComplexShape.up ℤ) n (S.X₂.X n) i hi) }

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- A brutal truncation retains the original actual term bounds and membership. -/
theorem stupidTruncGE_mem {K : CochainComplex A ℤ} (hK : boundedTerms P K) (n : ℤ) :
    boundedTerms P (stupidTruncGE K n) := by
  obtain ⟨⟨a, b, hab⟩, ht⟩ := hK
  refine ⟨⟨a, b, fun i hi ↦ ?_⟩, fun i ↦ ?_⟩
  · let : IsSplitMono ((stupidTruncGEInclusion K n).f i) :=
      stupidTruncGEInclusion_degreewiseSplitMono K n i
    exact IsZero.of_mono ((stupidTruncGEInclusion K n).f i) (hab i hi)
  · by_cases hi : n ≤ i
    · exact P.prop_of_iso (stupidTruncGEXIso K n i hi).symm (ht i)
    · exact P.prop_of_isZero (stupidTruncGE_isZero_X K n i (by omega))

/-- The actual single complex of a P-object is bounded and termwise in P. -/
theorem boundedTerms_single_mem (n : ℤ) (X : A) (hX : P X) :
    boundedTerms P ((single A (ComplexShape.up ℤ) n).obj X) := by
  refine ⟨⟨n, n, fun i hi ↦ isZero_single_obj_X (ComplexShape.up ℤ) n X i (by omega)⟩,
    fun i ↦ ?_⟩
  by_cases hi : i = n
  · subst i
    exact P.prop_of_iso (singleObjXSelf (ComplexShape.up ℤ) n X).symm hX
  · exact P.prop_of_isZero (isZero_single_obj_X (ComplexShape.up ℤ) n X i hi)

/-- The original brutal functor restricted to actual bounded termwise-P complexes. -/
def boundedTermsStupidTruncGEFunctor (n : ℤ) :
    (boundedTerms P).FullSubcategory ⥤ (boundedTerms P).FullSubcategory :=
  (boundedTerms P).lift ((boundedTerms P).ι ⋙ stupidTruncGEFunctor n)
    (fun K ↦ stupidTruncGE_mem P K.property n)

/-- The original single-term functor restricted to the same actual category. -/
def boundedTermsStupidLayerFunctor (n : ℤ) :
    (boundedTerms P).FullSubcategory ⥤ (boundedTerms P).FullSubcategory :=
  (boundedTerms P).lift ((boundedTerms P).ι ⋙ stupidTruncGELayerFunctor n)
    (fun K ↦ boundedTerms_single_mem P n (K.obj.X n) (K.property.2 n))

instance boundedTermsStupidTruncGEFunctor_additive (n : ℤ) :
    (boundedTermsStupidTruncGEFunctor P n).Additive :=
  inferInstanceAs (Functor.Additive ((boundedTerms P).lift _ _))

instance boundedTermsStupidLayerFunctor_additive (n : ℤ) :
    (boundedTermsStupidLayerFunctor P n).Additive :=
  inferInstanceAs (Functor.Additive ((boundedTerms P).lift _ _))

/-- The actual inherited transition, still natural for every chain map. -/
def boundedTermsStupidTruncGETransitionNat {n m : ℤ} (h : n ≤ m) :
    boundedTermsStupidTruncGEFunctor P m ⟶ boundedTermsStupidTruncGEFunctor P n where
  app K := (boundedTerms P).homMk (stupidTruncGETransition K.obj h)
  naturality _ _ f := ObjectProperty.hom_ext _ (stupidTruncGETransition_naturality f.hom h)

/-- The original single-term projection in the inherited category. -/
def boundedTermsStupidLayerProjectionNat (n : ℤ) :
    boundedTermsStupidTruncGEFunctor P n ⟶ boundedTermsStupidLayerFunctor P n where
  app K := (boundedTerms P).homMk (stupidTruncGELayerProjection K.obj n)
  naturality _ _ f := ObjectProperty.hom_ext _ (stupidTruncGELayerProjection_naturality f.hom n)

@[reassoc]
theorem boundedTermsStupidLayer_comp_zero (n : ℤ) :
    boundedTermsStupidTruncGETransitionNat P (by omega : n ≤ n + 1) ≫
      boundedTermsStupidLayerProjectionNat P n = 0 := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _ (stupidTruncGELayer_zero K.obj n)

variable [(abelianExactStructure A).IsExtensionClosed P]

/-- Actual exactness of the restricted original brutal truncation. -/
def boundedTermsStupidTruncGEExactFunctor (n : ℤ) :
    ExactFunctor (boundedTermsExactStructure P) (boundedTermsExactStructure P) where
  toFunctor := boundedTermsStupidTruncGEFunctor P n
  map_conflation S hS := stupidTruncGE_shortExact (S.map (boundedTerms P).ι) hS n

/-- Actual exactness of the restricted original single-term layer. -/
def boundedTermsStupidLayerExactFunctor (n : ℤ) :
    ExactFunctor (boundedTermsExactStructure P) (boundedTermsExactStructure P) where
  toFunctor := boundedTermsStupidLayerFunctor P n
  map_conflation S hS := stupidTruncGELayer_shortExact (S.map (boundedTerms P).ι) hS n

/-- The adjacent inherited sequence is the original actual ambient layer conflation. -/
theorem boundedTermsStupidLayer_conflation (n : ℤ) (K : (boundedTerms P).FullSubcategory) :
    (boundedTermsExactStructure P).conflation
      (ShortComplex.mk ((boundedTermsStupidTruncGETransitionNat P (by omega : n ≤ n + 1)).app K)
        ((boundedTermsStupidLayerProjectionNat P n).app K)
        (NatTrans.congr_app (boundedTermsStupidLayer_comp_zero P n) K)) :=
  stupidTruncGELayerSequence_shortExact K.obj n

end CochainComplex
