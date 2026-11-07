/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedTermsStrata
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.BoundedSSet

/-! # Actual bounded-term S-grids lift into their exact strata

The original S-maps of the increasing inclusions are strictly compatible.
Every finite grid lifts to a genuine common term-bound stratum, retaining its
actual zero objects, inflations, pushout squares, and inverse-image weak maps.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/BoundedTermsSSet.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe v u w w'
namespace CategoryTheory.Waldhausen.GilletWaldhausen

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
variable (w : MorphismProperty (boundedTerms P).FullSubcategory)

/-- The original weak-equivalence class restricted to the actual bounded stratum. -/
abbrev boundedTermsStratumWeak (N : ℕ) : MorphismProperty (boundedTermsStratum P
    N).FullSubcategory :=
  w.inverseImage (boundedTermsStratum P N).ι

/-- Exactness of the canonical stage inclusion, retaining the original weak maps. -/
theorem boundedTermsStratumInclusion_isExact (N : ℕ) :
    IsExact (boundedTermsStratumExactStructure P N).inflation (boundedTermsStratumWeak P w N)
      (boundedTermsExactStructure P).inflation w (boundedTermsStratum P N).ι where
  zero h := (boundedTermsStratum P N).ι.map_isZero h
  cofibration f hf := (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).map_inflation f hf
  weak _ hf := hf
  pushout hi h := (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).map_isPushout hi h

/-- Exactness of the strict increasing transition with restricted weak maps. -/
theorem boundedTermsStratumTransition_isExact {N M : ℕ} (h : N ≤ M) :
    IsExact (boundedTermsStratumExactStructure P N).inflation (boundedTermsStratumWeak P w N)
      (boundedTermsStratumExactStructure P M).inflation (boundedTermsStratumWeak P w M)
      (boundedTermsStratumTransition P h) where
  zero hz := (boundedTermsStratumTransition P h).map_isZero hz
  cofibration f hf := (boundedTermsStratumTransitionExact P h).map_inflation f hf
  weak _ hf := hf
  pushout hi hp := (boundedTermsStratumTransitionExact P h).map_isPushout hi hp

/-- The actual diagonal S-set at a specified bound. -/
abbrev boundedTermsStratumSSet (N : ℕ) : SSet.{max u v} :=
  sSet (boundedTermsStratumExactStructure P N).inflation (boundedTermsStratumWeak P w N)

/-- The actual unbounded union target S-set. -/
abbrev boundedTermsSSet : SSet.{max u v} :=
  sSet (boundedTermsExactStructure P).inflation w

/-- The canonical S-map of a bounded-stage inclusion. -/
def boundedTermsStratumSSetInclusion (N : ℕ) : boundedTermsStratumSSet P w N ⟶ boundedTermsSSet
    P w :=
  sSetMap (boundedTermsStratumInclusion_isExact P w N)

/-- The canonical S-map of an increasing transition. -/
def boundedTermsStratumSSetTransition {N M : ℕ} (h : N ≤ M) :
    boundedTermsStratumSSet P w N ⟶ boundedTermsStratumSSet P w M :=
  sSetMap (boundedTermsStratumTransition_isExact P w h)

@[simp]
theorem boundedTermsStratumSSetTransition_id (N : ℕ) :
    boundedTermsStratumSSetTransition P w (le_refl N) = 𝟙 _ := by
  ext n F
  apply Subtype.ext
  rfl

@[reassoc (attr := simp)]
theorem boundedTermsStratumSSetTransition_comp {N M L : ℕ} (h : N ≤ M) (h' : M ≤ L) :
    boundedTermsStratumSSetTransition P w h ≫ boundedTermsStratumSSetTransition P w h' =
      boundedTermsStratumSSetTransition P w (h.trans h') := by
  ext n F
  apply Subtype.ext
  rfl

@[reassoc (attr := simp)]
theorem boundedTermsStratumSSetTransition_inclusion {N M : ℕ} (h : N ≤ M) :
    boundedTermsStratumSSetTransition P w h ≫ boundedTermsStratumSSetInclusion P w M =
      boundedTermsStratumSSetInclusion P w N := by
  ext n F
  apply Subtype.ext
  rfl

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsExtensionClosed P] in
/-- Every finite actual grid has one common term bound. -/
theorem boundedTerms_grid_has_common_bound {n : SimplexCategory}
    (F : Grid n ⥤ (boundedTerms P).FullSubcategory) :
    ∃ N : ℕ, ∀ x, boundedTermsStratum P N (F.obj x) := by
  let : Finite (Grid n) := by unfold Grid; infer_instance
  exact boundedTermsStratum_covers_finite P F.obj

/-- Lifting an actual S-grid retains its zeros, inflations, quotient pushouts,
and genuine weak maps. No S-simplex conclusion is assumed in the bounded stage. -/
theorem boundedTermsGrid_isSimplex {n : SimplexCategory}
    {F : Grid n ⥤ (boundedTerms P).FullSubcategory}
    (hF : IsSimplex (boundedTermsExactStructure P).inflation w F)
    (N : ℕ) (hB : ∀ x, boundedTermsStratum P N (F.obj x)) :
    IsSimplex (boundedTermsStratumExactStructure P N).inflation (boundedTermsStratumWeak P w N)
      ((boundedTermsStratum P N).lift F hB) where
  zero t i := IsZero.of_full_of_faithful_of_isZero (boundedTermsStratum P N).ι _ (hF.zero t i)
  cofibration t i j k hij hjk := (boundedTermsStratum_inflation_iff P N _).2
    (hF.cofibration t i j k hij hjk)
  quotient t i j k hij hjk := IsPushout.of_map_of_faithful (boundedTermsStratum P N).ι
    (hF.quotient t i j k hij hjk)
  weak s t i j hst hij := hF.weak s t i j hst hij

/-- Every actual ambient S-simplex comes from one original bounded stage. -/
theorem boundedTermsStratumSSetInclusion_surjective (n : SimplexCategoryᵒᵖ)
    (F : (boundedTermsSSet P w).obj n) :
    ∃ N : ℕ, ∃ G : (boundedTermsStratumSSet P w N).obj n,
      (boundedTermsStratumSSetInclusion P w N).app n G = F := by
  obtain ⟨N, hN⟩ := boundedTerms_grid_has_common_bound P F.val
  exact ⟨N, ⟨(boundedTermsStratum P N).lift F.val hN, boundedTermsGrid_isSimplex P w F.property
    N hN⟩, rfl⟩

/-- Stage inclusions are literally injective on actual grid simplices. -/
theorem boundedTermsStratumSSetInclusion_injective (N : ℕ) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((boundedTermsStratumSSetInclusion P w N).app n) := by
  intro F G h
  apply Subtype.ext
  exact Functor.ext_of_comp_fullSubcategory (congrArg Subtype.val h)

end CategoryTheory.Waldhausen.GilletWaldhausen
