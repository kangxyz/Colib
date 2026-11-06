/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Functor.FullSubcategoryExt
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedStrata
public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.CategoryTheory.Waldhausen.ExactFunctor
public import Colib.CategoryTheory.ExactCategory.Functor.Pushouts

/-! # Actual finite S-grids lift into bounded exact strata

Canonical increasing inclusions induce strictly compatible S-maps. Every
finite S-grid in the bounded acyclic category lifts into one actual common
term-bound stratum. The weak-equivalence class is retained by inverse image,
so the construction applies to both original isomorphisms and quasi-isomorphisms.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/BoundedSSet.lean` at Quillen commit
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
variable (w : MorphismProperty (boundedAcyclic P).FullSubcategory)

/-- The original weak-equivalence class restricted to the actual bounded stratum. -/
abbrev boundedStratumWeak (N : ℕ) : MorphismProperty (boundedStratum P N).FullSubcategory :=
  w.inverseImage (boundedStratum P N).ι

/-- Exactness of the canonical stage inclusion, retaining the original weak maps. -/
theorem boundedStratumInclusion_isExact (N : ℕ) :
    IsExact (boundedStratumExactStructure P N).inflation (boundedStratumWeak P w N)
      (boundedAcyclicExactStructure P).inflation w (boundedStratum P N).ι where
  zero h := (boundedStratum P N).ι.map_isZero h
  cofibration f hf := (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).map_inflation f hf
  weak _ hf := hf
  pushout hi h := (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).map_isPushout hi h

/-- Exactness of the strict increasing transition with restricted weak maps. -/
theorem boundedStratumTransition_isExact {N M : ℕ} (h : N ≤ M) :
    IsExact (boundedStratumExactStructure P N).inflation (boundedStratumWeak P w N)
      (boundedStratumExactStructure P M).inflation (boundedStratumWeak P w M)
      (boundedStratumTransition P h) where
  zero hz := (boundedStratumTransition P h).map_isZero hz
  cofibration f hf := (boundedStratumTransitionExact P h).map_inflation f hf
  weak _ hf := hf
  pushout hi hp := (boundedStratumTransitionExact P h).map_isPushout hi hp

/-- The actual diagonal S-set at a specified bound. -/
abbrev boundedStratumSSet (N : ℕ) : SSet.{max u v} :=
  sSet (boundedStratumExactStructure P N).inflation (boundedStratumWeak P w N)

/-- The actual unbounded union target S-set. -/
abbrev boundedAcyclicSSet : SSet.{max u v} :=
  sSet (boundedAcyclicExactStructure P).inflation w

/-- The canonical S-map of a bounded-stage inclusion. -/
def boundedStratumSSetInclusion (N : ℕ) : boundedStratumSSet P w N ⟶ boundedAcyclicSSet P w :=
  sSetMap (boundedStratumInclusion_isExact P w N)

/-- The canonical S-map of an increasing transition. -/
def boundedStratumSSetTransition {N M : ℕ} (h : N ≤ M) :
    boundedStratumSSet P w N ⟶ boundedStratumSSet P w M :=
  sSetMap (boundedStratumTransition_isExact P w h)

@[simp]
theorem boundedStratumSSetTransition_id (N : ℕ) :
    boundedStratumSSetTransition P w (le_refl N) = 𝟙 _ := by
  ext n F
  apply Subtype.ext
  rfl

@[reassoc (attr := simp)]
theorem boundedStratumSSetTransition_comp {N M L : ℕ} (h : N ≤ M) (h' : M ≤ L) :
    boundedStratumSSetTransition P w h ≫ boundedStratumSSetTransition P w h' =
      boundedStratumSSetTransition P w (h.trans h') := by
  ext n F
  apply Subtype.ext
  rfl

@[reassoc (attr := simp)]
theorem boundedStratumSSetTransition_inclusion {N M : ℕ} (h : N ≤ M) :
    boundedStratumSSetTransition P w h ≫ boundedStratumSSetInclusion P w M =
      boundedStratumSSetInclusion P w N := by
  ext n F
  apply Subtype.ext
  rfl

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsExtensionClosed P] in
/-- Every finite actual grid has one common term bound. -/
theorem grid_has_common_bound {n : SimplexCategory}
    (F : Grid n ⥤ (boundedAcyclic P).FullSubcategory) :
    ∃ N : ℕ, ∀ x, boundedStratum P N (F.obj x) := by
  let : Finite (Grid n) := by unfold Grid; infer_instance
  exact boundedStratum_covers_finite P F.obj

/-- Lifting an actual S-grid retains its zeros, inflations, quotient pushouts,
and genuine weak maps. No S-simplex conclusion is assumed in the bounded stage. -/
theorem boundedGrid_isSimplex {n : SimplexCategory}
    {F : Grid n ⥤ (boundedAcyclic P).FullSubcategory}
    (hF : IsSimplex (boundedAcyclicExactStructure P).inflation w F)
    (N : ℕ) (hB : ∀ x, boundedStratum P N (F.obj x)) :
    IsSimplex (boundedStratumExactStructure P N).inflation (boundedStratumWeak P w N)
      ((boundedStratum P N).lift F hB) where
  zero t i := IsZero.of_full_of_faithful_of_isZero (boundedStratum P N).ι _ (hF.zero t i)
  cofibration t i j k hij hjk := (boundedStratum_inflation_iff P N _).2
    (hF.cofibration t i j k hij hjk)
  quotient t i j k hij hjk := IsPushout.of_map_of_faithful (boundedStratum P N).ι
    (hF.quotient t i j k hij hjk)
  weak s t i j hst hij := hF.weak s t i j hst hij

/-- Every actual ambient S-simplex comes from one original bounded stage. -/
theorem boundedStratumSSetInclusion_surjective (n : SimplexCategoryᵒᵖ)
    (F : (boundedAcyclicSSet P w).obj n) :
    ∃ N : ℕ, ∃ G : (boundedStratumSSet P w N).obj n,
      (boundedStratumSSetInclusion P w N).app n G = F := by
  obtain ⟨N, hN⟩ := grid_has_common_bound P F.val
  exact ⟨N, ⟨(boundedStratum P N).lift F.val hN, boundedGrid_isSimplex P w F.property N hN⟩, rfl⟩

/-- Stage inclusions are literally injective on actual grid simplices. -/
theorem boundedStratumSSetInclusion_injective (N : ℕ) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((boundedStratumSSetInclusion P w N).app n) := by
  intro F G h
  apply Subtype.ext
  exact Functor.ext_of_comp_fullSubcategory (congrArg Subtype.val h)

end CategoryTheory.Waldhausen.GilletWaldhausen
