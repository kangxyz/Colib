/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Resolution.BoundedStrata
public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Resolution.Strata
public import Colib.KTheory.Quillen.Resolution.SubcategoryComparison
/-!
# Quillen resolution with an arbitrary finite common bound

The adjacent finite-resolution-length strata are actual inherited exact
categories. Each successive inclusion has genuine length-one resolutions.
Iterating the proved length-one theorem gives the canonical K-isomorphism
for any finite bound. The passage to objectwise finite, unbounded lengths
is a separate union argument.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [E.IsKernelClosed P] [P.IsClosedUnderFiniteProducts]

section Strata
variable [Fact (E.ResolutionHypothesis P)]

omit [P.IsClosedUnderFiniteProducts] in
/-- Every adjacent length-stratum inclusion induces the actual all-degree
K-isomorphism furnished by the proved length-one resolution theorem. -/
theorem stratumKMap_bijective (n k : ℕ) :
    Function.Bijective ((stratumExactInclusion E P n).KMap k) :=
  inclusionOfLEKMap_bijective_of_length_one E
    (E.ResolutionLength P n) (E.ResolutionLength P (n + 1))
    (E.resolutionLength_mono P (Nat.le_succ n))
    (adjacentStratum_resolutionLength_one E P n) k

/-- The adjacent comparison is an actual homotopy equivalence, for use in
the filtered-union step as well as its induced K-group bijections. -/
def stratumClassifyingHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (stratumExactStructure E P n).KSpace
      (stratumExactStructure E P (n + 1)).KSpace :=
  inclusionOfLEClassifyingHomotopyEquivOfLengthOne E
    (E.ResolutionLength P n) (E.ResolutionLength P (n + 1))
    (E.resolutionLength_mono P (Nat.le_succ n))
    (adjacentStratum_resolutionLength_one E P n)

omit [P.IsClosedUnderFiniteProducts] in
@[simp] theorem stratumClassifyingHomotopyEquiv_toFun (n : ℕ) :
    (stratumClassifyingHomotopyEquiv E P n).toFun =
      (classifyingSpaceMap (stratumExactInclusion E P n).mapQ).hom :=
  inclusionOfLEClassifyingHomotopyEquivOfLengthOne_toFun _ _ _ _ _

/-- Iterate a specified finite number of adjacent comparisons. -/
def stratumAddHomotopyEquiv (m : ℕ) : (k : ℕ) →
    ContinuousMap.HomotopyEquiv (stratumExactStructure E P m).KSpace
      (stratumExactStructure E P (m + k)).KSpace
  | 0 => .refl _
  | k + 1 => (stratumAddHomotopyEquiv m k).trans (stratumClassifyingHomotopyEquiv E P (m + k))

omit [P.IsClosedUnderFiniteProducts] in
@[simp] theorem stratumAddHomotopyEquiv_toFun (m k : ℕ) :
    (stratumAddHomotopyEquiv E P m k).toFun =
      (classifyingSpaceMap (stratumTransition E P (Nat.le_add_right m k)).mapQ).hom := by
  induction k with
  | zero =>
    change ContinuousMap.id _ =
      (classifyingSpaceMap (CategoryTheory.ExactCategory.ExactFunctor.id (stratumExactStructure E P
        m)).mapQ).hom
    rw [CategoryTheory.ExactCategory.ExactFunctor.mapQ_id, classifyingSpaceMap_id]
    rfl
  | succ k ih =>
    change (stratumClassifyingHomotopyEquiv E P (m + k)).toFun.comp
      (stratumAddHomotopyEquiv E P m k).toFun = _
    rw [stratumClassifyingHomotopyEquiv_toFun, ih, ← TopCat.hom_comp,
      ← classifyingSpaceMap_comp, ← CategoryTheory.ExactCategory.ExactFunctor.mapQ_comp]
    rfl

omit [P.IsClosedUnderFiniteProducts] in
/-- Existence of an actual equivalence for every ordered transition, proved
by finite induction on the order proof. -/
theorem exists_stratumTransitionHomotopyEquiv {m n : ℕ} (h : m ≤ n) :
    ∃ e : ContinuousMap.HomotopyEquiv (stratumExactStructure E P m).KSpace
      (stratumExactStructure E P n).KSpace,
      e.toFun = (classifyingSpaceMap (stratumTransition E P h).mapQ).hom := by
  induction h with
  | refl =>
    refine ⟨.refl _, ?_⟩
    change ContinuousMap.id _ =
      (classifyingSpaceMap (CategoryTheory.ExactCategory.ExactFunctor.id (stratumExactStructure E P
        m)).mapQ).hom
    rw [CategoryTheory.ExactCategory.ExactFunctor.mapQ_id, classifyingSpaceMap_id]
    rfl
  | @step n h ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e.trans (stratumClassifyingHomotopyEquiv E P n), ?_⟩
    change (stratumClassifyingHomotopyEquiv E P n).toFun.comp e.toFun = _
    rw [stratumClassifyingHomotopyEquiv_toFun, he, ← TopCat.hom_comp,
      ← classifyingSpaceMap_comp, ← CategoryTheory.ExactCategory.ExactFunctor.mapQ_comp]
    rfl

/-- Every ordered transition has an actual homotopy equivalence, with no
coherent choices of inverse required by filtered realization invariance. -/
def stratumTransitionHomotopyEquiv {m n : ℕ} (h : m ≤ n) :
    ContinuousMap.HomotopyEquiv (stratumExactStructure E P m).KSpace
      (stratumExactStructure E P n).KSpace :=
  Classical.choose (exists_stratumTransitionHomotopyEquiv E P h)

omit [P.IsClosedUnderFiniteProducts] in
@[simp] theorem stratumTransitionHomotopyEquiv_toFun {m n : ℕ} (h : m ≤ n) :
    (stratumTransitionHomotopyEquiv E P h).toFun =
      (classifyingSpaceMap (stratumTransition E P h).mapQ).hom :=
  Classical.choose_spec (exists_stratumTransitionHomotopyEquiv E P h)

/-- Iteration retains the exact canonical inclusion map at each stage. -/
theorem intoStratumKMap_bijective (n k : ℕ) :
    Function.Bijective ((intoStratumExact E P n).KMap k) := by
  induction n with
  | zero =>
    exact inclusionOfLEKMap_bijective_of_reverse E P (E.ResolutionLength P 0)
      (E.le_resolutionLength P 0) (fun X hX => (E.resolutionLength_zero_iff P X).1 hX) k
  | succ n ih =>
    have hf : (intoStratumExact E P n).comp (stratumExactInclusion E P n) =
        intoStratumExact E P (n + 1) := rfl
    rw [← hf, CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
    exact (stratumKMap_bijective E P n k).comp ih

end Strata

/-- Quillen resolution for any common finite length bound. The conclusion is
bijectivity of the original canonical inclusion K-map in every degree. -/
theorem inclusionKMap_bijective_of_bounded (N : ℕ)
    (h : ∀ X, E.ResolutionLength P N X) (k : ℕ) :
    Function.Bijective (inclusionKMap E P k) := by
  let : Fact (E.ResolutionHypothesis P) :=
    ⟨fun X => by obtain ⟨R, _⟩ := h X; exact ⟨R⟩⟩
  have h₁ := intoStratumKMap_bijective E P N k
  have h₂ := inclusionKMap_bijective_of_all E (E.ResolutionLength P N) h k
  change Function.Bijective ((exactInclusion E P).KMap k)
  change Function.Bijective ((ExactSubcategory.exactInclusion E P).KMap k)
  rw [← exactInclusionOfLE_comp E P (E.ResolutionLength P N) (E.le_resolutionLength P N),
    CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  exact h₂.comp h₁

/-- The bounded-resolution equivalence with its forward map fixed. -/
def KEquivOfBounded (N : ℕ) (h : ∀ X, E.ResolutionLength P N X) (k : ℕ) :
    (ExactSubcategory.exactStructure E P).K k ≃* E.K k :=
  MulEquiv.ofBijective (inclusionKMap E P k) (inclusionKMap_bijective_of_bounded E P N h k)

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem KEquivOfBounded_coe (N : ℕ) (h : ∀ X, E.ResolutionLength P N X) (k : ℕ) :
    (↑(KEquivOfBounded E P N h k) : (ExactSubcategory.exactStructure E P).K k →* E.K k) =
        inclusionKMap E P k := rfl

end CategoryTheory.ExactCategory.Resolution
