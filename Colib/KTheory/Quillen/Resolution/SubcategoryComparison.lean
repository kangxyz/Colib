/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Resolution.SubcategoryComparison
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.KTheory.Quillen.Resolution.LengthOneK
public import Colib.CategoryTheory.ExactCategory.Equivalence
public import Colib.KTheory.Quillen.Equivalence

/-! # Q and K comparisons for nested resolving subcategories -/
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
  (E : ExactStructure C) (P Q : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] [E.IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts]

instance nestedLiftExact_mapQ_isEquivalence (h : P ≤ Q) :
    (nestedLiftExact E P Q h).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro X Y i hi
    rw [← nestedLift_ofEquivalence E P Q h]
    exact (CategoryTheory.ExactCategory.ExactStructure.ofEquivalence_inflation_iff _ _ i).mpr hi
  · intro X Y p hp
    rw [← nestedLift_ofEquivalence E P Q h]
    exact (CategoryTheory.ExactCategory.ExactStructure.ofEquivalence_deflation_iff _ _ p).mpr hp

/-- Length-one resolution applied to a nested inherited exact inclusion,
with the original un-nested inclusion K-map as its conclusion. -/
theorem inclusionOfLEKMap_bijective_of_length_one [E.IsKernelClosed P]
    (hPQ : P ≤ Q)
    (h : ∀ X, (ExactSubcategory.exactStructure E Q).ResolutionLength
      (P.inverseImage Q.ι) 1 X) (n : ℕ) :
    Function.Bijective ((exactInclusionOfLE E P Q hPQ).KMap n) := by
  have h₁ := (nestedLiftExact E P Q hPQ).KMap_bijective_of_mapQ_isEquivalence n
  have h₂ := inclusionKMap_bijective_of_length_one
    (ExactSubcategory.exactStructure E Q) (P.inverseImage Q.ι) h n
  rw [← nestedLift_factor E P Q hPQ, CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  exact h₂.comp h₁

/-- The corresponding genuine classifying-space equivalence, with the
un-nested exact inclusion as its forward map. -/
def inclusionOfLEClassifyingHomotopyEquivOfLengthOne [E.IsKernelClosed P]
    (hPQ : P ≤ Q)
    (h : ∀ X, (ExactSubcategory.exactStructure E Q).ResolutionLength
      (P.inverseImage Q.ι) 1 X) :
    ContinuousMap.HomotopyEquiv (ExactSubcategory.exactStructure E P).KSpace
      (ExactSubcategory.exactStructure E Q).KSpace :=
  (classifyingHomotopyEquivOfIsEquivalence (nestedLiftExact E P Q hPQ).mapQ).trans
    (classifyingHomotopyEquivOfLengthOne (ExactSubcategory.exactStructure E Q)
      (P.inverseImage Q.ι) h)

@[simp] theorem inclusionOfLEClassifyingHomotopyEquivOfLengthOne_toFun [E.IsKernelClosed P]
    (hPQ : P ≤ Q)
    (h : ∀ X, (ExactSubcategory.exactStructure E Q).ResolutionLength
      (P.inverseImage Q.ι) 1 X) :
    (inclusionOfLEClassifyingHomotopyEquivOfLengthOne E P Q hPQ h).toFun =
      (classifyingSpaceMap (exactInclusionOfLE E P Q hPQ).mapQ).hom := by
  change (classifyingHomotopyEquivOfLengthOne (ExactSubcategory.exactStructure E Q)
    (P.inverseImage Q.ι) h).toFun.comp
      (classifyingSpaceMap (nestedLiftExact E P Q hPQ).mapQ).hom = _
  rw [classifyingHomotopyEquivOfLengthOne_toFun, ← TopCat.hom_comp,
    ← classifyingSpaceMap_comp, ← CategoryTheory.ExactCategory.ExactFunctor.mapQ_comp,
      nestedLift_factor]

/-- Equal object classes give an actual equivalence for their inherited
inclusion; this is a categorical equivalence, not a resolution assumption. -/
theorem inclusionOfLE_mapQ_isEquivalence_of_reverse (hPQ : P ≤ Q) (hQP : Q ≤ P) :
    (exactInclusionOfLE E P Q hPQ).mapQ.IsEquivalence := by
  let F := exactInclusionOfLE E P Q hPQ
  let : F.toFunctor.Full := inferInstanceAs (ObjectProperty.ιOfLE hPQ).Full
  let : F.toFunctor.Faithful := inferInstanceAs (ObjectProperty.ιOfLE hPQ).Faithful
  let : F.toFunctor.EssSurj :=
    ⟨fun Y => ⟨⟨Y.obj, hQP _ Y.property⟩, ⟨Iso.refl _⟩⟩⟩
  let : F.toFunctor.IsEquivalence := {}
  change F.mapQ.IsEquivalence
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro X Y i hi
    obtain ⟨Z, hZ, p, hp, hS⟩ := (ExactSubcategory.inflation_iff E Q _).1 hi
    exact (ExactSubcategory.inflation_iff E P _).2 ⟨Z, hQP _ hZ, p, hp, hS⟩
  · intro X Y p hp
    obtain ⟨Z, hZ, i, hi, hS⟩ := (ExactSubcategory.deflation_iff E Q _).1 hp
    exact (ExactSubcategory.deflation_iff E P _).2 ⟨Z, hQP _ hZ, i, hi, hS⟩

/-- The equivalent inherited inclusions give the same canonical all-degree
K-map equivalence. -/
theorem inclusionOfLEKMap_bijective_of_reverse (hPQ : P ≤ Q) (hQP : Q ≤ P) (n : ℕ) :
    Function.Bijective ((exactInclusionOfLE E P Q hPQ).KMap n) := by
  let := inclusionOfLE_mapQ_isEquivalence_of_reverse E P Q hPQ hQP
  exact (exactInclusionOfLE E P Q hPQ).KMap_bijective_of_mapQ_isEquivalence n

/-- If every ambient object satisfies the predicate, the inherited exact
inclusion is an actual equivalence and its canonical K-map is bijective. -/
theorem inclusionKMap_bijective_of_all (hP : ∀ X, P X) (n : ℕ) :
    Function.Bijective (inclusionKMap E P n) := by
  let F := exactInclusion E P
  let : F.toFunctor.Full := inferInstanceAs P.ι.Full
  let : F.toFunctor.Faithful := inferInstanceAs P.ι.Faithful
  let : F.toFunctor.EssSurj := ⟨fun Y => ⟨⟨Y, hP Y⟩, ⟨Iso.refl _⟩⟩⟩
  let : F.toFunctor.IsEquivalence := {}
  let : F.mapQ.IsEquivalence := by
    apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
    · intro X Y i hi
      obtain ⟨Z, p, hp, hS⟩ := hi
      exact (ExactSubcategory.inflation_iff E P _).2 ⟨Z, hP Z, p, hp, hS⟩
    · intro X Y p hp
      obtain ⟨Z, i, hi, hS⟩ := hp
      exact (ExactSubcategory.deflation_iff E P _).2 ⟨Z, hP Z, i, hi, hS⟩
  exact F.KMap_bijective_of_mapQ_isEquivalence n

end CategoryTheory.ExactCategory.Resolution
