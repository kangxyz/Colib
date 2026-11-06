/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.FinitePosetCriterion
public import Colib.CategoryTheory.Waldhausen.Approximation.FinitePoset.WeakCommaCone
public import Colib.CategoryTheory.TheoremA.WeakComma

/-!
# Complete weak equivalence of an approximation functor on weak categories

App1/App2, exactness, target two-out-of-three and given functorial source
factorization give genuine finite-poset replacements and cones in every
original weak comma. The actual poset-resolution criterion proves these
comma nerves weakly contractible. Weak Quillen Theorem A then applies to the
ORIGINAL exact functor on weak-equivalence categories, in all degrees.
This is the weak-category stage; an S-construction approximation theorem
requires the corresponding row hypotheses and a realization argument.

Implementation provenance:
`Quillen/Waldhausen/Approximation/WeakEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat SSet
open CategoryTheory
universe u
namespace CategoryTheory

namespace Waldhausen.HasApproximationProperty
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty] (T : FunctorialFactorization W)

include h T in
/-- Full original weak-comma contractibility in the weak sense follows from
actual finite replacements, without a global contraction choice. -/
theorem weakComma_toPoint_isWeakHomotopyEquivalence (Y : WideSubcategory V.weq) :
    IsWeakHomotopyEquivalence (ContinuousMap.const
      (ClassifyingSpace (WeakComma hF Y)) (PUnit.unit : PUnit.{u + 1})) := by
  apply classifyingSpace_toPoint_isWeakHomotopyEquivalence_of_finitePoset
  intro J _ _ K
  exact finitePoset_weakComma_classifyingMap_nullhomotopic h hF T Y K

include h T in
/-- App1/App2 and genuine functorial source factorization imply complete
weakness of the ORIGINAL functor between weak-equivalence categories. -/
theorem weakFunctor_classifyingSpaceMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (classifyingSpaceMap hF.weakFunctor).hom :=
  TheoremA.classifyingSpaceMap_isWeakHomotopyEquivalence_of_weak_comma hF.weakFunctor
    (weakComma_toPoint_isWeakHomotopyEquivalence h hF T)

end Waldhausen.HasApproximationProperty
end CategoryTheory
