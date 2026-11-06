/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.KTheory.Quillen.Resolution.UnionNerve
public import Colib.Topology.FilteredRealization.Sequential
public import Mathlib.CategoryTheory.Limits.Final

/-! The actual countable resolution union, via mono-realization HEP and sequential invariance.
No global common bound and no unproved general filtered invariance is used. -/
@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.ExactCategory.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [E.IsKernelClosed P] [P.IsClosedUnderFiniteProducts]
  [Fact (E.ResolutionHypothesis P)]

/-- The actual resolution nerve diagram, reindexed along the small-model equivalence. -/
abbrev stratumNerveSequence : ℕ ⥤ SSet.{u} :=
  AsSmall.up ⋙ stratumQDiagram E P ⋙ nerveFunctor

/-- Its genuine ambient-nerve cocone. -/
def stratumNerveSequenceCocone : Cocone (stratumNerveSequence E P) :=
  (nerveFunctor.mapCocone (stratumQCocone E P)).whisker AsSmall.up

/-- Equivalence of indexing categories preserves this actual colimit. -/
def stratumNerveSequenceIsColimit : IsColimit (stratumNerveSequenceCocone E P) := by
  let : (AsSmall.up : ℕ ⥤ AsSmall.{u} ℕ).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.functor).IsEquivalence
  exact (Functor.Final.isColimitWhiskerEquiv AsSmall.up _).symm
    (stratumNerveCoconeIsColimit E P)

/-- The stage-zero inclusion into the actual objectwise-finite union is an equivalence. -/
def stratumZeroToAmbientHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (stratumExactStructure E P 0).KSpace E.KSpace :=
  Topology.FilteredRealization.sequentialStageZeroHomotopyEquiv
    (stratumNerveSequence E P) (stratumNerveSequenceCocone E P)
    (stratumNerveSequenceIsColimit E P)
    (fun n => stratumTransition_nerveMap_mono E P (Nat.le_succ n))
    (fun n => stratumTransitionHomotopyEquiv E P (Nat.zero_le n))
    (fun n => stratumTransitionHomotopyEquiv_toFun E P (Nat.zero_le n))

omit [P.IsClosedUnderFiniteProducts] in
@[simp] theorem stratumZeroToAmbientHomotopyEquiv_toFun :
    (stratumZeroToAmbientHomotopyEquiv E P).toFun =
      (classifyingSpaceMap (exactInclusion E (E.ResolutionLength P 0)).mapQ).hom := rfl

end CategoryTheory.ExactCategory.Resolution
