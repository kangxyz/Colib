/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeMonoidal
public import Colib.CategoryTheory.GroupCompletion.MonoidalFunctor
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionBased
public import Colib.Topology.Homotopy.HomotopyGroup.PathComponentWeakEquivalence

/-!
# Actual change of rings on the independent projective completion

Both coordinates and the translating denominator use the original right-module
base-change functor. The original initial comparison gives the precise path
between the image of the rank-zero object and the target rank-zero object.

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/ProjectiveCompletionBaseChange.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology SSet HomotopyGroup
open CategoryTheory MonoidalCategory
universe u
namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- The actual actor-changing functor on both original completion coordinates. -/
def completionBaseChange : StableCompletion.Completion R ⥤ StableCompletion.Completion S :=
  GroupCompletion.monoidalMap (rightBaseChange f).core

/-- The original unit entry commutes up to its canonical unit comparison. -/
def completionBaseChangeUnitIso :
    GroupCompletion.Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) ⋙ completionBaseChange f ≅
      (rightBaseChange f).core ⋙
        GroupCompletion.Localization.unitEntry (C := IsoCategory Sᵐᵒᵖ) :=
  GroupCompletion.monoidalMapUnitIso (rightBaseChange f).core

/-- Both original rank-zero coordinates are rebased by the actual inverse unit isomorphism. -/
def completionBaseChangeZeroIso :
    (completionBaseChange f).obj (StableCompletion.stageObject R 0) ≅
      StableCompletion.stageObject S 0 :=
  (GroupCompletion.ActionLocalization.ofFunctor
    (C := IsoCategory Sᵐᵒᵖ) (D := IsoCategory Sᵐᵒᵖ × IsoCategory Sᵐᵒᵖ)).mapIso
      ((Functor.Monoidal.εIso (rightBaseChange f).core).symm.prod
        (Functor.Monoidal.εIso (rightBaseChange f).core).symm)

/-- The actual continuous completion map, before restriction to its zero component. -/
def completionBaseChangeMap :
    C(ClassifyingSpace (StableCompletion.Completion R),
      ClassifyingSpace (StableCompletion.Completion S)) :=
  classifyingSpaceMapUniversal (completionBaseChange f)

/-- The original unit-comparison edge supplies the precise ambient basepoint path. -/
def completionBaseChangeBasepointPath :
    Path (completionBaseChangeMap f (StableCompletion.zeroPoint R))
      (StableCompletion.zeroPoint S) :=
  (classifyingSpacePath (completionBaseChangeZeroIso f).hom).cast
    (classifyingSpaceMapUniversal_point (completionBaseChange f)
      (StableCompletion.stageObject R 0)) rfl

/-- Restrict the unchanged original map to the genuine zero components. -/
def zeroCompletionBaseChangeMap :
    C(StableCompletion.ZeroComponent R, StableCompletion.ZeroComponent S) :=
  pathComponentMap (completionBaseChangeMap f) (StableCompletion.zeroPoint R)
    (StableCompletion.zeroPoint S) ⟨completionBaseChangeBasepointPath f⟩

/-- The restriction changes no point of the original continuous map. -/
@[simp]
theorem zeroCompletionBaseChangeMap_val (x : StableCompletion.ZeroComponent R) :
    (zeroCompletionBaseChangeMap f x).val = completionBaseChangeMap f x.val := rfl

/-- The component basepoint path retains the entire original comparison edge. -/
def zeroCompletionBaseChangeBasepointPath :
    Path (zeroCompletionBaseChangeMap f (StableCompletion.zeroBase R))
      (StableCompletion.zeroBase S) :=
  pathComponentMapBasepointPath (completionBaseChangeMap f) (StableCompletion.zeroPoint R)
    (StableCompletion.zeroPoint S) (completionBaseChangeBasepointPath f)

/-- Every point of the component track is the original ring-change basepoint track. -/
@[simp]
theorem zeroCompletionBaseChangeBasepointPath_val (t : unitInterval) :
    (zeroCompletionBaseChangeBasepointPath f t).val =
      completionBaseChangeBasepointPath f t := rfl

end ModuleCat.FiniteProjective
