/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.TheoremB.NaturalTransformationCancellation
public import Colib.CategoryTheory.TheoremB.NaturalTransformationFiberLift

/-!
# Actual source-fixed cancellation inside natural-transformation fiber lifts

## Implementation provenance

Adapted from `Quillen/CategoryTheory/TheoremB/NaturalTransformationFiberCancellation.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology SSet HomotopyGroup
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace CategoryTheory.TheoremB
variable {A C D : Type u} [SmallCategory A] [SmallCategory C] [SmallCategory D]
  (P : A ⥤ C) (F : C ⥤ D) (d : D) {K : A ⥤ D}
  (α : K ⟶ P ⋙ F) (β : P ⋙ F ⟶ (Functor.const A).obj d)

/-- The unchanged reversed-first/composite track, cast only at its two endpoint maps. -/
def naturalTransformationCancellationNullhomotopy :
    ((classifyingSpaceMap F).hom.comp (classifyingSpaceMap P).hom).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint d)) :=
  ((classifyingSpaceNaturalTransformationHomotopy α).symm.trans
    (classifyingSpaceNaturalTransformationHomotopy (α ≫ β))).cast
      (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
      (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- Cancelling the actual original tracks gives a source-fixed homotopy of fiber lifts. -/
def naturalTransformationFiberCancellationHomotopy :
    (HomotopyFiber.lift (classifyingSpaceMap F).hom (classifyingSpacePoint d)
      (classifyingSpaceMap P).hom
      (naturalTransformationCancellationNullhomotopy P F d α β)).Homotopy
      (naturalTransformationFiberLift P F d β) :=
  HomotopyFiber.fiberLiftNullhomotopyHomotopy _ _ _ _ _
    (naturalTransformationCancellationHomotopy α β)

/-- Every intermediate fiber point retains the original source map. -/
theorem naturalTransformationFiberCancellationHomotopy_source
    (s : unitInterval) (x : ClassifyingSpace A) :
    (naturalTransformationFiberCancellationHomotopy P F d α β (s, x)).val.1 =
      classifyingSpaceMap P x := rfl

/-- The whole fiber path is the original endpoint-relative triangle cancellation. -/
theorem naturalTransformationFiberCancellationHomotopy_path
    (s t : unitInterval) (x : ClassifyingSpace A) :
    (naturalTransformationFiberCancellationHomotopy P F d α β (s, x)).val.2 t =
      naturalTransformationCancellationHomotopy α β (s, (t, x)) := rfl

/-- Casting the nullhomotopy leaves its original reversed/composite track unchanged. -/
theorem naturalTransformationCancellationNullhomotopy_apply
    (t : unitInterval) (x : ClassifyingSpace A) :
    naturalTransformationCancellationNullhomotopy P F d α β (t, x) =
      ((classifyingSpaceNaturalTransformationHomotopy α).symm.trans
        (classifyingSpaceNaturalTransformationHomotopy (α ≫ β))) (t, x) := rfl

end CategoryTheory.TheoremB
