/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletion

/-!
# Original finite-stage compatibility of the stable completion map

The canonical common-universe homeomorphisms transport the proved finite-stage
square back to the original single-object matrix-group classifying spaces.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Topology SSet HomotopyGroup CategoryTheory.Limits
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal

namespace ModuleCat.FiniteProjective.StableCompletion
variable (R : Type u) [Ring R]

/-- The actual finite matrix action, on its original single-object classifying space. -/
def finiteCompletionMap (n : ℕ) :
    C(ClassifyingSpace (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)),
      ClassifyingSpace (Completion R)) :=
  (classifyingSpaceMapUniversal (stageFunctor R n)).comp
    ⟨asSmallClassifyingHomeomorph
        (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)),
      (asSmallClassifyingHomeomorph
        (SingleObj (Matrix.GeneralLinearGroup (Fin n) R))).continuous⟩

/-- Restricting the stable comparison along the original finite inclusion gives the original
finite matrix action, up to the explicitly proved projection-inverse homotopy. -/
lemma stableMap_stage (n : ℕ) :
    ((stableMap R).comp (StableGeneralLinear.stageMap R n).hom).Homotopic
      (finiteCompletionMap R n) := by
  let hn : C(ClassifyingSpace (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)),
      ClassifyingSpace (StableGeneralLinear.finiteCategory R n)) :=
    ⟨asSmallClassifyingHomeomorph
        (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)),
      (asSmallClassifyingHomeomorph
        (SingleObj (Matrix.GeneralLinearGroup (Fin n) R))).continuous⟩
  let hs : C(ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)),
      ClassifyingSpace (StableGeneralLinear.stableCategory R)) :=
    ⟨asSmallClassifyingHomeomorph
        (SingleObj (StableGeneralLinear.Group R)),
      (asSmallClassifyingHomeomorph
        (SingleObj (StableGeneralLinear.Group R))).continuous⟩
  have hc : hs.comp (StableGeneralLinear.stageMap R n).hom =
      (classifyingSpaceMap (StableGeneralLinear.smallFunctor
        (StableGeneralLinear.of R n))).hom.comp hn := by
    ext x
    exact (StableGeneralLinear.smallFunctor_classifying_naturality
      (StableGeneralLinear.of R n) x).symm
  have he : stableMap R = (smallStableMap R).comp hs := rfl
  rw [he, ContinuousMap.comp_assoc, hc, ← ContinuousMap.comp_assoc]
  exact (smallStableMap_stage R n).comp (ContinuousMap.Homotopic.refl hn)

end ModuleCat.FiniteProjective.StableCompletion
