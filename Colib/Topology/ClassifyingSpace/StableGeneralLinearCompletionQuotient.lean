/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionBased
public import Colib.GroupTheory.StableGeneralLinear.ElementaryQuotient
public import Colib.CategoryTheory.GroupCompletion.Monoidal
public import Colib.Topology.ClassifyingSpace.MonoidalFundamentalGroup
public import Colib.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Elementary factorization of the actual stable completion fundamental-group map

Eckmann--Hilton at the original monoidal unit, followed by the actual component
inclusion equivalence, proves commutativity of the target fundamental group.
Consequently the actual based stable map kills the stable elementary subgroup
and factors through its quotient. Neither surjectivity nor the reverse kernel
inclusion is asserted here.
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
  ModuleCat.FiniteProjective.directSumSymmetric

namespace ModuleCat.FiniteProjective.StableCompletion
variable (R : Type u) [Ring R]

/-- The ambient completion fundamental group is commutative at the actual zero-pair vertex. -/
lemma completionPiOne_mul_comm
    (a b : HomotopyGroup.Pi 1 (ClassifyingSpace (Completion R)) (zeroPoint R)) :
    a * b = b * a :=
  classifyingUnitPi_mul_comm (C := Completion R) 0 a b

/-- The actual zero-component fundamental group inherits this same commutativity. -/
lemma zeroPiOne_mul_comm (a b : HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R)) :
    a * b = b * a :=
  pathComponentPiOne_mul_comm (zeroPoint R) (completionPiOne_mul_comm R) a b

/-- The commutative group structure retains the original fundamental-group operations. -/
instance zeroPiOneCommGroup : CommGroup (HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R)) where
  mul_comm := zeroPiOne_mul_comm R

/-- Every actual stable elementary matrix is killed by the actual based completion map. -/
lemma elementary_le_ker_stableGroupPiOneMap :
    StableGeneralLinear.elementary R ≤ (stableGroupPiOneMap R).ker := by
  rw [StableGeneralLinear.elementary_eq_commutator]
  exact Abelianization.commutator_subset_ker (stableGroupPiOneMap R)

/-- The original elementary subgroup in the source fundamental group is killed by the
actual based completion homomorphism. -/
lemma elementaryPiOne_le_ker_stablePiOneMap :
    (StableGeneralLinear.elementary R).map
      (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)).toMonoidHom ≤
        (stablePiOneMap R).ker := by
  rintro x ⟨g, hg, rfl⟩
  exact elementary_le_ker_stableGroupPiOneMap R hg

/-- The actual based completion homomorphism factors through the stable elementary quotient. -/
def elementaryPiOneFactor : StableGeneralLinear.ElementaryQuotient R →*
    HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R) :=
  StableGeneralLinear.quotientLift R (stableGroupPiOneMap R)

/-- The factorization preserves every original stable matrix class exactly. -/
@[simp]
lemma elementaryPiOneFactor_quotientMap (g : StableGeneralLinear.Group R) :
    elementaryPiOneFactor R (StableGeneralLinear.quotientMap R g) = stableGroupPiOneMap R g := rfl

/-- This factors the original homomorphism, retaining its original stable-matrix values. -/
lemma elementaryPiOneFactor_comp_quotientMap :
    (elementaryPiOneFactor R).comp (StableGeneralLinear.quotientMap R) =
      stableGroupPiOneMap R := rfl

/-- The actual quotient factor is uniquely determined by its original stable-matrix values. -/
lemma elementaryPiOneFactor_unique
    (f : StableGeneralLinear.ElementaryQuotient R →*
      HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R))
    (hf : f.comp (StableGeneralLinear.quotientMap R) = stableGroupPiOneMap R) :
    f = elementaryPiOneFactor R :=
  StableGeneralLinear.quotientLift_unique R (stableGroupPiOneMap R) f hf

end ModuleCat.FiniteProjective.StableCompletion
