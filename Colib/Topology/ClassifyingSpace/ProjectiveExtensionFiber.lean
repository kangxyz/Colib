/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionUnit
public import Colib.Topology.ClassifyingSpace.UnitalDiagonal

/-!
# Weak contractibility of the actual fixed-quotient extension action category

For every finite projective quotient over any unital ring, the category of
extensions stabilized in their kernels has a genuinely weakly contractible
classifying space. Multiplication is the actual pullback over the fixed quotient,
its kernel is the direct sum of the kernels, and its natural diagonal is the
actual middle-term diagonal. No contractibility input is assumed.
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Topology SSet HomotopyGroup
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] directSumMonoidal extensionFiberDirectSumAction

/-- All actual positive homotopy groups of the extension action category vanish. -/
theorem extensionAction_unitPi_subsingleton (C : Category.{u, u} R) (n : ℕ) :
    Subsingleton (ShiftedHomotopyGroup (ExtensionActionCategory R C) (extensionActionUnit R C) n) :=
  classifyingSpace_unitPi_subsingleton_of_unitalDiagonal
    (extensionActionUnit R C) (extensionActionMultiplication R C)
    (extensionActionLeftUnit R C) (extensionActionRightUnit R C)
    (extensionAction_unit_coherence R C) (extensionActionDiagonalNatTrans R C)
    (extensionAction_diagonal_unit R C) n

/-- The actual fixed-quotient extension action category is weakly contractible,
including bijectivity on path components and every positive homotopy group. -/
theorem extensionAction_weaklyContractible (C : Category.{u, u} R) :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const (ClassifyingSpace (ExtensionActionCategory R C))
        (PUnit.unit : PUnit.{u + 2})) := by
  let := extensionActionCategory_isConnected R C
  exact classifyingSpace_weaklyContractible_of_unitalDiagonal
    (extensionActionUnit R C) (extensionActionMultiplication R C)
    (extensionActionLeftUnit R C) (extensionActionRightUnit R C)
    (extensionAction_unit_coherence R C) (extensionActionDiagonalNatTrans R C)
    (extensionAction_diagonal_unit R C)

end ModuleCat.FiniteProjective
