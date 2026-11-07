/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionSpanTransport
public import Colib.Topology.ClassifyingSpace.ProjectiveExtensionFiber
public import Colib.Topology.ClassifyingSpace.EquivariantTransport

/-! # Weak equivalence of the original localized Q-span extension transport -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] directSumMonoidal directSumSymmetric extensionFiberDirectSumAction

/-- The original localized span transport is a weak equivalence. Its source and target
action categories are proved weakly contractible; no transport equivalence is assumed. -/
theorem localizedExtensionSpanTransport_isWeakHomotopyEquivalence
    {X Y : Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y) :
    IsWeakHomotopyEquivalence
      (classifyingSpaceMapUniversal (localizedExtensionSpanTransport R s)) := by
  let : ∀ A : IsoCategory R, (tensorRight A).Faithful := directSumRight_faithful R
  let : ∀ p : (exactStructure R).ExtensionFiber Y,
      (MonoidalLeftAction.actionRight (IsoCategory R) p).Faithful :=
    extensionActionRight_faithful R Y
  let : ∀ p : (exactStructure R).ExtensionFiber X,
      (MonoidalLeftAction.actionRight (IsoCategory R) p).Faithful :=
    extensionActionRight_faithful R X
  let := extensionSpanTransportLinear R s
  exact GroupCompletion.Localization.map_isWeakHomotopyEquivalence_of_weakBases
    ((exactStructure R).extensionSpanTransport s) ((exactStructure R).extensionUnit Y)
    (extensionAction_weaklyContractible R Y) (extensionAction_weaklyContractible R X)

end ModuleCat.FiniteProjective
