/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.FiltrationWeakEquivalence
public import Colib.Topology.ClassifyingSpace.Adjunction

/-! # Classifying equivalence of the original fine-weak filtrations

Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/FiltrationWeakEquivalence.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, classifying-space declarations.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The original weak-filtration map induces a genuine classifying-space homotopy equivalence. -/
def weakFiltrationClassifyingHomotopyEquiv (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (FineWeakRows N n))
      (ClassifyingSpace (FineWeakChains N n)) :=
  equivalenceClassifyingHomotopyEquiv (weakFiltrationEquivalence N he n)

/-- The realized forward map is literally that of the original weak-filtration functor. -/
@[simp] theorem weakFiltrationClassifyingHomotopyEquiv_toFun
    (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    (weakFiltrationClassifyingHomotopyEquiv N he n).toFun =
      (classifyingSpaceMap (weakFiltrationPresentation N he n)).hom := rfl

/-- The realized inverse remains the actual zero-augmented cofiber-completion functor. -/
@[simp] theorem weakFiltrationClassifyingHomotopyEquiv_invFun
    (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    (weakFiltrationClassifyingHomotopyEquiv N he n).invFun =
      (classifyingSpaceMap (weakCompletionFunctor N n)).hom := rfl

end CategoryTheory.Waldhausen.Fibration.RelativeRows
