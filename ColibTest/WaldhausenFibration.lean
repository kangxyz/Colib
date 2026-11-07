/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Waldhausen.Fibration.GeneralComparison

/-!
# Original-map Waldhausen fibration regression tests

The global test keeps object and morphism universes independent. Projection and
nullhomotopy tests check the actual path-space comparison, not an abstract fiber model.
-/

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open Topology

universe u v

section General

variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

example (x : (acyclicStructure N).Delooping) :
    (canonicalFiberMap N x).1.1 = acyclicInclusionMap N x := rfl

example (x : (acyclicStructure N).Delooping) (t : unitInterval) :
    (canonicalFiberMap N x).1.2 t = acyclicNullhomotopy N (t, x) := rfl

example [N.coarse.weq.HasTwoOutOfThreeProperty] (he : ExtensionAxiom N.coarse)
    (D : RowFactorization.JointData N) (hs : RowFactorization.SecondEndpointSection N D) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N) :=
  canonicalFiberMap_isWeakHomotopyEquivalence_general N he D hs

end General

section Small

variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)

example : IsWeakHomotopyEquivalence (RelativeRows.totalTailFiberComparison N) :=
  RelativeRows.totalTailFiberComparison_isWeakHomotopyEquivalence N

end Small
