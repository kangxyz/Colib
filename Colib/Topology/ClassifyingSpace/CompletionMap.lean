/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.GroupoidCompletion

/-!
# Original completed-loop comparison

Extracted from the third declaration of
`Quillen/Topology/ClassifyingSpace/GroupoidCompletion.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. This is the actual original functor's
endomorphism monoid map. No injectivity, retraction or bijectivity is asserted.
-/
@[expose] public noncomputable section

universe u v

open CategoryTheory

namespace CategoryTheory

/-- The canonical comparison on any chosen vertex endomorphism monoid.
The codomain is the actual topological fundamental group. -/
def classifyingGroupoidCompletionMap (C : Type u) [Category.{v} C] (c : C) :
    End ((⊤ : MorphismProperty C).Q.obj c) →*
      FundamentalGroup (ClassifyingSpace C) (classifyingSpacePoint c) :=
  (classifyingGroupoidCompletionFunctor C).mapEnd ((⊤ : MorphismProperty C).Q.obj c)

end CategoryTheory
