/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Nonempty families of continuous product extensions

A family of continuous maps selected by a predicate extends to the product
with any topological space by ignoring the second coordinate. Each selected
map supplies its own extension, so the codomain need not be nonempty.
-/

@[expose] public section

namespace ContinuousMap

/-- A predicate-selected family of continuous maps has a family of extensions
constant in the second product coordinate. -/
instance instNonemptySubtypeToProd {X T Z : Type*}
    [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace Z]
    (p : C(X, Z) → Prop) :
    Nonempty ({f : C(X, Z) // p f} → C(X × T, Z)) :=
  ⟨fun f ↦ f.val.comp ContinuousMap.fst⟩

end ContinuousMap
