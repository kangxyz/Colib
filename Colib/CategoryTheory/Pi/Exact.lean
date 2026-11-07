/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.Pi.Abelian

/-! # Exact evaluation in abelian category families

Adapted from `Quillen/Aglib/CategoryTheory/Pi/Abelian.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

Extend the native pointwise abelian structure with short-exactness detection and
coordinate evaluation bundled for the standard exact structures. The index, object and
morphism universes remain independent.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.Pi
universe u v w
variable {I : Type u} (C : I → Type v) [∀ i, Category.{w} (C i)]

/-- A sequence of families is short exact exactly when every coordinate sequence is. -/
theorem shortExact_pi_iff [∀ i, Abelian (C i)] (S : ShortComplex (∀ i, C i)) :
    S.ShortExact ↔ ∀ i, (S.map (Pi.eval C i)).ShortExact :=
  ⟨fun h i => h.map_of_exact (Pi.eval C i), shortExact_pi_of C S⟩

/-- Actual coordinate evaluation, bundled for the standard abelian exact structures. -/
def exactEvaluation [∀ i, Abelian (C i)] (i : I) :
    ExactCategory.ExactFunctor (ExactCategory.abelianExactStructure (∀ i, C i))
      (ExactCategory.abelianExactStructure (C i)) where
  toFunctor := Pi.eval C i
  map_conflation _ h := h.map_of_exact (Pi.eval C i)

end CategoryTheory.Pi
