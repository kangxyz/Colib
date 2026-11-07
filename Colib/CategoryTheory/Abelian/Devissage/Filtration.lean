/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Filtration.Basic
public import Colib.CategoryTheory.ExactCategory.Abelian

/-! # Objectwise existence of finite abelian filtrations -/
/-!
Implementation provenance: adapted from
`Quillen/Aglib/CategoryTheory/ExactCategory/Filtration/Hypothesis.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Native Mathlib full subcategories, Colib exact structures,
restricted spans, actual realization maps and their universes are retained.
No extension-closure, uniform filtration bound, alternate K-model or Aglib import is added.
-/

@[expose] public section

open CategoryTheory.ExactCategory
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Abelian.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

/-- Classical dévissage requires finite filtrations by actual short exact
sequences, starting with a zero object, and with successive quotients in `P`.
No extension closure is required of `P`. -/
def FiltrationHypothesis : Prop :=
  ∀ X : C, Nonempty ((abelianExactStructure C).Filtration P X)

end CategoryTheory.Abelian.Devissage
