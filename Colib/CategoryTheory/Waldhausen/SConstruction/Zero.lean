/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.SConstruction

/-!
# The zero simplex of the diagonal Waldhausen S-construction

The constant grid at any object equipped with `IsZero` is a simplex in every degree.
This lower simplicial construction does not depend on realization or K-groups.

Implementation provenance: the `zeroSimplex` definition is extracted unchanged from
`Colib/KTheory/Waldhausen/Basic.lean`, whose implementation was adapted from
`Quillen/Waldhausen/KTheory.lean` at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Waldhausen

variable {C : Type u} [Category.{v} C]
variable (cof weq : MorphismProperty C)

/-- The all-zero quotient diagram is a simplex in every degree. -/
def zeroSimplex [cof.ContainsIdentities] [weq.ContainsIdentities]
    (Z : C) (hZ : IsZero Z) (n : SimplexCategoryᵒᵖ) :
    (sSet cof weq).obj n :=
  ⟨(Functor.const (Grid n.unop)).obj Z, {
    zero := fun _ _ ↦ hZ
    cofibration := fun _ _ _ _ _ _ ↦ cof.id_mem Z
    quotient := fun _ _ _ _ _ _ ↦ IsPushout.id_horiz (𝟙 Z)
    weak := fun _ _ _ _ _ _ ↦ weq.id_mem Z }⟩

end CategoryTheory.Waldhausen
