/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Bisimplicial
public import Colib.KTheory.Waldhausen.Basic

/-!
# Zero-simplex compatibility for the bisimplicial diagonal

Adapted from `Quillen/Waldhausen/SConstruction/Bisimplicial.lean`, lines 176–181,
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This compares the actual constant diagram on an arbitrary object equipped with
`IsZero`. It does not impose a strict chosen-zero normalization.
Isolated strict compilation is recorded in the accompanying release report.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe v u
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C] (cof weq : MorphismProperty C)

/-- The diagonal identification preserves the original zero simplex exactly. -/
@[simp] theorem bisimplicialDiagonalIsoOfProperties_zero
    [cof.ContainsIdentities] [weq.ContainsIdentities]
    (Z : C) (hZ : IsZero Z) (n : SimplexCategoryᵒᵖ) :
    (bisimplicialDiagonalIsoOfProperties cof weq).hom.app n (zeroSimplex₂ cof weq Z hZ n n) =
      zeroSimplex cof weq Z hZ n := rfl

end CategoryTheory.Waldhausen
