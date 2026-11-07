/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # A zero module-valued cycle class is an actual boundary

Extracted from `Quillen/Topology/LocalCoefficients/RelativeFiniteBoundary.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The proof uses the genuine
categorical cycles and homology quotient, and produces an actual chain.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace ChainComplex

/-- Vanishing in the genuine categorical homology quotient gives an actual chain boundary. -/
theorem exists_boundary_of_homologyπ_eq_zero
    (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) (z : K.cycles n)
    (hz : K.homologyπ n z = 0) :
    ∃ b : K.X (n + 1), K.d (n + 1) n b = K.iCycles n z := by
  have hp : K.pOpcycles n (K.iCycles n z) = 0 := by
    have h := ConcreteCategory.congr_hom (K.homology_π_ι n) z
    simpa only [ModuleCat.comp_apply, hz, map_zero] using h.symm
  have hb := (K.sc n).moduleCat_pOpcycles_eq_zero_iff _ |>.mp hp
  change ∃ b : K.X ((ComplexShape.down ℕ).prev n),
    K.d ((ComplexShape.down ℕ).prev n) n b = K.iCycles n z at hb
  rw [ChainComplex.prev ℕ n] at hb
  exact hb


end ChainComplex
