/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Homotopy

/-!
Adapted from `Quillen/Topology/LocalCoefficients/DegreeRaisingHomotopy.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Packaging proved degreewise homotopy equations

This constructor packages explicit degree-raising maps and their already-proved
boundary equations into mathlib's chain homotopy. It does not construct any
subdivision operator or supply any boundary equation.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ChainComplex

variable {V : Type*} [Category* V] [Preadditive V]

/-- Extend degree-raising components to the chain-complex shape. -/
def degreeRaisingData {C : ChainComplex V ℕ}
    (H : ∀ n, C.X n ⟶ C.X (n + 1)) (i j : ℕ)
    (h : (ComplexShape.down ℕ).Rel j i) : C.X i ⟶ C.X j := by
  simp only [ComplexShape.down_Rel] at h
  subst j
  exact H i

/-- Package explicit maps satisfying the homotopy equations into a chain homotopy. -/
def homotopyOfDegreeRaising {C : ChainComplex V ℕ} (S : C ⟶ C)
    (H : ∀ n, C.X n ⟶ C.X (n + 1))
    (hzero : H 0 ≫ C.d 1 0 = 𝟙 (C.X 0) - S.f 0)
    (hsucc : ∀ n, H (n + 1) ≫ C.d (n + 2) (n + 1) + C.d (n + 1) n ≫ H n =
      𝟙 (C.X (n + 1)) - S.f (n + 1)) : Homotopy (𝟙 C) S := by
  have heq : Homotopy.nullHomotopicMap' (degreeRaisingData H) = 𝟙 C - S := by
    ext n : 1
    cases n with
    | zero =>
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (k₁ := 1) rfl
        (fun l ↦ by simp only [ComplexShape.down_Rel]; omega)]
      simpa only [degreeRaisingData, HomologicalComplex.sub_f_apply,
        HomologicalComplex.id_f] using hzero
    | succ n =>
      rw [Homotopy.nullHomotopicMap'_f (k₂ := n + 2) (k₀ := n) rfl rfl]
      simpa only [degreeRaisingData, HomologicalComplex.sub_f_apply,
        HomologicalComplex.id_f, add_comm] using hsucc n
  refine Homotopy.equivSubZero.symm ?_
  rw [← heq]
  exact Homotopy.nullHomotopy' (degreeRaisingData H)

end ChainComplex
