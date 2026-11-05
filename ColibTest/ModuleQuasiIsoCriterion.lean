/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

import Colib.Algebra.Homology.ShortComplex.ModuleQuasiIso

/-! Tests for the general criterion and the original sufficient API. -/

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

-- Independent ring and module universes, and no commutativity assumption.
example {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)
    [ShortComplex.QuasiIso φ] (y : T.X₂) (hy : T.g y = 0) :
    ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, T.f z = y - φ.τ₂ x :=
  ((ShortComplex.quasiIso_iff_liftCycles_mod_boundaries φ).mp inferInstance).2 y hy

-- The zero endomorphism of an acyclic short complex is a quasi-isomorphism.
-- For a nonzero M it does not lift all cycles exactly, so the weaker hypothesis
-- is essential rather than a renamed version of the earlier sufficient criterion.
example (M : ModuleCat.{v} R) :
    ShortComplex.QuasiIso
      (0 : ShortComplex.mk (𝟙 M) (0 : M ⟶ M) (Category.id_comp _) ⟶
        ShortComplex.mk (𝟙 M) (0 : M ⟶ M) (Category.id_comp _)) := by
  apply (ShortComplex.quasiIso_iff_liftCycles_mod_boundaries _).mpr
  constructor
  · intro x _ _
    exact ⟨x, rfl⟩
  · intro y _
    refine ⟨0, by simp, y, ?_⟩
    simp

-- Exact cycle lifting remains a special case, without repeating its homology proof.
example {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)
    (hcycle : ∀ y : T.X₂, T.g y = 0 → ∃ x : S.X₂, S.g x = 0 ∧ φ.τ₂ x = y)
    (hboundary : ∀ x : S.X₂, S.g x = 0 →
      (∃ y : T.X₁, T.f y = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x) :
    ShortComplex.QuasiIso φ :=
  ShortComplex.quasiIso_of_liftCycles_of_reflectBoundaries φ hcycle hboundary
