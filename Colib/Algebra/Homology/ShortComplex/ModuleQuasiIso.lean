/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Colib.Algebra.Homology.ShortComplex.ModuleQuasiIsoCriterion

/-!
# An elementwise quasi-isomorphism criterion for module complexes

A morphism of short complexes induces an isomorphism on homology when cycles
lift and a cycle whose image is a boundary was already a boundary. The proof
uses the actual kernel/range-quotient homology data in the module category.

Adapted from `Aglib.Algebra.Homology.ShortComplex.ModuleQuasiIso` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The single theorem retains its original
statement; its proof is now a short corollary of the modulo-boundary criterion.
No new homology or Koszul model is introduced.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R]

/-- Cycle lifting and reflection of boundaries imply an actual quasi-isomorphism. -/
theorem quasiIso_of_liftCycles_of_reflectBoundaries
    {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)
    (hcycle : ∀ y : T.X₂, T.g y = 0 → ∃ x : S.X₂, S.g x = 0 ∧ φ.τ₂ x = y)
    (hboundary : ∀ x : S.X₂, S.g x = 0 →
      (∃ y : T.X₁, T.f y = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x) :
    ShortComplex.QuasiIso φ := by
  apply (quasiIso_iff_liftCycles_mod_boundaries φ).mpr
  refine ⟨hboundary, ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hcycle y hy
  exact ⟨x, hx, 0, by simp [hxy]⟩

end CategoryTheory.ShortComplex
