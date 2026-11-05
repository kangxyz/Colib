/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Quasi-isomorphisms detected by cycles modulo boundaries

This strengthens the exact-cycle lifting criterion migrated from
`Aglib.Algebra.Homology.ShortComplex.ModuleQuasiIso` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f` to a necessary and sufficient criterion.
It uses Mathlib's actual module homology data. Lifting is only required modulo
boundaries, so the middle component need not surject onto cycles.

The same equivalence is private (`quasiIso_iff_cycles`) in the pinned Stacks
`Homology.Eta.Derived`; related sufficient criteria are private in its DGA and
naive cotangent developments. This lower-level interface needs only a ring and permits
an independent module universe. No Koszul or homology model is introduced.
-/

@[expose] public section

universe u v

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R]

set_option backward.isDefEq.respectTransparency false in
/-- A map of module short complexes is a quasi-isomorphism exactly when it reflects
boundaries among cycles and lifts target cycles modulo boundaries. -/
theorem quasiIso_iff_liftCycles_mod_boundaries
    {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T) :
    ShortComplex.QuasiIso φ ↔
      (∀ x : S.X₂, S.g x = 0 →
        (∃ y : T.X₁, T.f y = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x) ∧
      (∀ y : T.X₂, T.g y = 0 →
        ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, T.f z = y - φ.τ₂ x) := by
  let γ : ShortComplex.LeftHomologyMapData φ
      S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData := default
  have hK (x : LinearMap.ker S.g.hom) : (γ.φK x).val = φ.τ₂ x.val := by
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp γ.commi) x
  have hH (x : LinearMap.ker S.g.hom) :
      γ.φH (Submodule.Quotient.mk x) = Submodule.Quotient.mk (γ.φK x) :=
    ConcreteCategory.congr_hom γ.commπ x
  rw [γ.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  constructor
  · rintro ⟨hinj, hsurj⟩
    constructor
    · rintro x hx ⟨y, hy⟩
      have hz : γ.φH (Submodule.Quotient.mk ⟨x, hx⟩) = 0 := by
        rw [hH]
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact ⟨y, Subtype.ext (hy.trans (hK ⟨x, hx⟩).symm)⟩
      have hz' : (Submodule.Quotient.mk ⟨x, hx⟩ :
          S.moduleCatLeftHomologyData.H) = 0 := hinj (hz.trans (map_zero γ.φH.hom).symm)
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz'
      exact ⟨z, congrArg Subtype.val hz⟩
    · intro y hy
      obtain ⟨x, hx⟩ := hsurj (Submodule.Quotient.mk ⟨y, hy⟩)
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [hH] at hx
        obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).mp hx.symm
        refine ⟨x.val, x.property, z, ?_⟩
        have hv := congrArg Subtype.val hz
        change T.f z = y - (γ.φK x).val at hv
        rwa [hK] at hv
  · rintro ⟨hboundary, hcycle⟩
    constructor
    · apply (injective_iff_map_eq_zero γ.φH.hom).mpr
      intro x hx
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        rw [hH] at hx
        obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
        obtain ⟨z, hz⟩ := hboundary x.val x.property
          ⟨y, (congrArg Subtype.val hy).trans (hK x)⟩
        exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, Subtype.ext hz⟩
    · intro y
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        obtain ⟨x, hx, z, hz⟩ := hcycle y.val y.property
        refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
        rw [hH]
        symm
        apply (Submodule.Quotient.eq _).mpr
        refine ⟨z, Subtype.ext ?_⟩
        change T.f z = y.val - (γ.φK ⟨x, hx⟩).val
        rwa [hK]

end CategoryTheory.ShortComplex
