/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Multiplicity.PrincipalEuler.Basic
public import Colib.Util.References
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Quotient.Basic
public import StacksFrontier.RingTheory.Length.IndexAdditivity

/-!
# Additivity and invariance of principal Euler length

Stacks' index theorem for a commutative ladder of short exact sequences gives
scalar Euler additivity. Finiteness of the outer scalar kernels and cokernels
already supplies finiteness of the middle ones. The source theorem with all
three finiteness hypotheses is retained as a corollary.

This rewrites the three module-level endpoints of
`Aglib.RingTheory.Multiplicity.PrincipalEuler.Additivity` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, source SHA-256
`ff7dc2b939e2e72a71a1b3a65b921037aefdabee2093e138b40ef73c9ec26f74`.
That source credits `R5Lab.RingTheory.LocalLength.PrincipalEulerAdditivity` at
revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`26ee2397a837a665bc1b1c6f248fdacdc0d43009ea147acb68137233d7c5446d`.
The Motivic reuse is recorded in Aglib's `docs/migration/motivic-milnor-k.json`.

No scalar snake sequence is reconstructed. The source integer telescoping
helper is not part of this module's migrated surface. The ring and all three
module carriers have independent universes.
-/

@[expose] public noncomputable section

universe u v w z

namespace Module

variable {A : Type u} [CommRing A]
  {U : Type v} {V : Type w} {W : Type z}
  [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
  [AddCommGroup W] [Module A W]

/-- In a short exact sequence, finite scalar homology at the two ends implies
finite scalar homology in the middle and additivity of principal Euler length. -/
@[colib_tag "COL-0170",
  colib_ref "aglib_principal_euler_pin" "RingTheory/Multiplicity/PrincipalEuler/Additivity.lean"
    "adaptation" "Scalar specialization of the exact-sequence Euler index, with outer finiteness"]
theorem finitePrincipal_and_principalEuler_add_of_exact
    (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (t : A)
    (hU : FinitePrincipal U t) (hW : FinitePrincipal W t) :
    FinitePrincipal V t ∧
      principalEuler (N := V) t = principalEuler (N := U) t + principalEuler (N := W) t := by
  have h := Module.lengthIndex_add_of_ladder f g f g
    (LinearMap.lsmul A U t) (LinearMap.lsmul A V t) (LinearMap.lsmul A W t)
    hf hg hex hf hg hex
    (by ext x; exact f.map_smul t x)
    (by ext x; exact g.map_smul t x)
    (Module.length_ne_top_iff.mp hU.1) (Module.length_ne_top_iff.mp hU.2)
    (Module.length_ne_top_iff.mp hW.1) (Module.length_ne_top_iff.mp hW.2)
  refine ⟨⟨Module.length_ne_top_iff.mpr h.1, Module.length_ne_top_iff.mpr h.2.1⟩, ?_⟩
  simpa only [principalEuler_eq_length_quotient_sub_length_ker] using h.2.2

/-- The middle module inherits finite scalar homology from the two ends of a
short exact sequence. -/
theorem finitePrincipal_of_exact (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (t : A)
    (hU : FinitePrincipal U t) (hW : FinitePrincipal W t) : FinitePrincipal V t :=
  (finitePrincipal_and_principalEuler_add_of_exact f g hf hg hex t hU hW).1

/-- Principal Euler length is additive when the outer scalar homology modules
have finite length; the middle finiteness condition is a consequence. -/
@[colib_tag "COL-0170"]
theorem principalEuler_add_of_exact_of_outer_finite
    (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (t : A)
    (hU : FinitePrincipal U t) (hW : FinitePrincipal W t) :
    principalEuler (N := V) t = principalEuler (N := U) t + principalEuler (N := W) t :=
  (finitePrincipal_and_principalEuler_add_of_exact f g hf hg hex t hU hW).2

/-- The source form of scalar Euler additivity, retaining all three explicit
finite-length hypotheses without any regularity or flatness assumption. -/
theorem principalEuler_add_of_exact (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (t : A)
    (hU : FinitePrincipal U t) (_hV : FinitePrincipal V t) (hW : FinitePrincipal W t) :
    principalEuler (N := V) t = principalEuler (N := U) t + principalEuler (N := W) t :=
  principalEuler_add_of_exact_of_outer_finite f g hf hg hex t hU hW

private theorem map_ker_lsmul (e : U ≃ₗ[A] V) (t : A) :
    (LinearMap.ker (LinearMap.lsmul A U t)).map e.toLinearMap =
      LinearMap.ker (LinearMap.lsmul A V t) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change t • e x = 0
    rw [← e.map_smul, show t • x = 0 from hx, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change t • e.symm y = 0
    rw [← e.symm.map_smul, show t • y = 0 from hy, map_zero]

private theorem map_range_lsmul (e : U ≃ₗ[A] V) (t : A) :
    (LinearMap.range (LinearMap.lsmul A U t)).map e.toLinearMap =
      LinearMap.range (LinearMap.lsmul A V t) := by
  ext y
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact ⟨e u, (e.map_smul t u).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨t • e.symm v, ⟨e.symm v, rfl⟩, ?_⟩
    change e (t • e.symm v) = t • v
    rw [e.map_smul, e.apply_symm_apply]

/-- A coefficient-module linear equivalence preserves the principal Euler integer. -/
@[colib_tag "COL-0170"]
theorem principalEuler_congr (e : U ≃ₗ[A] V) (t : A) :
    principalEuler (N := U) t = principalEuler (N := V) t := by
  have hk := (e.ofSubmodules _ _ (map_ker_lsmul e t)).length_eq
  have hc := (Submodule.Quotient.equiv _ _ e (map_range_lsmul e t)).length_eq
  rw [principalEuler_eq_length_quotient_sub_length_ker,
    principalEuler_eq_length_quotient_sub_length_ker, hk, hc]

/-- A coefficient-module linear equivalence preserves finite scalar homology. -/
@[colib_tag "COL-0170"]
theorem finitePrincipal_congr (e : U ≃ₗ[A] V) (t : A) :
    FinitePrincipal U t ↔ FinitePrincipal V t := by
  have hk := (e.ofSubmodules _ _ (map_ker_lsmul e t)).length_eq
  have hc := (Submodule.Quotient.equiv _ _ e (map_range_lsmul e t)).length_eq
  unfold FinitePrincipal
  rw [hk, hc]

end Module
