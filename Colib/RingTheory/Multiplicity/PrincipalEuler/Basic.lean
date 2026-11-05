/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.Algebra.Regular.SMul
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Length

/-!
# Principal Euler length on the native periodic complex

The principal Euler integer is the periodic length of the existing Stacks
complex with differentials zero and scalar multiplication. Its concrete
expression is cokernel length minus kernel length, with each extended-natural
length converted using `ENat.toNat`. Finiteness is a separate hypothesis; the
expression itself is defined for every module.

This rewrites `Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, source SHA-256
`f164baf700c2747343b36363e9b6b173b9f065d5871b9d66c7d13b17bfa21741`.
That source retains the Apache-2.0 implementation credit of
`R5Lab.RingTheory.LocalLength.PrincipalEuler` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. The Motivic reuse is recorded in
Aglib's `docs/migration/motivic-milnor-k.json`.

The complex, homology, module kernel and quotient are native Stacks/Mathlib
objects. No scalar-homology model or comparison of two independently defined
complexes is introduced. Ring and module universes are independent.
-/

@[expose] public noncomputable section

universe u v

namespace Module

variable {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N] [Module A N]

/-- The principal Euler integer, realized by the native periodic complex with
zero differential in degree zero and multiplication by `t` in degree one. -/
@[colib_tag "COL-0169"]
abbrev principalEuler (t : A) : ℤ :=
  AlgebraicGeometry.periodicLength
    (AlgebraicGeometry.twoPeriodicComplex (0 : Module.End A N)
      (LinearMap.lsmul A N t) (zero_mul _) (mul_zero _))

/-- The native periodic length has the source convention: cokernel minus kernel. -/
@[colib_tag "COL-0169", stacks 0EA6 "principal scalar specialization"]
theorem principalEuler_eq_length_quotient_sub_length_ker (t : A) :
    principalEuler (N := N) t =
      ((Module.length A (N ⧸ LinearMap.range (LinearMap.lsmul A N t))).toNat : ℤ) -
        ((Module.length A (LinearMap.ker (LinearMap.lsmul A N t))).toNat : ℤ) :=
  AlgebraicGeometry.periodicLength_zero_eq_length_quotient_sub_length_ker
    (LinearMap.lsmul A N t)

/-- Every scalar has principal Euler integer zero on a finite-length module. -/
@[colib_tag "COL-0169", stacks 0EA8 "equal-term scalar periodic complex"]
theorem principalEuler_zero_of_finite_length (t : A) (hN : Module.length A N ≠ ⊤) :
    principalEuler (N := N) t = 0 :=
  AlgebraicGeometry.periodicLength_eq_zero_of_iso _
    (Module.length_ne_top_iff.mp hN) (CategoryTheory.Iso.refl _)

/-- A regular scalar removes the kernel contribution. This does not assert that
the quotient has finite length. -/
@[colib_tag "COL-0169"]
theorem principalEuler_of_regular (t : A) (ht : IsSMulRegular N t) :
    principalEuler (N := N) t =
      ((Module.length A (N ⧸ LinearMap.range (LinearMap.lsmul A N t))).toNat : ℤ) := by
  let : Subsingleton (LinearMap.ker (LinearMap.lsmul A N t)) :=
    ⟨fun x y => Subtype.ext (ht (x.property.trans y.property.symm))⟩
  have hk : Module.length A (LinearMap.ker (LinearMap.lsmul A N t)) = 0 :=
    Module.length_eq_zero
  rw [principalEuler_eq_length_quotient_sub_length_ker, hk]
  simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero]

/-- Both scalar homology modules have finite length, stated directly on the
native kernel and quotient. This does not require scalar regularity. -/
@[colib_tag "COL-0169"]
def FinitePrincipal (N : Type v) [AddCommGroup N] [Module A N] (t : A) : Prop :=
  Module.length A (LinearMap.ker (LinearMap.lsmul A N t)) ≠ ⊤ ∧
    Module.length A (N ⧸ LinearMap.range (LinearMap.lsmul A N t)) ≠ ⊤

/-- The finite-length predicate is equivalent to finite length of the two
actual scalar homology modules. -/
theorem finitePrincipal_iff_isFiniteLength (t : A) :
    FinitePrincipal N t ↔
      IsFiniteLength A (LinearMap.ker (LinearMap.lsmul A N t)) ∧
        IsFiniteLength A (N ⧸ LinearMap.range (LinearMap.lsmul A N t)) := by
  simp only [FinitePrincipal, Module.length_ne_top_iff]

/-- A regular scalar with finite-length cokernel has finite scalar homology. -/
theorem finitePrincipal_of_regular (N : Type v) [AddCommGroup N] [Module A N]
    (t : A) (hr : IsSMulRegular N t)
    (hc : Module.length A (N ⧸ LinearMap.range (LinearMap.lsmul A N t)) ≠ ⊤) :
    FinitePrincipal N t := by
  let : Subsingleton (LinearMap.ker (LinearMap.lsmul A N t)) :=
    ⟨fun x y => Subtype.ext (hr (x.property.trans y.property.symm))⟩
  refine ⟨?_, hc⟩
  simp only [Module.length_eq_zero, ne_eq, ENat.zero_ne_top, not_false_eq_true]

end Module
