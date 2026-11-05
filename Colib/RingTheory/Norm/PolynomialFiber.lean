/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Norm.FiniteAlgebra
public import Colib.Util.References
public import Mathlib.Algebra.Polynomial.Degree.Units
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.FreeModule.PID
public import StacksFrontier.RingTheory.Norm.BaseChangeProduct

/-!
# Length-weighted norms in polynomial evaluation fibres

The norm of a global unit of a finite free algebra over `k[X]` is a constant unit
polynomial. Its norms in any two evaluation fibres agree, as do the products of
all residue-field norms weighted by the actual local lengths.

Each fibre is the literal tensor product `k ⊗[k[X]] B`, with the polynomial action
on `k` specified by `Polynomial.evalRingHom`. There is no separate fibre type or
specialization map: the specialized element is the native pure tensor `1 ⊗ x`.
The intrinsic products need no chosen enumeration of the maximal spectrum.

This includes nonreduced fibres and inseparable residue extensions. The result is
algebraic: it does not identify a fibre fundamental cycle with a correspondence
pullback or prove a statement about a motivic sheaf.

## Source provenance

This adapts `Aglib/RingTheory/PolynomialFiberNorm.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`bb00fca90033628db4475e0030ec0d6e2a43cde6a4c074318f1b0ea37decfa13`.
Its original source is `Motivic.Aglib.RingTheory.PolynomialFiberNorm`, recorded in
`docs/migration/motivic-milnor-k.json`. Native norm base change comes directly from
`Stacks.Norm.norm_tmul_one`, at Stacks revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.

-/

@[expose] public noncomputable section

open scoped BigOperators TensorProduct
open Polynomial

namespace Algebra.PolynomialFiber

universe u v

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [Algebra k[X] B]

/-- Norm in the literal evaluation fibre is evaluation of the polynomial-valued norm. -/
@[colib_tag "COL-0184",
  colib_ref "aglib_principal_euler_pin" "RingTheory/PolynomialFiberNorm.lean"
    "adaptation" "Literal polynomial evaluation fibres and length-weighted unit norms"]
theorem norm_one_tmul [Module.Free k[X] B] [Module.Finite k[X] B] (a : k) (x : B) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     Algebra.norm k (1 ⊗ₜ[k[X]] x : k ⊗[k[X]] B)) =
      (Algebra.norm k[X] x).eval a := by
  let := (Polynomial.evalRingHom a).toAlgebra
  exact Stacks.Norm.norm_tmul_one (R := k[X]) (A := k) x

/-- The determinant norm of a unit is a constant unit polynomial. -/
theorem norm_unit_eq_C (u : Bˣ) :
    ∃ c : kˣ, Algebra.norm k[X] (u : B) = Polynomial.C (c : k) := by
  obtain ⟨c, hc, h⟩ := Polynomial.isUnit_iff.mp (u.isUnit.map (Algebra.norm k[X]))
  obtain ⟨c, rfl⟩ := hc
  exact ⟨c, h.symm⟩

/-- A global unit has the same norm in any two actual evaluation fibres. -/
@[colib_tag "COL-0184"]
theorem norm_one_tmul_eq [Module.Free k[X] B] [Module.Finite k[X] B]
    (u : Bˣ) (a b : k) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     Algebra.norm k (1 ⊗ₜ[k[X]] (u : B) : k ⊗[k[X]] B)) =
    (letI := (Polynomial.evalRingHom b).toAlgebra
     Algebra.norm k (1 ⊗ₜ[k[X]] (u : B) : k ⊗[k[X]] B)) := by
  obtain ⟨c, hc⟩ := norm_unit_eq_C (k := k) u
  calc
    _ = (Algebra.norm k[X] (u : B)).eval a := norm_one_tmul a (u : B)
    _ = (Algebra.norm k[X] (u : B)).eval b := by simp only [hc, Polynomial.eval_C]
    _ = _ := (norm_one_tmul b (u : B)).symm

/-- Finite torsion-free algebras over the polynomial PID satisfy the same equality. -/
@[colib_tag "COL-0184"]
theorem norm_one_tmul_eq_of_torsionFree [Module.Finite k[X] B]
    [Module.IsTorsionFree k[X] B] (u : Bˣ) (a b : k) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     Algebra.norm k (1 ⊗ₜ[k[X]] (u : B) : k ⊗[k[X]] B)) =
    (letI := (Polynomial.evalRingHom b).toAlgebra
     Algebra.norm k (1 ⊗ₜ[k[X]] (u : B) : k ⊗[k[X]] B)) := by
  let : Module.Free k[X] B := Module.free_of_finite_type_torsion_free'
  exact norm_one_tmul_eq u a b

/-- Norm equality holds in the actual unit group of the base field. -/
@[colib_tag "COL-0184"]
theorem normUnits_one_tmul_eq [Module.Free k[X] B] [Module.Finite k[X] B]
    (u : Bˣ) (a b : k) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     Units.map (Algebra.norm k)
       (Units.map (Algebra.TensorProduct.includeRight :
         B →ₐ[k[X]] k ⊗[k[X]] B).toMonoidHom u)) =
    (letI := (Polynomial.evalRingHom b).toAlgebra
     Units.map (Algebra.norm k)
       (Units.map (Algebra.TensorProduct.includeRight :
         B →ₐ[k[X]] k ⊗[k[X]] B).toMonoidHom u)) := by
  apply Units.ext
  exact norm_one_tmul_eq u a b

/-- The norm in one fibre is the product of all residue norms with local multiplicities.
Only finiteness of the polynomial algebra is needed for this single-fibre formula. -/
@[colib_tag "COL-0184"]
theorem norm_one_tmul_eq_finprod [Module.Finite k[X] B] (a : k) (x : B) :
    letI := (Polynomial.evalRingHom a).toAlgebra
    Algebra.norm k (1 ⊗ₜ[k[X]] x : k ⊗[k[X]] B) =
      ∏ᶠ q : MaximalSpectrum (k ⊗[k[X]] B),
        Algebra.norm k (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k[X]] x)) ^
          (Module.length (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal)).toNat := by
  let := (Polynomial.evalRingHom a).toAlgebra
  exact Algebra.norm_eq_finprod_quotient_norm_pow_local_length (k := k) _

/-- Length-weighted residue-norm products agree in any two fibres of a global unit.
No reducedness, separability, etaleness or enumeration assumption is used. -/
@[colib_tag "COL-0184"]
theorem finprod_residue_norm_eq [Module.Free k[X] B] [Module.Finite k[X] B]
    (u : Bˣ) (a b : k) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     ∏ᶠ q : MaximalSpectrum (k ⊗[k[X]] B),
       Algebra.norm k (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k[X]] (u : B))) ^
         (Module.length (Localization.AtPrime q.asIdeal)
           (Localization.AtPrime q.asIdeal)).toNat) =
    (letI := (Polynomial.evalRingHom b).toAlgebra
     ∏ᶠ q : MaximalSpectrum (k ⊗[k[X]] B),
       Algebra.norm k (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k[X]] (u : B))) ^
         (Module.length (Localization.AtPrime q.asIdeal)
           (Localization.AtPrime q.asIdeal)).toNat) :=
  (norm_one_tmul_eq_finprod a (u : B)).symm.trans
    ((norm_one_tmul_eq u a b).trans (norm_one_tmul_eq_finprod b (u : B)))

/-- The weighted-product equality also follows from finite torsion-freeness over `k[X]`. -/
@[colib_tag "COL-0184"]
theorem finprod_residue_norm_eq_of_torsionFree [Module.Finite k[X] B]
    [Module.IsTorsionFree k[X] B] (u : Bˣ) (a b : k) :
    (letI := (Polynomial.evalRingHom a).toAlgebra
     ∏ᶠ q : MaximalSpectrum (k ⊗[k[X]] B),
       Algebra.norm k (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k[X]] (u : B))) ^
         (Module.length (Localization.AtPrime q.asIdeal)
           (Localization.AtPrime q.asIdeal)).toNat) =
    (letI := (Polynomial.evalRingHom b).toAlgebra
     ∏ᶠ q : MaximalSpectrum (k ⊗[k[X]] B),
       Algebra.norm k (Ideal.Quotient.mk q.asIdeal (1 ⊗ₜ[k[X]] (u : B))) ^
         (Module.length (Localization.AtPrime q.asIdeal)
           (Localization.AtPrime q.asIdeal)).toNat) := by
  let : Module.Free k[X] B := Module.free_of_finite_type_torsion_free'
  exact finprod_residue_norm_eq u a b

end Algebra.PolynomialFiber
