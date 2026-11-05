/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Fraction-field base change of a finite product of domains

An actual integral decomposition `A ⊗[R] S ≃ₐ[A] ∀ i, D i` induces an actual decomposition
`B ⊗[F] E ≃ₐ[B] ∀ i, C i`, where `F`, `E`, `B`, and `C i` are the specified fraction fields
of `R`, `S`, `A`, and `D i`. The input algebras `S/R` and `D i/A` need only be algebraic and
faithful, rather than finite. In particular, the construction applies to finite faithful
algebras and to finite torsion-free domain extensions.

The construction uses the native fraction-field pushout, tensor-product base-change
cancellation, the given integral equivalence, and the native finite-product equivalence.
There is no choice of a uniformizer, auxiliary localization model, or replacement field.
The generator and quotient formulas retain the coordinates of the given equivalence.
All ring, field, factor, and index universes are independent.

Implementation provenance: this generalizes the rationalization in
`Aglib/RingTheory/AdicCompletion/FractionBranches.lean` and
`Aglib/RingTheory/AdicCompletion/FractionTensorBranches.lean`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, replacing their localization-away construction
with the native algebraic fraction-field pushout.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- Algebra homomorphisms out of a tensor product with a fraction ring are determined by
integral right-factor generators. No scalar action of `S` on the target is required. -/
theorem algHom_ext_of_isFractionRing
    {F B E Q : Type*} (S : Type*)
    [CommSemiring F] [CommSemiring B] [CommRing S] [CommRing E] [Semiring Q]
    [Algebra F B] [Algebra F E] [Algebra S E] [IsFractionRing S E] [Algebra B Q]
    {f g : B ⊗[F] E →ₐ[B] Q}
    (h : ∀ s : S, f (1 ⊗ₜ[F] algebraMap S E s) = g (1 ⊗ₜ[F] algebraMap S E s)) :
    f = g := by
  apply AlgHom.coe_ringHom_injective
  apply Algebra.TensorProduct.ringHom_ext
  · apply RingHom.ext
    intro b
    change f (algebraMap B (B ⊗[F] E) b) = g (algebraMap B (B ⊗[F] E) b)
    rw [f.commutes, g.commutes]
  · apply IsLocalization.ringHom_ext (nonZeroDivisors S)
    apply RingHom.ext
    intro s
    exact h s

universe uR uS uA uF uE uB uι uD uC

variable (R : Type uR) (S : Type uS) (A : Type uA)
  (F : Type uF) (E : Type uE) (B : Type uB)
  [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
  [FaithfulSMul R S] [Algebra.IsAlgebraic R S]
  [CommRing A] [Algebra R A]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsFractionRing S E]
  [IsScalarTower R S E] [Algebra F E] [IsScalarTower R F E]
  [Field B] [Algebra A B] [IsFractionRing A B]
  [Algebra R B] [IsScalarTower R A B]
  [Algebra F B] [IsScalarTower R F B]
  {ι : Type uι} [Finite ι] (D : ι → Type uD) (C : ι → Type uC)
  [∀ i, CommRing (D i)] [∀ i, IsDomain (D i)] [∀ i, Algebra A (D i)]
  [∀ i, FaithfulSMul A (D i)] [∀ i, Algebra.IsAlgebraic A (D i)]
  [∀ i, Field (C i)] [∀ i, Algebra (D i) (C i)] [∀ i, IsFractionRing (D i) (C i)]
  [∀ i, Algebra A (C i)] [∀ i, IsScalarTower A (D i) (C i)]
  [∀ i, Algebra B (C i)] [∀ i, IsScalarTower A B (C i)]

/-- Rationalizing a given finite product decomposition, in the specified fraction fields.
The action of `B` on every factor is the specified compatible fraction-field action. -/
@[colib_tag "COL-0190",
  colib_ref "aglib_principal_euler_pin" "RingTheory/AdicCompletion/FractionTensorBranches.lean"
    "adaptation" "Algebraic faithful finite-product rationalization by native fraction pushouts"]
def fractionPiEquiv (e : A ⊗[R] S ≃ₐ[A] ∀ i, D i) :
    B ⊗[F] E ≃ₐ[B] ∀ i, C i := by
  classical
  let := Fintype.ofFinite ι
  exact
    (congr (AlgEquiv.refl : B ≃ₐ[B] B) (Algebra.IsPushout.equiv R F S E).symm).trans
      ((cancelBaseChange R F B B S).trans
        ((cancelBaseChange R A B B S).symm.trans
          ((congr (AlgEquiv.refl : B ≃ₐ[B] B) e).trans
            ((piRight A B B D).trans
              (AlgEquiv.piCongrRight fun i ↦ Algebra.IsPushout.equiv A B (D i) (C i))))))

/-- The rationalized equivalence retains the actual integral coordinate maps. -/
@[simp]
theorem fractionPiEquiv_tmul_algebraMap
    (e : A ⊗[R] S ≃ₐ[A] ∀ i, D i) (b : B) (s : S) (i : ι) :
    fractionPiEquiv R S A F E B D C e (b ⊗ₜ[F] algebraMap S E s) i =
      algebraMap B (C i) b * algebraMap (D i) (C i) (e (1 ⊗ₜ[R] s) i) := by
  classical
  simp [fractionPiEquiv, Algebra.IsPushout.equiv_symm_algebraMap_right,
    Algebra.IsPushout.equiv_tmul]

/-- Original integral elements enter the product through the given integral decomposition. -/
theorem fractionPiEquiv_one_tmul_algebraMap
    (e : A ⊗[R] S ≃ₐ[A] ∀ i, D i) (s : S) (i : ι) :
    fractionPiEquiv R S A F E B D C e (1 ⊗ₜ[F] algebraMap S E s) i =
      algebraMap (D i) (C i) (e (1 ⊗ₜ[R] s) i) := by
  simp

/-- A pure tensor carries its left coefficient by the specified fraction-field action. -/
theorem fractionPiEquiv_tmul
    (e : A ⊗[R] S ≃ₐ[A] ∀ i, D i) (b : B) (x : E) (i : ι) :
    fractionPiEquiv R S A F E B D C e (b ⊗ₜ[F] x) i =
      algebraMap B (C i) b * fractionPiEquiv R S A F E B D C e (1 ⊗ₜ[F] x) i := by
  have h : b ⊗ₜ[F] x =
      algebraMap B (B ⊗[F] E) b * (1 ⊗ₜ[F] x) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [h, map_mul, (fractionPiEquiv R S A F E B D C e).commutes]
  rfl

/-- Every fraction has the quotient of its actual integral coordinates. The formula also
holds for a zero denominator, using the field's totalized division. -/
theorem fractionPiEquiv_one_tmul_div
    (e : A ⊗[R] S ≃ₐ[A] ∀ i, D i) (s t : S) (i : ι) :
    fractionPiEquiv R S A F E B D C e
        (1 ⊗ₜ[F] (algebraMap S E s / algebraMap S E t)) i =
      algebraMap (D i) (C i) (e (1 ⊗ₜ[R] s) i) /
        algebraMap (D i) (C i) (e (1 ⊗ₜ[R] t) i) := by
  let f : E →+* C i :=
    (Pi.evalRingHom C i).comp
      ((fractionPiEquiv R S A F E B D C e).toRingHom.comp
        (includeRight : E →ₐ[F] B ⊗[F] E).toRingHom)
  have hf (a : S) : f (algebraMap S E a) =
      algebraMap (D i) (C i) (e (1 ⊗ₜ[R] a) i) :=
    fractionPiEquiv_one_tmul_algebraMap R S A F E B D C e a i
  change f (algebraMap S E s / algebraMap S E t) = _
  rw [map_div₀, hf, hf]

/-- The complete coordinate formula on pure tensors of fractions. -/
theorem fractionPiEquiv_tmul_div
    (e : A ⊗[R] S ≃ₐ[A] ∀ i, D i) (b : B) (s t : S) (i : ι) :
    fractionPiEquiv R S A F E B D C e
        (b ⊗ₜ[F] (algebraMap S E s / algebraMap S E t)) i =
      algebraMap B (C i) b *
        (algebraMap (D i) (C i) (e (1 ⊗ₜ[R] s) i) /
          algebraMap (D i) (C i) (e (1 ⊗ₜ[R] t) i)) := by
  rw [fractionPiEquiv_tmul, fractionPiEquiv_one_tmul_div]

/-- Agreement on the original integral right-factor generators characterizes the entire
rationalized map, not just its restriction to integral tensors. -/
@[colib_tag "COL-0190"]
theorem fractionPiEquiv_unique
    (e : A ⊗[R] S ≃ₐ[A] ∀ i, D i)
    (f : B ⊗[F] E →ₐ[B] ∀ i, C i)
    (h : ∀ (s : S) (i : ι), f (1 ⊗ₜ[F] algebraMap S E s) i =
      algebraMap (D i) (C i) (e (1 ⊗ₜ[R] s) i)) :
    f = (fractionPiEquiv R S A F E B D C e).toAlgHom := by
  apply algHom_ext_of_isFractionRing S
  intro s
  funext i
  exact (h s i).trans (fractionPiEquiv_one_tmul_algebraMap R S A F E B D C e s i).symm

end Algebra.TensorProduct
