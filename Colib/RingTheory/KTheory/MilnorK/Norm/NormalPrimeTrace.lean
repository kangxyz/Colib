/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeChosenPresentation
public import Colib.RingTheory.KTheory.MilnorK.Norm.SplitBaseChange
public import Mathlib.FieldTheory.Fixed

/-!
# Restriction of the chosen norm in normal separable prime degree

The restriction of the native chosen norm is the sum of the actual Galois
automorphism maps. The proof uses the selected minpoly presentation of that norm,
the split simple-norm formula, and native equivalences of algebra homomorphisms.

Only separability of the extension is needed, not perfectness of the base field.
All fields share the universe required by the native chosen norm. The quotient
uses `Ideal.Quotient.field`; no replacement norm, quotient field structure,
comparison object, arbitrary-presentation invariance, or tower law is assumed.

-/

@[expose] public noncomputable section

open Polynomial Module
open scoped BigOperators

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [Normal k L] [Algebra.IsSeparable k L]

/-- Restricting the native chosen norm of a normal separable prime-degree
extension is the sum over its actual base-algebra endomorphisms. -/
theorem milnorKNormRing_map_eq_sum_algHom_of_normal_prime
    (hp : Nat.Prime (finrank k L)) (x : MilnorKRing L) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
      ∑ σ : L →ₐ[k] L, milnorKRingMap σ.toRingHom x := by
  classical
  obtain ⟨a, _ha, e, _hdegree, hchosen⟩ :=
    exists_selected_simpleMilnorNorm_presentation_of_prime hp
  let p : MonicIrreducibleOfDegree k (minpoly k a).natDegree :=
    minpolyOfDegree k (Algebra.IsIntegral.isIntegral (R := k) a)
  let : Fintype ((k[X] ⧸ Ideal.span {poly p}) →ₐ[k] L) :=
    PowerBasis.AlgHom.fintype (B := L) (AdjoinRoot.powerBasis' (monic p))
  have hsep : (poly p).Separable := by
    change (minpoly k a).Separable
    exact Algebra.IsSeparable.isSeparable k a
  have hsplit : ((poly p).map (algebraMap k L)).Splits := by
    change ((minpoly k a).map (algebraMap k L)).Splits
    exact Normal.splits (inferInstance : Normal k L) a
  calc
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
        milnorKRingMap (algebraMap k L)
          (simpleMilnorNorm p (milnorKRingMap e.toRingHom x)) :=
      congrArg (milnorKRingMap (algebraMap k L)) (hchosen x)
    _ = ∑ σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] L,
        milnorKRingMap σ.toRingHom (milnorKRingMap e.toRingHom x) :=
      simpleMilnorNorm_map_eq_sum_algHom p hsep hsplit
        (milnorKRingMap e.toRingHom x)
    _ = ∑ σ : L →ₐ[k] L, milnorKRingMap σ.toRingHom x := by
      refine Fintype.sum_equiv
        (AlgEquiv.arrowCongr e.symm (AlgEquiv.refl : L ≃ₐ[k] L)) _ _ ?_
      intro σ
      simp only [AlgEquiv.arrowCongr_apply, AlgEquiv.symm_symm,
        AlgEquiv.refl_toAlgHom, AlgHom.id_comp]
      exact milnorKRingMap_comp_apply e.toRingHom σ.toRingHom x

/-- Restriction of the actual chosen norm is the Galois trace in normal
separable prime degree. Finiteness of the automorphism type is supplied by the
native finite-dimensional algebra-equivalence instance. -/
theorem milnorKNormRing_map_eq_sum_gal_of_normal_prime
    (hp : Nat.Prime (finrank k L)) (x : MilnorKRing L) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
      ∑ σ : Gal(L/k), milnorKRingMap σ.toRingHom x := by
  classical
  rw [milnorKNormRing_map_eq_sum_algHom_of_normal_prime hp x]
  symm
  exact Fintype.sum_equiv (algEquivEquivAlgHom k L).toEquiv _ _ (fun _ => rfl)

/-- The chosen-norm restriction formula in every homogeneous degree, including
degree zero, with the existing homogeneous field maps. -/
theorem milnorKNorm_map_eq_sum_gal_of_normal_prime
    (hp : Nat.Prime (finrank k L)) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTheoryMap (algebraMap k L) n (milnorKNorm k L n x) =
      ∑ σ : Gal(L/k), milnorKTheoryMap σ.toRingHom n x := by
  classical
  simp only [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  change milnorKRingMap (algebraMap k L) (milnorKNormRing k L (x : MilnorKRing L)) =
    (milnorKGrading L n).subtype (∑ σ : Gal(L/k), milnorKTransport σ.toRingHom n x)
  rw [map_sum]
  exact milnorKNormRing_map_eq_sum_gal_of_normal_prime hp (x : MilnorKRing L)

end Stacks.Chow

end
