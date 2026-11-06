/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Norm.PrimeChosenPresentation
public import Colib.KTheory.MilnorK.Norm.NormalPrimePresentation

/-!
# The chosen norm in an arbitrary normal prime-degree presentation

Over a perfect base, the native chosen norm of a normal prime-degree extension
equals the native simple norm in every actual polynomial presentation. The proof
uses the selected presentation of the chosen norm and the existing independence
of normal prime-degree polynomial presentations. The degrees and the normality
of the selected quotient are transported through the actual algebra equivalence.

The resulting naturality is for an actual algebra equivalence over the fixed
base. All fields share one universe. Only the native `Ideal.Quotient.field` is
used on polynomial quotients. No norm, carrier, comparison structure, general
tower law, or assumed norm-invariance statement is introduced.

-/

@[expose] public noncomputable section

open Polynomial Module

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k]

private theorem simpleMilnorNorm_eq_map_algEquiv_of_normal_prime_of_degree_eq
    [PerfectField k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (q : MonicIrreducibleOfDegree k e)
    (hp : d.Prime) (hde : d = e)
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    simpleMilnorNorm p x = simpleMilnorNorm q (milnorKRingMap f.toRingHom x) := by
  subst e
  exact simpleMilnorNorm_eq_map_algEquiv_of_normal_prime p q hp f x

section Presentation

variable {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L]
  [PerfectField k] [Normal k L]

/-- The native chosen norm agrees with the simple norm in an arbitrary actual
polynomial presentation of a normal prime-degree extension over a perfect base.
The polynomial degree is not an extra hypothesis: it follows from `f`. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime
    (hp : Nat.Prime (finrank k L)) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p})) (x : MilnorKRing L) :
    milnorKNormRing k L x = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) := by
  classical
  obtain ⟨a, _ha, e, hdegree, hchosen⟩ :=
    exists_selected_simpleMilnorNorm_presentation_of_prime hp
  let p₀ : MonicIrreducibleOfDegree k (minpoly k a).natDegree :=
    minpolyOfDegree k (Algebra.IsIntegral.isIntegral (R := k) a)
  let : Normal k (k[X] ⧸ Ideal.span {poly p₀}) := Normal.of_algEquiv e
  have hdim : finrank k L = d := by
    calc
      finrank k L = finrank k (k[X] ⧸ Ideal.span {poly p}) :=
        f.toLinearEquiv.finrank_eq
      _ = (poly p).natDegree := finrank_quotient_span_eq_natDegree
      _ = d := natDegree_eq p
  have hp₀ : Nat.Prime (minpoly k a).natDegree := by
    rw [hdegree]
    exact hp
  have hdegrees : (minpoly k a).natDegree = d := hdegree.trans hdim
  let g : (k[X] ⧸ Ideal.span {poly p₀}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p}) :=
    e.symm.trans f
  have hcomp : g.toRingHom.comp e.toRingHom = f.toRingHom := by
    apply RingHom.ext
    intro z
    change f (e.symm (e z)) = f z
    rw [e.symm_apply_apply]
  calc
    milnorKNormRing k L x = simpleMilnorNorm p₀ (milnorKRingMap e.toRingHom x) :=
      hchosen x
    _ = simpleMilnorNorm p
        (milnorKRingMap g.toRingHom (milnorKRingMap e.toRingHom x)) :=
      simpleMilnorNorm_eq_map_algEquiv_of_normal_prime_of_degree_eq
        p₀ p hp₀ hdegrees g (milnorKRingMap e.toRingHom x)
    _ = simpleMilnorNorm p (milnorKRingMap f.toRingHom x) := by
      rw [milnorKRingMap_comp_apply, hcomp]

/-- Arbitrary-presentation comparison as equality of the existing additive maps. -/
theorem milnorKNormRing_eq_comp_simpleMilnorNorm_of_algEquiv_of_normal_prime
    (hp : Nat.Prime (finrank k L)) {d : ℕ}
    (p : MonicIrreducibleOfDegree k d)
    (f : L ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p})) :
    milnorKNormRing k L =
      (simpleMilnorNorm p).comp (milnorKRingMap f.toRingHom).toAddMonoidHom := by
  ext x
  exact milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime hp p f x

end Presentation

/-- On the native polynomial quotient, the chosen and simple norms agree in
normal prime degree over a perfect base. The finite-dimensional instance can be
supplied by `(AdjoinRoot.powerBasis' (monic p)).finite`. -/
theorem milnorKNormRing_eq_simpleMilnorNorm_of_normal_prime
    [PerfectField k] {d : ℕ} (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
    [FiniteDimensional k (k[X] ⧸ Ideal.span {poly p})]
    [Normal k (k[X] ⧸ Ideal.span {poly p})]
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x = simpleMilnorNorm p x := by
  have hprime : Nat.Prime (finrank k (k[X] ⧸ Ideal.span {poly p})) := by
    rw [finrank_quotient_span_eq_natDegree, natDegree_eq p]
    exact hp
  have h := milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime
    hprime p (AlgEquiv.refl : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k]
      (k[X] ⧸ Ideal.span {poly p})) x
  change milnorKNormRing k (k[X] ⧸ Ideal.span {poly p}) x =
    simpleMilnorNorm p (milnorKRingMap (RingHom.id _) x) at h
  simpa only [milnorKRingMap_id_apply] using h

section Equivariance

variable {L M : Type u} [Field L] [Field M] [Algebra k L] [Algebra k M]
  [FiniteDimensional k L] [FiniteDimensional k M] [PerfectField k] [Normal k L]

/-- The native chosen norm is unchanged by an actual base-algebra equivalence
between finite extensions when the source has normal prime degree. Normality of
the target and equality of degrees are proved from the equivalence. -/
theorem milnorKNormRing_map_algEquiv_of_normal_prime
    (hp : Nat.Prime (finrank k L)) (f : L ≃ₐ[k] M) (x : MilnorKRing L) :
    milnorKNormRing k M (milnorKRingMap f.toRingHom x) = milnorKNormRing k L x := by
  classical
  let : Normal k M := Normal.of_algEquiv f
  have hpM : Nat.Prime (finrank k M) := by
    rw [← f.toLinearEquiv.finrank_eq]
    exact hp
  obtain ⟨a, _ha, e, _hdegree, hchosen⟩ :=
    exists_selected_simpleMilnorNorm_presentation_of_prime hp
  let p : MonicIrreducibleOfDegree k (minpoly k a).natDegree :=
    minpolyOfDegree k (Algebra.IsIntegral.isIntegral (R := k) a)
  let g : M ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p}) := f.symm.trans e
  have hcomp : g.toRingHom.comp f.toRingHom = e.toRingHom := by
    apply RingHom.ext
    intro z
    change e (f.symm (f z)) = e z
    rw [f.symm_apply_apply]
  calc
    milnorKNormRing k M (milnorKRingMap f.toRingHom x) =
        simpleMilnorNorm p
          (milnorKRingMap g.toRingHom (milnorKRingMap f.toRingHom x)) :=
      milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime
        hpM p g (milnorKRingMap f.toRingHom x)
    _ = simpleMilnorNorm p (milnorKRingMap e.toRingHom x) := by
      rw [milnorKRingMap_comp_apply, hcomp]
    _ = milnorKNormRing k L x := (hchosen x).symm

/-- Actual algebra-equivalence naturality as equality of the native additive maps. -/
theorem milnorKNormRing_comp_map_algEquiv_of_normal_prime
    (hp : Nat.Prime (finrank k L)) (f : L ≃ₐ[k] M) :
    (milnorKNormRing k M).comp (milnorKRingMap f.toRingHom).toAddMonoidHom =
      milnorKNormRing k L := by
  ext x
  exact milnorKNormRing_map_algEquiv_of_normal_prime hp f x

/-- Actual algebra-equivalence naturality holds in every homogeneous degree,
including degree zero, for the native chosen norm and existing homogeneous map. -/
theorem milnorKNorm_map_algEquiv_of_normal_prime
    (hp : Nat.Prime (finrank k L)) (f : L ≃ₐ[k] M)
    (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm k M n (milnorKTheoryMap f.toRingHom n x) = milnorKNorm k L n x := by
  rw [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKNormRing_map_algEquiv_of_normal_prime hp f (x : MilnorKRing L)

end Equivariance

end Stacks.Chow

end
