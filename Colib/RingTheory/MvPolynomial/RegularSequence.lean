/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors, kangxyz
-/
module

public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular

/-!
# Distinct variables in an arbitrary polynomial ring

Every finite list of distinct original variables is weakly regular, including the empty
list and the zero coefficient ring. The coordinate type need not be finite, and its universe
is independent of the coefficient universe. Flat coefficient modules inherit the same weak
regularity. Proper regularity is asserted only over a nontrivial coefficient ring.

The two source endpoints are adapted from `Aglib.RingTheory.MvPolynomial.RegularSequence`
at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`, whose SHA-256 is
`bc6338c46a52bf1f08e15474b2d56f7cf95e4bd74cb13d1e43648376d6e39fc1`.
The source attributes its proofs to the Apache-2.0 Motivic archive member
`Motivic/RingTheory/MvPolynomial/RegularSequence.lean`, SHA-256
`e7c2874e7260e03067827da56d70f854b6db9e243971c1e9106786da4d2fb4dc`.

The monomial argument is already in the pinned Stacks library as
`MvPolynomial.mem_span_X_image_of_X_mul_mem`; it is reused rather than reimplemented.
The existing Stacks sequence theorem treats all variables of `Fin (n + 1)`.
The only extension here is an arbitrary distinct list in an arbitrary coordinate type,
with its finite-family and flat-module consequences. No new regularity or Koszul model is used.
-/

@[expose] public section

open RingTheory.Sequence
open scoped TensorProduct

universe u v w

namespace MvPolynomial

variable {R : Type u} [CommRing R] {I : Type v}

/-- A new original variable acts injectively modulo any set of other original variables. -/
theorem isSMulRegular_quotient_span_X (s : Set I) (i : I) (hi : i ∉ s) :
    IsSMulRegular (MvPolynomial I R ⧸ Ideal.span ((X : I → MvPolynomial I R) '' s))
      (X i : MvPolynomial I R) := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro p hp
  exact mem_span_X_image_of_X_mul_mem hi (by simpa only [smul_eq_mul] using hp)

/-- Every finite list of distinct original variables is weakly regular. -/
theorem isWeaklyRegular_X (l : List I) (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial I R) (l.map (X : I → MvPolynomial I R)) := by
  constructor
  intro i hi
  have hi' : i < l.length := by simpa only [List.length_map] using hi
  have hnew : l[i] ∉ {j | j ∈ l.take i} := by
    intro h
    obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp h
    have hji : j = i := hl.getElem_inj.mp he
    omega
  have heq : Ideal.ofList ((l.map (X : I → MvPolynomial I R)).take i) =
      Ideal.span (X '' {j | j ∈ l.take i}) := by
    rw [← List.map_take]
    unfold Ideal.ofList
    congr 1
    ext p
    exact List.mem_map
  rw [heq, Ideal.smul_eq_mul, Ideal.mul_top, List.getElem_map]
  exact isSMulRegular_quotient_span_X _ _ hnew

/-- Distinct original variables form a regular sequence if the coefficient ring is nonzero. -/
theorem isRegular_X_of_nodup [Nontrivial R] (l : List I) (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial I R) (l.map (X : I → MvPolynomial I R)) where
  toIsWeaklyRegular := isWeaklyRegular_X l hl
  top_ne_smul := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have heq : Ideal.ofList (l.map (X : I → MvPolynomial I R)) =
        Ideal.span (X '' {j | j ∈ l}) := by
      unfold Ideal.ofList
      congr 1
      ext p
      exact List.mem_map
    rw [heq]
    exact ((Ideal.ne_top_iff_one _).2 one_notMem_span_X_image).symm

/-- A finite injective family may select any variables, including none. -/
theorem isWeaklyRegular_ofFn_X_of_injective {n : ℕ} (f : Fin n → I)
    (hf : Function.Injective f) :
    IsWeaklyRegular (MvPolynomial I R) (List.ofFn fun i => (X (f i) : MvPolynomial I R)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    (isWeaklyRegular_X (R := R) (List.ofFn f) (List.nodup_ofFn.mpr hf))

/-- Flat coefficient modules inherit regularity of distinct polynomial variables.
No finite generation or nontriviality of the coefficient module is required. -/
theorem isWeaklyRegular_X_on_flat (M : Type w) [AddCommGroup M]
    [Module (MvPolynomial I R) M] [Module.Flat (MvPolynomial I R) M]
    (l : List I) (hl : l.Nodup) :
    IsWeaklyRegular M (l.map (X : I → MvPolynomial I R)) := by
  have h : IsWeaklyRegular (MvPolynomial I R ⊗[MvPolynomial I R] M)
      (l.map (X : I → MvPolynomial I R)) :=
    (isWeaklyRegular_X l hl).isWeaklyRegular_rTensor
  exact ((TensorProduct.lid (MvPolynomial I R) M).isWeaklyRegular_congr _).mp h

/-- Finite injective families of variables are weakly regular on any flat coefficient module. -/
theorem isWeaklyRegular_ofFn_X_on_flat {n : ℕ} (f : Fin n → I)
    (hf : Function.Injective f) (M : Type w) [AddCommGroup M]
    [Module (MvPolynomial I R) M] [Module.Flat (MvPolynomial I R) M] :
    IsWeaklyRegular M (List.ofFn fun i => (X (f i) : MvPolynomial I R)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    (isWeaklyRegular_X_on_flat M (List.ofFn f) (List.nodup_ofFn.mpr hf))

end MvPolynomial
