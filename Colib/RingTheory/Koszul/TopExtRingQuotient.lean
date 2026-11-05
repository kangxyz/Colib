/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.TopExtClass
public import Colib.Algebra.Homology.DerivedCategory.Ext.Quotient
public import StacksFrontier.RingTheory.Koszul.DualExactness

/-!
# The native top Ext line of a positive-length Koszul-regular quotient

The actual standard top-coordinate class has kernel precisely the generated
ideal. It therefore identifies `R/(f)` with top Ext with ring coefficients,
linearly over that same quotient ring and with its native Ext action.

This is the positive-length canonical-model counterpart of
`ChainComplex.Koszul.topExtClass_ring_ker` and `topExtRingQuotientLinearEquiv`
in `Aglib.Algebra.Homology.Koszul.Ext.Quotient` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`.
The proof directly reuses Stacks' `mem_span_iff_exists_dual_d_eq`; it neither
copies self-duality nor reconstructs the source recursive coinduction model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)] {n : ℕ}
  (f : Fin (n + 1) → R) (hf : IsKoszulRegular f)

/-- The native ring-coefficient top class vanishes exactly on the generated ideal. -/
theorem seqTopExtClass_ring_eq_zero_iff (x : R) :
    seqTopExtClass f hf (ModuleCat.of R R) x = 0 ↔ x ∈ Ideal.span (Set.range f) := by
  let φ : (⋀[R]^(n + 1) (Fin (n + 1) → R)) →ₗ[R] R :=
    (LinearMap.toSpanSingleton R R x).comp (topEquiv R (n + 1)).toLinearMap
  rw [seqTopExtClass_eq_zero_iff f hf (ModuleCat.of R R) n rfl]
  constructor
  · rintro ⟨g, hg⟩
    rw [seqComplex_d] at hg
    have hφ : ∀ z, φ z ∈ Ideal.span (Set.range f) :=
      (mem_span_iff_exists_dual_d_eq f φ).mpr ⟨g.hom, by
        exact congrArg ModuleCat.Hom.hom hg⟩
    simpa [φ] using hφ (topGen R (n + 1))
  · intro hx
    have hφ : ∀ z, φ z ∈ Ideal.span (Set.range f) := by
      intro z
      exact Ideal.mul_mem_left _ _ hx
    obtain ⟨ψ, hψ⟩ := (mem_span_iff_exists_dual_d_eq f φ).mp hφ
    refine ⟨ModuleCat.ofHom ψ, ?_⟩
    rw [seqComplex_d]
    apply ModuleCat.hom_ext
    exact hψ

/-- The kernel of the standard top-coordinate class is exactly the generated ideal. -/
theorem seqTopExtClass_ring_ker :
    LinearMap.ker (seqTopExtClass f hf (ModuleCat.of R R)) = Ideal.span (Set.range f) := by
  ext x
  exact seqTopExtClass_ring_eq_zero_iff f hf x

/-- The actual ring quotient computes the native top Ext line through its standard cocycle. -/
def seqTopExtRingLinearEquiv :
    (R ⧸ Ideal.span (Set.range f)) ≃ₗ[R]
      Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R R) (n + 1) :=
  (Submodule.quotEquivOfEq _ _ (seqTopExtClass_ring_ker f hf).symm).trans
    ((seqTopExtClass f hf (ModuleCat.of R R)).quotKerEquivOfSurjective
      (seqTopExtClass_surjective f hf (ModuleCat.of R R)))

/-- Every quotient representative retains the literal standard top-coordinate class. -/
@[simp]
theorem seqTopExtRingLinearEquiv_apply_mk (x : R) :
    seqTopExtRingLinearEquiv f hf (Ideal.Quotient.mk (Ideal.span (Set.range f)) x) =
      seqTopExtClass f hf (ModuleCat.of R R) x := by
  change seqTopExtRingLinearEquiv f hf (Submodule.Quotient.mk x) = _
  simp only [seqTopExtRingLinearEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The same actual top Ext equivalence is linear for the native quotient-ring action. -/
def seqTopExtRingQuotientLinearEquiv :
    letI := Ext.quotientSourceModule (Ideal.span (Set.range f)) (ModuleCat.of R R) (n + 1)
    (R ⧸ Ideal.span (Set.range f)) ≃ₗ[R ⧸ Ideal.span (Set.range f)]
      Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) (ModuleCat.of R R) (n + 1) := by
  letI := Ext.quotientSourceModule (Ideal.span (Set.range f)) (ModuleCat.of R R) (n + 1)
  refine { __ := (seqTopExtRingLinearEquiv f hf).toAddEquiv, map_smul' := ?_ }
  intro b y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  change seqTopExtRingLinearEquiv f hf
      (Ideal.Quotient.mk (Ideal.span (Set.range f)) (r * x)) =
    Ideal.Quotient.mk (Ideal.span (Set.range f)) r •
      seqTopExtRingLinearEquiv f hf (Ideal.Quotient.mk (Ideal.span (Set.range f)) x)
  rw [seqTopExtRingLinearEquiv_apply_mk, seqTopExtRingLinearEquiv_apply_mk,
    Ext.quotientSourceModule_mk_smul]
  exact (seqTopExtClass f hf (ModuleCat.of R R)).map_smul r x

/-- Quotient-linearity preserves the standard cocycle on representatives. -/
@[simp]
theorem seqTopExtRingQuotientLinearEquiv_apply_mk (x : R) :
    seqTopExtRingQuotientLinearEquiv f hf (Ideal.Quotient.mk (Ideal.span (Set.range f)) x) =
      seqTopExtClass f hf (ModuleCat.of R R) x :=
  seqTopExtRingLinearEquiv_apply_mk f hf x

end Koszul

attribute [colib_tag "COL-0119"] Koszul.seqTopExtClass_ring_eq_zero_iff
  Koszul.seqTopExtClass_ring_ker Koszul.seqTopExtRingLinearEquiv
  Koszul.seqTopExtRingLinearEquiv_apply_mk Koszul.seqTopExtRingQuotientLinearEquiv
  Koszul.seqTopExtRingQuotientLinearEquiv_apply_mk

attribute [stacks 06XP "Ingredient: Yoneda composition; quotient-line computation proved here"]
  Koszul.seqTopExtRingQuotientLinearEquiv
