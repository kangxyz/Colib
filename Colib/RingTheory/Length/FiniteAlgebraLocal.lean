/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Length.FiniteAlgebraFiber
public import Colib.Util.References
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.WithTop
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Length over a local ring of a module over a finite algebra

For a finite algebra `S` over a local ring `R` and an `S`-module `M` of finite length,
its `R`-length is the sum of its lengths at all maximal ideals of `S`, weighted by the
corresponding residue degrees. The sum is in extended naturals. In particular, its
`R`-length is finite. Neither ring is required to be Noetherian, and `S` need not be
local, reduced or Artinian. Ring and module universes are independent.

The formula directly specializes the native Stacks semilocal decomposition. Its local
finiteness hypotheses are derived from that same decomposition and Mathlib's length
monotonicity; no prime-filtration model is recreated. The tensor presentation uses
`LocalizedModule.equivTensorProduct` and is not a second localization construction.

## Source provenance

This preserves the endpoint scope of
`Aglib/RingTheory/FiniteLength/FiniteAlgebraLength.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`f0b180d641ffe8500c461ab435479748e3b4e9aa5007960101ebafc1d8bc363d`.
The source is `Motivic.RingTheory.LocalLength.FiniteAlgebraLength`, recorded in Aglib's
`docs/migration/motivic-milnor-k.json`. Its Noetherian base hypothesis is not used by the
native decomposition proof and is omitted here. Source helper APIs for the custom
`PrimeFiltrationFrom` model are replaced, not copied.

Native Stacks revision: `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.
References: Stacks 02M0 (length over a semilocal finite algebra).
-/

@[expose] public noncomputable section

open scoped BigOperators TensorProduct

namespace Module

universe u v w

section LocalFiniteness

variable {S : Type v} [CommRing S] {M : Type w} [AddCommGroup M] [Module S M]

/-- In the semilocal situation, the native decomposition makes each local factor a
finite-length module. The estimate uses only Mathlib's restriction-of-scalars inequality. -/
private theorem localized_length_ne_top_of_finite_maximalSpectrum
    [Finite (MaximalSpectrum S)] (hM : Module.length S M ≠ ⊤) (q : MaximalSpectrum S) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) ≠ ⊤ := by
  classical
  let : IsArtinian S M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hM)).2
  obtain ⟨e⟩ := Stacks.Length.nonempty_linearEquiv_pi_localizedModule (B := S) M
  have hlocal : Module.length S (LocalizedModule q.asIdeal.primeCompl M) ≤ Module.length S M :=
    Module.length_le_of_surjective ((LinearMap.proj q).comp e.toLinearMap)
      ((LinearMap.proj_surjective (R := S) q).comp e.surjective)
  have hrestrict :
      Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M) ≤
        Module.length S (LocalizedModule q.asIdeal.primeCompl M) := by
    have htop := ((Submodule.topEquiv :
      (⊤ : Submodule (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M)) ≃ₗ[Localization.AtPrime q.asIdeal]
          LocalizedModule q.asIdeal.primeCompl M).restrictScalars S).length_eq
    have h := Submodule.length_le_length_restrictScalars S
      (⊤ : Submodule (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M))
    exact (Module.length_top (R := Localization.AtPrime q.asIdeal)).symm.le.trans
      (h.trans htop.le)
  exact ne_top_of_le_ne_top hM (hrestrict.trans hlocal)

end LocalFiniteness

variable (R : Type u) (S : Type v) [CommRing R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [Module.Finite R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

include R in
/-- Every maximal localization of a finite-length module over a finite algebra has
finite length. No separate support, Noetherianity or finiteness hypothesis is required. -/
theorem finiteAlgebra_localized_length_ne_top (hM : Module.length S M ≠ ⊤)
    (q : MaximalSpectrum S) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) ≠ ⊤ := by
  let : Finite (MaximalSpectrum S) := finiteAlgebra_maximalSpectrum_finite R S
  exact localized_length_ne_top_of_finite_maximalSpectrum hM q

variable [Module R M] [IsScalarTower R S M]

/-- The finite-algebra specialization of Stacks 02M0, over all maximal points.
The native localized modules and the literal quotient residue degrees are used. -/
@[colib_tag "COL-0181", stacks 02M0 "finite-algebra specialization with independent universes"]
theorem finiteAlgebra_length_eq_sum [Fintype (MaximalSpectrum S)]
    (hM : Module.length S M ≠ ⊤) :
    Module.length R M = ∑ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) * (finiteAlgebraResidueDegree R S q : ℕ∞) := by
  let : IsArtinian S M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hM)).2
  let : ∀ q : MaximalSpectrum S,
      IsLocalHom (algebraMap R (Localization.AtPrime q.asIdeal)) :=
    fun q => Stacks.Length.isLocalHom_algebraMap_localization (A := R) q
  calc
    _ = ∑ q : MaximalSpectrum S,
        (Module.finrank (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℕ∞) *
            Module.length (Localization.AtPrime q.asIdeal)
              (LocalizedModule q.asIdeal.primeCompl M) :=
      Stacks.Length.length_eq_sum_finrank_mul_length_localizedModule (A := R) (B := S) M
        (fun q => finiteAlgebra_localized_length_ne_top R S hM q)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [finiteAlgebra_residueDegree_eq_localized R S q]
      exact mul_comm _ _

/-- The intrinsic all-point sum, without a supplied enumeration of the maximal spectrum. -/
@[colib_tag "COL-0181"]
theorem finiteAlgebra_length_eq_finsum (hM : Module.length S M ≠ ⊤) :
    Module.length R M = ∑ᶠ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) * (finiteAlgebraResidueDegree R S q : ℕ∞) := by
  classical
  let : Finite (MaximalSpectrum S) := finiteAlgebra_maximalSpectrum_finite R S
  let : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  exact finiteAlgebra_length_eq_sum R S hM

/-- The source tensor-localization presentation of the same intrinsic formula. -/
@[colib_tag "COL-0181"]
theorem finiteAlgebra_length_eq_finsum_tensor (hM : Module.length S M ≠ ⊤) :
    Module.length R M = ∑ᶠ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[S] M) * (finiteAlgebraResidueDegree R S q : ℕ∞) := by
  rw [finiteAlgebra_length_eq_finsum R S hM]
  apply finsum_congr
  intro q
  rw [(LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M).length_eq]

/-- The literal enumerated tensor formula of the source, now without Noetherianity. -/
@[colib_tag "COL-0181"]
theorem finiteAlgebra_length_eq_sum_tensor [Fintype (MaximalSpectrum S)]
    (hM : Module.length S M ≠ ⊤) :
    Module.length R M = ∑ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[S] M) * (finiteAlgebraResidueDegree R S q : ℕ∞) := by
  simpa only [finsum_eq_sum_of_fintype] using finiteAlgebra_length_eq_finsum_tensor R S hM

/-- Restriction along a finite algebra over a local ring preserves finite length. -/
@[colib_tag "COL-0181"]
theorem finiteAlgebra_length_ne_top (hM : Module.length S M ≠ ⊤) :
    Module.length R M ≠ ⊤ := by
  classical
  let : Finite (MaximalSpectrum S) := finiteAlgebra_maximalSpectrum_finite R S
  let : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  rw [finiteAlgebra_length_eq_sum R S hM]
  apply WithTop.sum_ne_top.mpr
  intro q _
  exact WithTop.mul_ne_top (finiteAlgebra_localized_length_ne_top R S hM q)
    (ENat.natCast_ne_top _)

/-- A proposition-valued version of the finite-length restriction result. -/
@[colib_tag "COL-0181"]
theorem finiteAlgebra_isFiniteLength (hM : IsFiniteLength S M) : IsFiniteLength R M :=
  Module.length_ne_top_iff.mp
    (finiteAlgebra_length_ne_top R S (Module.length_ne_top_iff.mpr hM))

end Module
