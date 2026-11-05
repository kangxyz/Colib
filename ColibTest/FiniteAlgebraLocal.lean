/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Length.FiniteAlgebra
import Colib.RingTheory.Length.FiniteAlgebraLocal
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.LocalRing.NonLocalRing

/-!
# Regressions for finite-algebra length over a local base

The generic tests keep the universes of the base ring, finite algebra and module independent.
They assume neither Noetherianity nor flatness nor a domain hypothesis; in particular, the
finite algebra is not assumed local. The product tests use the actual nonlocal algebra
`k × k`. The final test compares the existing field ring-coefficient pilot with the new
module formula, using their literal prime/maximal spectra and residue-degree presentations.
-/

noncomputable section

open scoped BigOperators TensorProduct

-- The quotient-field abbreviation is not a global instance exported by the imported module.
attribute [local instance] Ideal.Quotient.field

universe u v w

section LocalBase

variable (R : Type u) (S : Type v) [CommRing R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [Module.Finite R S]

-- No Noetherian base, local finite algebra, or preselected maximal-spectrum enumeration.
example (q : MaximalSpectrum S) :
    q.asIdeal.under R = IsLocalRing.maximalIdeal R :=
  Module.finiteAlgebra_maximal_under R S q

example : IsArtinianRing ((IsLocalRing.maximalIdeal R).Fiber S) :=
  Module.finiteAlgebra_specialFiber_artinian R S

example : Finite (MaximalSpectrum S) :=
  Module.finiteAlgebra_maximalSpectrum_finite R S

-- The source coefficient uses the actual maximal quotient, not a replacement field.
example (q : MaximalSpectrum S) :
    (S ⧸ q.asIdeal) ≃ₐ[S] q.asIdeal.ResidueField :=
  Module.finiteAlgebraResidueQuotientEquiv S q

example (q : MaximalSpectrum S) :
    Module.Finite (IsLocalRing.ResidueField R) (S ⧸ q.asIdeal) :=
  Module.finiteAlgebra_residue_finite R S q

example (q : MaximalSpectrum S) :
    Module.finiteAlgebraResidueDegree R S q =
      Module.finrank (IsLocalRing.ResidueField R) (S ⧸ q.asIdeal) :=
  rfl

example (q : MaximalSpectrum S) :
    Module.length R (S ⧸ q.asIdeal) =
      (Module.finrank (IsLocalRing.ResidueField R) (S ⧸ q.asIdeal) : ℕ∞) :=
  Module.finiteAlgebra_residue_length R S q

-- The local-map hypothesis is derived from the finite algebra, not imposed on the caller.
local instance (q : MaximalSpectrum S) :
    IsLocalHom (algebraMap R (Localization.AtPrime q.asIdeal)) :=
  Stacks.Length.isLocalHom_algebraMap_localization (A := R) q

example (q : MaximalSpectrum S) :
    Module.finrank (IsLocalRing.ResidueField R) (S ⧸ q.asIdeal) =
      Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) :=
  Module.finiteAlgebra_residueDegree_eq_localized R S q

variable (M : Type w) [AddCommGroup M] [Module S M] [Module R M]
  [IsScalarTower R S M]

example (hM : Module.length S M ≠ ⊤) (q : MaximalSpectrum S) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl M) ≠ ⊤ :=
  Module.finiteAlgebra_localized_length_ne_top R S hM q

example [Fintype (MaximalSpectrum S)] (hM : Module.length S M ≠ ⊤) :
    Module.length R M = ∑ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) *
          (Module.finiteAlgebraResidueDegree R S q : ℕ∞) :=
  Module.finiteAlgebra_length_eq_sum R S hM

example (hM : Module.length S M ≠ ⊤) :
    Module.length R M = ∑ᶠ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) *
          (Module.finiteAlgebraResidueDegree R S q : ℕ∞) :=
  Module.finiteAlgebra_length_eq_finsum R S hM

-- This is the literal source tensor formula, including the quotient-field coefficient.
example [Fintype (MaximalSpectrum S)] (hM : Module.length S M ≠ ⊤) :
    Module.length R M = ∑ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[S] M) *
          (Module.finrank (IsLocalRing.ResidueField R) (S ⧸ q.asIdeal) : ℕ∞) :=
  Module.finiteAlgebra_length_eq_sum_tensor R S hM

example (hM : Module.length S M ≠ ⊤) :
    Module.length R M = ∑ᶠ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[S] M) *
          (Module.finiteAlgebraResidueDegree R S q : ℕ∞) :=
  Module.finiteAlgebra_length_eq_finsum_tensor R S hM

-- The tensor presentation computes the same intrinsic sum as the native localization.
example (hM : Module.length S M ≠ ⊤) :
    (∑ᶠ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) *
          (Module.finiteAlgebraResidueDegree R S q : ℕ∞)) =
      ∑ᶠ q : MaximalSpectrum S,
        Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal ⊗[S] M) *
            (Module.finiteAlgebraResidueDegree R S q : ℕ∞) :=
  (Module.finiteAlgebra_length_eq_finsum R S hM).symm.trans
    (Module.finiteAlgebra_length_eq_finsum_tensor R S hM)

example (hM : Module.length S M ≠ ⊤) : Module.length R M ≠ ⊤ :=
  Module.finiteAlgebra_length_ne_top R S hM

example (hM : IsFiniteLength S M) : IsFiniteLength R M :=
  Module.finiteAlgebra_isFiniteLength R S hM

-- Any subsingleton module tests the zero module in its own independent universe.
example [Subsingleton M] :
    (∑ᶠ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) *
          (Module.finiteAlgebraResidueDegree R S q : ℕ∞)) = 0 := by
  have hM : Module.length S M ≠ ⊤ := by simp
  rw [← Module.finiteAlgebra_length_eq_finsum R S hM]
  exact Module.length_eq_zero

example [Subsingleton M] :
    (∑ᶠ q : MaximalSpectrum S,
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[S] M) *
          (Module.finiteAlgebraResidueDegree R S q : ℕ∞)) = 0 := by
  have hM : Module.length S M ≠ ⊤ := by simp
  rw [← Module.finiteAlgebra_length_eq_finsum_tensor R S hM]
  exact Module.length_eq_zero

example [Subsingleton M] : IsFiniteLength R M := by
  apply Module.finiteAlgebra_isFiniteLength R S
  exact Module.length_ne_top_iff.mp (by simp)

end LocalBase

section NonlocalProduct

variable (k : Type u) [Field k]

example : Module.Finite k (k × k) := inferInstance

example : ¬ IsLocalRing (k × k) :=
  IsLocalRing.not_isLocalRing_of_prod_of_nontrivial k k

example : Finite (MaximalSpectrum (k × k)) :=
  Module.finiteAlgebra_maximalSpectrum_finite k (k × k)

variable (M : Type w) [AddCommGroup M] [Module (k × k) M] [Module k M]
  [IsScalarTower k (k × k) M]

-- The finite algebra is genuinely nonlocal and the module is not specialized to the ring.
example (hM : Module.length (k × k) M ≠ ⊤) :
    Module.length k M = ∑ᶠ q : MaximalSpectrum (k × k),
      Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) *
          (Module.finiteAlgebraResidueDegree k (k × k) q : ℕ∞) :=
  Module.finiteAlgebra_length_eq_finsum k (k × k) hM

example (hM : Module.length (k × k) M ≠ ⊤) :
    Module.length k M = ∑ᶠ q : MaximalSpectrum (k × k),
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[k × k] M) *
          (Module.finiteAlgebraResidueDegree k (k × k) q : ℕ∞) :=
  Module.finiteAlgebra_length_eq_finsum_tensor k (k × k) hM

example (hM : IsFiniteLength (k × k) M) : IsFiniteLength k M :=
  Module.finiteAlgebra_isFiniteLength k (k × k) hM

end NonlocalProduct

section FieldPilot

variable (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
  [Module.Finite k S]

-- The old ring-coefficient sum and the new module sum agree on M = S.
-- Finite length over S is derived here; it is not an extra hypothesis of the test.
example :
    ((∑ᶠ x : PrimeSpectrum S,
      (Module.length (Localization.AtPrime x.asIdeal) (Localization.AtPrime x.asIdeal)).toNat *
        Module.finrank k (IsLocalRing.ResidueField (Localization.AtPrime x.asIdeal)) : ℕ) : ℕ∞) =
      ∑ᶠ q : MaximalSpectrum S,
        Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl S) *
            (Module.finiteAlgebraResidueDegree k S q : ℕ∞) := by
  let : IsArtinian S S := isArtinian_of_tower k (M := S) inferInstance
  let : IsNoetherian S S := isNoetherian_of_tower k (M := S) inferInstance
  have hS : Module.length S S ≠ ⊤ := Module.length_ne_top
  rw [← IsArtinianRing.finrank_eq_finsum_length_mul_residueFinrank k S,
    ← Module.length_eq_finrank k S]
  exact Module.finiteAlgebra_length_eq_finsum k S hS

end FieldPilot
