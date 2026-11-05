/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition

/-!
# The closed fibre of a finite algebra over a local ring

A finite algebra over a local ring has finitely many maximal ideals. They all lie over
its closed point and have finite residue degrees. The algebra itself need not be local
or Artinian. Only its actual closed fibre is asserted to be Artinian.

The native Stacks semilocal decomposition supplies the finiteness and local-map facts.
The quotient presentation of each residue degree is retained for source compatibility.
The ring universes are independent, and no Noetherian hypothesis is used.

## Source provenance

This adapts `Aglib/RingTheory/FiniteLength/FiniteAlgebraFiber.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`bd8b10a57abedbbd23c988cbf017f65c9b72ffcfd8c092fc9783b5946bad33b6`.
Its motivic source is `Motivic.RingTheory.LocalLength.FiniteAlgebraFiber`, recorded in
Aglib's `docs/migration/motivic-milnor-k.json`. Native reuse is from pinned Stacks
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.

-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Module

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [Module.Finite R S]

/-- Every maximal ideal lies over the maximal ideal of the local base. -/
theorem finiteAlgebra_maximal_under (q : MaximalSpectrum S) :
    q.asIdeal.under R = IsLocalRing.maximalIdeal R :=
  Stacks.Length.comap_asIdeal_eq_maximalIdeal (A := R) q

/-- The actual closed fibre is a finite algebra over a field, hence Artinian. -/
@[colib_tag "COL-0180",
  colib_ref "aglib_principal_euler_pin" "RingTheory/FiniteLength/FiniteAlgebraFiber.lean"
    "adaptation" "Actual closed fibre and quotient residue degrees over a local base"]
theorem finiteAlgebra_specialFiber_artinian :
    IsArtinianRing ((IsLocalRing.maximalIdeal R).Fiber S) := by
  change IsArtinianRing ((IsLocalRing.maximalIdeal R).ResidueField ⊗[R] S)
  exact IsArtinianRing.of_finite (IsLocalRing.maximalIdeal R).ResidueField _

include R in
/-- There are finitely many maximal ideals; no enumeration is assumed. -/
@[colib_tag "COL-0180"]
theorem finiteAlgebra_maximalSpectrum_finite : Finite (MaximalSpectrum S) :=
  Stacks.Length.finite_maximalSpectrum (A := R) (B := S)

attribute [local instance] Ideal.Quotient.field

/-- The actual maximal quotient is the residue field of its actual prime localization. -/
@[colib_tag "COL-0180"]
def finiteAlgebraResidueQuotientEquiv (q : MaximalSpectrum S) :
    (S ⧸ q.asIdeal) ≃ₐ[S] q.asIdeal.ResidueField :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom S (S ⧸ q.asIdeal) q.asIdeal.ResidueField)
    q.asIdeal.bijective_algebraMap_quotient_residueField

/-- The quotient residue field is finite over the residue field of the local base. -/
theorem finiteAlgebra_residue_finite (q : MaximalSpectrum S) :
    Module.Finite (IsLocalRing.ResidueField R) (S ⧸ q.asIdeal) := by
  have : Module.Finite R (S ⧸ q.asIdeal) := Module.Finite.trans S (S ⧸ q.asIdeal)
  infer_instance

/-- The source-compatible degree uses the literal maximal quotient. -/
@[colib_tag "COL-0180"]
abbrev finiteAlgebraResidueDegree (q : MaximalSpectrum S) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField R) (S ⧸ q.asIdeal)

/-- The base length of a maximal quotient is its residue degree. -/
theorem finiteAlgebra_residue_length (q : MaximalSpectrum S) :
    Module.length R (S ⧸ q.asIdeal) = (finiteAlgebraResidueDegree R S q : ℕ∞) := by
  have := finiteAlgebra_residue_finite R S q
  calc
    _ = Module.length (IsLocalRing.ResidueField R) (S ⧸ q.asIdeal) :=
      Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := R))
    _ = _ := Module.length_eq_finrank _ _

/-- The quotient degree agrees with the native localized-residue-field degree.
The local-hom instance is supplied by `Stacks.Length.isLocalHom_algebraMap_localization`.
Comparing base lengths avoids introducing a second residue-field algebra structure. -/
@[colib_tag "COL-0180"]
theorem finiteAlgebra_residueDegree_eq_localized (q : MaximalSpectrum S)
    [IsLocalHom (algebraMap R (Localization.AtPrime q.asIdeal))] :
    finiteAlgebraResidueDegree R S q =
      Module.finrank (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) := by
  have := Stacks.Length.finite_residueField R q
  have h :=
    ((finiteAlgebraResidueQuotientEquiv (S := S) q).toLinearEquiv.restrictScalars R).length_eq
  rw [finiteAlgebra_residue_length R S q,
    Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := R)),
    Module.length_eq_finrank] at h
  exact ENat.natCast_inj.mp h

end Module
