/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.FundamentalIdentity

/-!
# Degree from an actual DVR uniformizer equation

The pinned Stacks local fundamental identity identifies the product of the
actual ramification index and residue degree with the fraction-field degree.
The native additive valuation identifies that index with the exponent of the
supplied uniformizer equation. Finite torsion-freeness supplies flatness and
faithfulness, and finite integral faithfulness supplies the local map.

No perfectness, separability, henselianity, or integral-closure presentation is
assumed. In prime degree, the actual exponent or residue degree must be one.

## Source provenance

Adapted from `Aglib/RingTheory/DVRRamificationDegree.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`7e773818e89786db19bafa4fa0633763fb8d92b2d774319286a446da893f82bd`.
The original module is `Motivic.Aglib.RingTheory.DVRRamificationDegree`, with source SHA-256
`0989e962d932824371e840d85385c29e423b63aa12cb44cf3b56c76eb67c4b40`.
The source proof through norm valuations is replaced by the pinned Stacks
fundamental identity. Its perfect-field and integral-closure hypotheses are
not needed for this stronger statement. All maps and residue fields are native.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v w z

namespace IsDiscreteValuationRing

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]

/-- The degree formula uses the actual exponent in the supplied uniformizer
equation, rather than an independent or assumed ramification index. -/
@[colib_tag "COL-0196",
  colib_ref "aglib_principal_euler_pin" "RingTheory/DVRRamificationDegree.lean"
    "adaptation" "Native local fundamental identity with the supplied uniformizer exponent"]
theorem finrank_eq_ramification_mul_residue_finrank
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    Module.finrank F E = e * Module.finrank (ResidueField R) (ResidueField S) := by
  let : FaithfulSMul R S := inferInstance
  let : Module.Flat R S := inferInstance
  let : IsLocalHom (algebraMap R S) := inferInstance
  have heidx : Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S = e := by
    have hv :=
      Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_ramificationIdx
        R S π hπ
    rw [he, addVal_def' u hϖ e] at hv
    exact_mod_cast hv.symm
  have hd :=
    Stacks.DiscreteValuationRing.Ramification.ramificationIdx_mul_inertiaDeg_eq_finrank
      R S F E
  rw [heidx, Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal R)] at hd
  exact hd.symm

/-- In actual prime field degree, either the literal ramification exponent or
the actual residue-field degree is one. -/
@[colib_tag "COL-0196"]
theorem ramification_eq_one_or_residue_finrank_eq_one
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (hp : Nat.Prime (Module.finrank F E)) :
    e = 1 ∨ Module.finrank (ResidueField R) (ResidueField S) = 1 := by
  have hd := finrank_eq_ramification_mul_residue_finrank R S F E hπ hϖ u e he
  rw [hd] at hp
  exact (Nat.prime_mul_iff.mp hp).elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)

end IsDiscreteValuationRing
