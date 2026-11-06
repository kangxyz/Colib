/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Residue.CanonicalRamifiedMap
public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Canonical DVR residues and actual integral automorphisms

An actual ring equivalence carries a uniformizer to a uniformizer. The canonical ramified
formula therefore gives exponent one, with the existing residue-field map. Specializing
to Mathlib's actual `galRestrict` identifies the residue of a fraction-field automorphism
with the residue action of its integral restriction. The integral closure is the specified
finite DVR algebra itself, not a second integral-closure carrier.

No Galois, prime-degree, perfectness, Henselianity or tameness assumption is needed for this
equivariance. This is one input to the error-annihilator argument, not a norm-residue theorem.
All four universes in the ring-equivalence statement remain independent.

-/

@[expose] public noncomputable section

universe u v w z

namespace Stacks.Chow

open IsLocalRing

/-- The canonical residue is natural for an actual integral ring equivalence and a
compatible fraction-field homomorphism. Its ramification exponent is proved to be one. -/
theorem dvrMilnorTameSymbol'_map_ringEquiv
    {R : Type u} {S : Type v}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {F : Type w} {E : Type z} [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
    (j : R ≃+* S) (f : F →+* E)
    (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r)) (n : ℕ) :
    (dvrMilnorTameSymbol' S E n).comp (milnorKTheoryMap f (n + 1)).toAddMonoidHom =
      (milnorKTheoryMap (ResidueField.map (j : R →+* S)) n).toAddMonoidHom.comp
        (dvrMilnorTameSymbol' R F n) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hjπ : Irreducible (j π) := hπ.map j
  have h := dvrMilnorTameSymbol'_map_ramified (j : R →+* S) f hf hπ hjπ
    (1 : Sˣ) 1 (by simp) n
  simpa only [Nat.cast_one, one_smul] using h

variable (R S F E : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Canonical residues intertwine a fraction-field automorphism with the residue map of
its native integral restriction on the specified finite DVR algebra. -/
theorem dvrMilnorTameSymbol'_map_galRestrict (σ : Gal(E/F)) (n : ℕ) :
    letI : Algebra.IsAlgebraic F E := isAlgebraic_of_isFractionRing R S F E
    (dvrMilnorTameSymbol' S E n).comp
        (milnorKTheoryMap σ.toRingHom (n + 1)).toAddMonoidHom =
      (milnorKTheoryMap
        (ResidueField.map (galRestrict R F E S σ : S →+* S)) n).toAddMonoidHom.comp
          (dvrMilnorTameSymbol' S E n) := by
  let : Algebra.IsAlgebraic F E := isAlgebraic_of_isFractionRing R S F E
  exact dvrMilnorTameSymbol'_map_ringEquiv (galRestrict R F E S σ).toRingEquiv
    σ.toRingHom (fun s => (algebraMap_galRestrict_apply R σ s).symm) n

end Stacks.Chow

end
