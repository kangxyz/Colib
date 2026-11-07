/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Residue.RamifiedOrder
public import Colib.RingTheory.KTheory.MilnorK.Residue.DegreeOne
public import Colib.RingTheory.KTheory.MilnorK.Symbols.DegreeOneTransport

/-!
# Ramified field restriction in residue degree one

For the actual equation `j π = u ρ^e`, the degree-one residues, identified with integers,
commute with field restriction up to multiplication by `e`. This is a consequence of the
migrated native integer-order formula and the native K1/K0 identifications. It does not assert
all-degree ramified residue naturality or uniformizer-independent canonical comparison.

The integer-order hypothesis and exponent match
`MilnorK.K2.DVR.ramified_value_map` in
`Aglib.KTheory.MilnorK.K2.DVR.RamifiedRestriction` (revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`). No positivity assumption is needed for this equality;
for a local ring map the supplied uniformizer equation forces positive exponent.
-/

@[expose] public noncomputable section

universe u v w z

namespace Stacks.Chow

variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type w} {E : Type z} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]

/-- Ramification multiplies the integer-valued native degree-one residue by its exponent. -/
theorem dvrMilnorTameSymbol_one_map_ramified (j : R →+* S) (f : F →+* E)
    (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
    {π : R} {ρ : S} (hπ : Irreducible π) (hρ : Irreducible ρ)
    (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e) (x : MilnorKTheory F 1) :
    milnorKTheoryZeroAddEquiv (IsLocalRing.ResidueField S)
        (dvrMilnorTameSymbol hρ 0 (milnorKTheoryMap f 1 x)) =
      (e : ℤ) * milnorKTheoryZeroAddEquiv (IsLocalRing.ResidueField R)
        (dvrMilnorTameSymbol hπ 0 x) := by
  rw [milnorKTheoryZeroAddEquiv_dvrMilnorTameSymbol,
    milnorKTheoryZeroAddEquiv_dvrMilnorTameSymbol, milnorKTheoryOneAddEquiv_map]
  exact dvrFracOrd_map_ramified j f hf hπ hρ u e hπmap _

end Stacks.Chow

attribute [colib_tag "COL-0140"] Stacks.Chow.dvrMilnorTameSymbol_one_map_ramified
attribute [stacks 0EAY "DVR tame-symbol background; ramified degree-one consequence proved here"]
  Stacks.Chow.dvrMilnorTameSymbol_one_map_ramified
