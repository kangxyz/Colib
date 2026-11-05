/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Residue.CanonicalRamifiedMap
public import Colib.KTheory.MilnorK.Residue.Specialization

/-!
# Ramified specialization on arbitrary homogeneous classes

This adapts `MilnorK.DVR.specialize_ramified_restrict` in
`Aglib.KTheory.MilnorK.Residue.RamifiedRestriction`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, lines 183–205. The correction is on the right
and has a plus sign. Specializations remain normalized by the stated uniformizers, while the
residue in the correction is the canonical native residue. No independence of specialization
is asserted. The proof promotes the already proved native main-component comparison.
-/

@[expose] public noncomputable section

universe u v w z

namespace Stacks.Chow

variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type w} {E : Type z} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) [IsLocalHom j] (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R} {ρ : S}

include hf

/-- Normalized specialization under ramification has the literal right unit correction. -/
theorem dvrMilnorSpecialization_map_ramified (hπ : Irreducible π) (hρ : Irreducible ρ)
    (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e) (n : ℕ)
    (x : MilnorKTheory F (n + 1)) :
    dvrMilnorSpecialization hρ (n + 1) (milnorKTheoryMap f (n + 1) x) =
      milnorKTheoryMap (IsLocalRing.ResidueField.map j) (n + 1)
          (dvrMilnorSpecialization hπ (n + 1) x) +
        GradedMonoid.GMul.mul (i := n) (j := 1)
          (milnorKTheoryMap (IsLocalRing.ResidueField.map j) n (dvrMilnorTameSymbol' R F n x))
          (milnorKTupleSymbol
            (fun _ : Fin 1 => Units.map (IsLocalRing.residue S).toMonoidHom u)) := by
  let c : MilnorKTheory (IsLocalRing.ResidueField S) 1 :=
    milnorKTupleSymbol (fun _ : Fin 1 => Units.map (IsLocalRing.residue S).toMonoidHom u)
  have h : (dvrMilnorSpecialization hρ (n + 1)).toAddMonoidHom.comp
        (milnorKTheoryMap f (n + 1)).toAddMonoidHom =
      (milnorKTheoryMap (IsLocalRing.ResidueField.map j) (n + 1)).toAddMonoidHom.comp
          (dvrMilnorSpecialization hπ (n + 1)).toAddMonoidHom +
        ((DirectSum.gMulHom (fun i => MilnorKTheory (IsLocalRing.ResidueField S) i)).flip c).comp
          ((milnorKTheoryMap (IsLocalRing.ResidueField.map j) n).toAddMonoidHom.comp
            (dvrMilnorTameSymbol' R F n)) := by
    apply milnorKTheory_addHom_ext
    intro a
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply, AddMonoidHom.flip_apply,
      LinearMap.toAddMonoidHom_coe, DirectSum.gMulHom_apply_apply, milnorKTheoryMap_tupleSymbol]
    rw [dvrMilnorTameSymbol'_eq_of_ramified_identity hπ]
    apply Subtype.ext
    simp only [AddSubgroup.coe_add, SetLike.coe_gMul, ← milnorKRingMapLift_coe,
      dvrMilnorSpecialization_coe, dvrMilnorTameSymbol_coe, coe_milnorKTupleSymbol,
      c, List.ofFn_const, List.replicate_one, milnorKSymbolProd_singleton]
    simpa only [List.map_ofFn, Function.comp_def] using
      (dvrMilnorShiftMap_symbolProd_map_ramified j f hf hπ hρ u e hπmap (List.ofFn a)).1
  exact DFunLike.congr_fun h x

omit hf in
/-- On the canonical residue kernel, specialization is independent of the chosen uniformizer.
This is the actual-DVR case of `MilnorK.specialize_eq_on_residue_kernel` in source `Residue.Change`.
-/
theorem dvrMilnorSpecialization_eq_on_residue_kernel {τ : R} (hπ : Irreducible π)
    (hτ : Irreducible τ) (n : ℕ) (x : MilnorKTheory F (n + 1))
    (hx : dvrMilnorTameSymbol' R F n x = 0) :
    dvrMilnorSpecialization hτ (n + 1) x = dvrMilnorSpecialization hπ (n + 1) x := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible R hτ hπ
  have hπmap : (RingHom.id R) π = (u : R) * τ ^ 1 := by
    simpa only [RingHom.id_apply, pow_one, mul_comm] using hu.symm
  have h := dvrMilnorSpecialization_map_ramified (RingHom.id R) (RingHom.id F)
    (fun _ => rfl) hπ hτ u 1 hπmap n x
  simpa [IsLocalRing.ResidueField.map_id, hx, DirectSum.GNonUnitalNonAssocSemiring.zero_mul] using h

end Stacks.Chow

attribute [colib_tag "COL-0151"]
  Stacks.Chow.dvrMilnorSpecialization_map_ramified
  Stacks.Chow.dvrMilnorSpecialization_eq_on_residue_kernel
attribute [stacks 0EAY
  "Tame-symbol background; specialization correction and independence proved here"]
  Stacks.Chow.dvrMilnorSpecialization_map_ramified
  Stacks.Chow.dvrMilnorSpecialization_eq_on_residue_kernel
