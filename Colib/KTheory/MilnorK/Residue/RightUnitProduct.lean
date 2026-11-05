/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Residue.UnitProduct
public import Colib.KTheory.MilnorK.Symbols.Involution

/-!
# Right ring-unit products and the native DVR residue

Multiplication on the right by a degree-`m` tuple of ring units introduces the sign `(-1)^m`.
The left factor is an arbitrary homogeneous class. This is a direct consequence of the native
Stacks shift multiplication and grading involution, complementing the migrated left formula.
It is not attributed to a nonexistent right-product declaration in Aglib's `Residue.Product`.
The degree cast is ordinary equality transport; no second graded product is introduced.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

private theorem coe_degree_cast {k : Type*} [Field k] {i j : ℕ} (h : i = j)
    (x : MilnorKTheory k i) :
    ((cast (congrArg (MilnorKTheory k) h) x : MilnorKTheory k j) : MilnorKRing k) = x := by
  subst j
  rfl

/-- Right multiplication by a tuple of ring units contributes its degree parity sign. -/
theorem dvrMilnorTameSymbol_mul_unitTuple (hπ : Irreducible π) (n m : ℕ)
    (z : MilnorKTheory F (n + 1)) (a : Fin m → Rˣ) :
    dvrMilnorTameSymbol hπ (n + m)
      (cast (congrArg (MilnorKTheory F) (Nat.add_right_comm n 1 m))
        (GradedMonoid.GMul.mul (i := n + 1) (j := m) z
          (milnorKTupleSymbol (Units.map (algebraMap R F).toMonoidHom ∘ a)))) =
      (-1 : ℤ) ^ m • GradedMonoid.GMul.mul (i := n) (j := m)
        (dvrMilnorTameSymbol hπ n z)
        (milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a)) := by
  apply Subtype.ext
  rw [dvrMilnorTameSymbol_coe, coe_degree_cast (Nat.add_right_comm n 1 m)]
  change MilnorKShift.shift (dvrMilnorShiftMap hπ
      ((z : MilnorKRing F) * milnorKSymbolProd F
        (List.ofFn (Units.map (algebraMap R F).toMonoidHom ∘ a)))) =
    (-1 : ℤ) ^ m • (MilnorKShift.shift (dvrMilnorShiftMap hπ (z : MilnorKRing F)) *
      milnorKSymbolProd (IsLocalRing.ResidueField R)
        (List.ofFn (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a)))
  have hunit : milnorKSymbolProd F
      (List.ofFn (Units.map (algebraMap R F).toMonoidHom ∘ a)) =
        unitSymbolProd F (List.ofFn a) := by
    simp only [unitSymbolProd, List.map_ofFn, Function.comp_def]
    rfl
  rw [hunit, map_mul, dvrMilnorShiftMap_unitSymbolProd]
  simp only [MilnorKShift.shift_mul, MilnorKShift.main_mk, MilnorKShift.shift_mk,
    mul_zero, zero_mul, add_zero, zero_add, residueSymbolProd, milnorKInvolution_symbolProd,
    List.length_ofFn, List.map_ofFn, Function.comp_def, mul_smul_comm]

/-- The canonical native residue satisfies the same signed right ring-unit formula. -/
theorem dvrMilnorTameSymbol'_mul_unitTuple (n m : ℕ)
    (z : MilnorKTheory F (n + 1)) (a : Fin m → Rˣ) :
    dvrMilnorTameSymbol' R F (n + m)
      (cast (congrArg (MilnorKTheory F) (Nat.add_right_comm n 1 m))
        (GradedMonoid.GMul.mul (i := n + 1) (j := m) z
          (milnorKTupleSymbol (Units.map (algebraMap R F).toMonoidHom ∘ a)))) =
      (-1 : ℤ) ^ m • GradedMonoid.GMul.mul (i := n) (j := m)
        (dvrMilnorTameSymbol' R F n z)
        (milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a)) :=
  dvrMilnorTameSymbol_mul_unitTuple
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec n m z a

end Stacks.Chow

attribute [colib_tag "COL-0129"]
  Stacks.Chow.dvrMilnorTameSymbol_mul_unitTuple
  Stacks.Chow.dvrMilnorTameSymbol'_mul_unitTuple

add_to_stacks 0EAY "DVR tame-symbol background; formula follows from native shift multiplication"
  Stacks.Chow.dvrMilnorTameSymbol'_mul_unitTuple
