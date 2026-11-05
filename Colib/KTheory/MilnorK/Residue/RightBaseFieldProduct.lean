/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Residue.RightUnitProduct
public import Colib.KTheory.MilnorK.Symbols.Transport

/-!
# Right base-field action on the native DVR residue

A field map into the valuation ring lets an arbitrary degree-`m` base-field class act on the
right of the residue, with the integer sign `(-1)^m`. The left factor is also arbitrary.
The proof extends the native right ring-unit tuple formula by existing symbol extensionality.
This is a native consequence complementing the left formula in Aglib's `Residue.Product`,
not a claim that the source contains a same-name right formula. All three universes are independent.
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
  {k : Type w} [Field k]

/-- Right multiplication by a base-field class contributes the integer sign of its degree. -/
theorem dvrMilnorTameSymbol'_mul_baseField (f : k →+* R) (n m : ℕ)
    (z : MilnorKTheory F (n + 1)) (x : MilnorKTheory k m) :
    dvrMilnorTameSymbol' R F (n + m)
      (cast (congrArg (MilnorKTheory F) (Nat.add_right_comm n 1 m))
        (GradedMonoid.GMul.mul (i := n + 1) (j := m) z
          (milnorKTheoryMap ((algebraMap R F).comp f) m x))) =
      (-1 : ℤ) ^ m • GradedMonoid.GMul.mul (i := n) (j := m)
        (dvrMilnorTameSymbol' R F n z)
        (milnorKTheoryMap ((IsLocalRing.residue R).comp f) m x) := by
  let degreeCast : MilnorKTheory F ((n + 1) + m) →+ MilnorKTheory F ((n + m) + 1) :=
    (AddEquiv.cast (M := MilnorKTheory F) (Nat.add_right_comm n 1 m)).toAddMonoidHom
  have h : (dvrMilnorTameSymbol' R F (n + m)).comp
      (degreeCast.comp
        ((DirectSum.gMulHom (fun i => MilnorKTheory F i) z).comp
          (milnorKTheoryMap ((algebraMap R F).comp f) m).toAddMonoidHom)) =
      (-1 : ℤ) ^ m •
        ((DirectSum.gMulHom (fun i => MilnorKTheory (IsLocalRing.ResidueField R) i)
          (dvrMilnorTameSymbol' R F n z)).comp
            (milnorKTheoryMap ((IsLocalRing.residue R).comp f) m).toAddMonoidHom) := by
    apply milnorKTheory_addHom_ext
    intro a
    change dvrMilnorTameSymbol' R F (n + m)
        (cast (congrArg (MilnorKTheory F) (Nat.add_right_comm n 1 m))
          (GradedMonoid.GMul.mul (i := n + 1) (j := m) z
            (milnorKTheoryMap ((algebraMap R F).comp f) m (milnorKTupleSymbol a)))) =
      (-1 : ℤ) ^ m • GradedMonoid.GMul.mul (i := n) (j := m)
        (dvrMilnorTameSymbol' R F n z)
        (milnorKTheoryMap ((IsLocalRing.residue R).comp f) m (milnorKTupleSymbol a))
    simp only [milnorKTheoryMap_tupleSymbol]
    have hfield : Units.map ((algebraMap R F).comp f).toMonoidHom ∘ a =
        Units.map (algebraMap R F).toMonoidHom ∘ (Units.map f.toMonoidHom ∘ a) := by
      funext i
      apply Units.ext
      rfl
    have hres : Units.map ((IsLocalRing.residue R).comp f).toMonoidHom ∘ a =
        Units.map (IsLocalRing.residue R).toMonoidHom ∘ (Units.map f.toMonoidHom ∘ a) := by
      funext i
      apply Units.ext
      rfl
    rw [hfield, hres]
    exact dvrMilnorTameSymbol'_mul_unitTuple n m z (Units.map f.toMonoidHom ∘ a)
  exact DFunLike.congr_fun h x

end Stacks.Chow

attribute [colib_tag "COL-0128"] Stacks.Chow.dvrMilnorTameSymbol'_mul_baseField

add_to_stacks 0EAY "DVR tame-symbol background; signed right action is a native consequence"
  Stacks.Chow.dvrMilnorTameSymbol'_mul_baseField
