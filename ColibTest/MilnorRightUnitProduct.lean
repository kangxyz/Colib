module

import Colib.KTheory.MilnorK.Residue.RightUnitProduct

open Stacks.Chow

universe u v

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]

-- Arbitrary left classes and arbitrary right tuple degree; no characteristic restriction.
example (n m : ℕ) (z : MilnorKTheory F (n + 1)) (a : Fin m → Rˣ) :
    dvrMilnorTameSymbol' R F (n + m)
      (cast (congrArg (MilnorKTheory F) (Nat.add_right_comm n 1 m))
        (GradedMonoid.GMul.mul (i := n + 1) (j := m) z
          (milnorKTupleSymbol (Units.map (algebraMap R F).toMonoidHom ∘ a)))) =
      (-1 : ℤ) ^ m • GradedMonoid.GMul.mul (i := n) (j := m)
        (dvrMilnorTameSymbol' R F n z)
        (milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a)) :=
  dvrMilnorTameSymbol'_mul_unitTuple n m z a

-- A right degree-one unit produces additive negation; no nonvanishing is asserted.
example (n : ℕ) (z : MilnorKTheory F (n + 1)) (a : Fin 1 → Rˣ) :
    dvrMilnorTameSymbol' R F (n + 1)
      (GradedMonoid.GMul.mul (i := n + 1) (j := 1) z
        (milnorKTupleSymbol (Units.map (algebraMap R F).toMonoidHom ∘ a))) =
      -GradedMonoid.GMul.mul (i := n) (j := 1)
        (dvrMilnorTameSymbol' R F n z)
        (milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a)) := by
  simpa using dvrMilnorTameSymbol'_mul_unitTuple n 1 z a
