/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Residue.UnitProduct

universe u v

open Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]

-- Independent ring and field universes; the right factor is an arbitrary homogeneous class.
example (m n : ℕ) (a : Fin m → Rˣ) (z : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' R F (m + n)
      (GradedMonoid.GMul.mul (i := m) (j := n + 1)
        (milnorKTupleSymbol (Units.map (algebraMap R F).toMonoidHom ∘ a)) z) =
      GradedMonoid.GMul.mul (i := m) (j := n)
        (milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘ a))
        (dvrMilnorTameSymbol' R F n z) :=
  dvrMilnorTameSymbol'_unitTuple_mul m n a z

-- Degree-zero target and empty left tuple are both included.
example (z : MilnorKTheory F 1) :
    dvrMilnorTameSymbol' R F 0
      (GradedMonoid.GMul.mul (i := 0) (j := 1)
        (milnorKTupleSymbol (Units.map (algebraMap R F).toMonoidHom ∘
          (Fin.elim0 : Fin 0 → Rˣ))) z) =
      GradedMonoid.GMul.mul (i := 0) (j := 0)
        (milnorKTupleSymbol (Units.map (IsLocalRing.residue R).toMonoidHom ∘
          (Fin.elim0 : Fin 0 → Rˣ)))
        (dvrMilnorTameSymbol' R F 0 z) :=
  dvrMilnorTameSymbol'_unitTuple_mul 0 0 Fin.elim0 z
