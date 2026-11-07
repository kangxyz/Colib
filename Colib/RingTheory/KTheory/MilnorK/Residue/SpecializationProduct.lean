/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Residue.Specialization

/-!
# Specialization preserves native graded multiplication

For an actual DVR and a specified uniformizer, specialization preserves products of arbitrary
homogeneous Milnor classes. This is the actual-DVR specialization of `MilnorK.specialize_product`
in `Aglib.KTheory.MilnorK.Residue.Product` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The proof directly uses multiplicativity of the native
shift map and its main component; no second product or ring realization is introduced.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

/-- Specialization at the specified uniformizer preserves arbitrary homogeneous products. -/
theorem dvrMilnorSpecialization_gmul (hπ : Irreducible π) (m n : ℕ)
    (x : MilnorKTheory F m) (y : MilnorKTheory F n) :
    dvrMilnorSpecialization hπ (m + n) (GradedMonoid.GMul.mul (i := m) (j := n) x y) =
      GradedMonoid.GMul.mul (i := m) (j := n)
        (dvrMilnorSpecialization hπ m x) (dvrMilnorSpecialization hπ n y) := by
  apply Subtype.ext
  simp only [dvrMilnorSpecialization_coe, SetLike.coe_gMul, map_mul, MilnorKShift.main_mul]

end Stacks.Chow

attribute [colib_tag "COL-0116"] Stacks.Chow.dvrMilnorSpecialization_gmul

add_to_stacks 0EAY "Construction consequence: homogeneous specialization preserves multiplication"
  Stacks.Chow.dvrMilnorSpecialization_gmul
