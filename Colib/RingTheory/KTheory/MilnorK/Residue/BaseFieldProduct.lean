/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Residue.UnitProduct
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# Base-field action on the native DVR residue

A field map into the valuation ring lets arbitrary base-field Milnor classes act on the left
of the tame residue. The condition that the field map lands in the ring is essential; an
arbitrary fraction-field map would not give this formula. The proof uses the existing bundled
graded multiplication, symbol extensionality and the ring-unit tuple formula.

This adapts `MilnorK.DVR.residue_product_base_field_left` in
`Aglib.KTheory.MilnorK.Residue.Product` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, with all three universes independent.
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
  {k : Type w} [Field k]

/-- The canonical DVR residue respects the left action of a field mapping into the ring. -/
theorem dvrMilnorTameSymbol'_baseField_mul (f : k →+* R) (m n : ℕ)
    (x : MilnorKTheory k m) (z : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol' R F (m + n)
      (GradedMonoid.GMul.mul (i := m) (j := n + 1)
        (milnorKTheoryMap ((algebraMap R F).comp f) m x) z) =
      GradedMonoid.GMul.mul (i := m) (j := n)
        (milnorKTheoryMap ((IsLocalRing.residue R).comp f) m x)
        (dvrMilnorTameSymbol' R F n z) := by
  have h : (dvrMilnorTameSymbol' R F (m + n)).comp
      (((DirectSum.gMulHom (fun i => MilnorKTheory F i)).flip z).comp
        (milnorKTheoryMap ((algebraMap R F).comp f) m).toAddMonoidHom) =
      ((DirectSum.gMulHom (fun i => MilnorKTheory (IsLocalRing.ResidueField R) i)).flip
        (dvrMilnorTameSymbol' R F n z)).comp
          (milnorKTheoryMap ((IsLocalRing.residue R).comp f) m).toAddMonoidHom := by
    apply milnorKTheory_addHom_ext
    intro a
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply,
      LinearMap.toAddMonoidHom_coe, DirectSum.gMulHom_apply_apply,
      milnorKTheoryMap_tupleSymbol]
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
    exact dvrMilnorTameSymbol'_unitTuple_mul m n (Units.map f.toMonoidHom ∘ a) z
  exact DFunLike.congr_fun h x

end Stacks.Chow

attribute [colib_tag "COL-0109"] Stacks.Chow.dvrMilnorTameSymbol'_baseField_mul

add_to_stacks 0EAY
  "Construction consequence: base-field action through the valuation ring commutes with residue"
  Stacks.Chow.dvrMilnorTameSymbol'_baseField_mul
