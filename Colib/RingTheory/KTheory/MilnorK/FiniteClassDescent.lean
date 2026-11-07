/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.FieldTheory.IntermediateField.FiniteUnits
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Finite fields of definition for native Milnor classes

Every class over an algebraic extension is the actual transport of a class
over a finite intermediate field, in every nonnegative degree. A finite
family, whose degrees may vary, admits one common intermediate field.

This is descent of elements, not descent of equalities. The argument uses
the existing native symbol extensionality and actual intermediate-field
inclusions. It introduces no new Milnor presentation or transport map.
-/

@[expose] public noncomputable section

universe u v w

variable {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E]

/-- Homogeneous field transport commutes with actual intermediate-field inclusions. -/
theorem milnorKTheoryMap_val_inclusion {S T : IntermediateField k E} (h : S ≤ T)
    (n : ℕ) (x : MilnorKTheory S n) :
    milnorKTheoryMap T.val.toRingHom n
        (milnorKTheoryMap (IntermediateField.inclusion h).toRingHom n x) =
      milnorKTheoryMap S.val.toRingHom n x := by
  rw [← LinearMap.comp_apply, ← milnorKTheoryMap_comp]
  rfl

variable (k E) [Algebra.IsAlgebraic k E]

/-- A native Milnor class over an algebraic extension comes from one finite
intermediate field. This includes degree zero and inseparable extensions. -/
theorem exists_finite_milnorKTheory (n : ℕ) (x : MilnorKTheory E n) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ y : MilnorKTheory S n, milnorKTheoryMap S.val.toRingHom n y = x := by
  let H : AddSubgroup (MilnorKTheory E n) :=
    { carrier := {x | ∃ S : IntermediateField k E, FiniteDimensional k S ∧
          ∃ y : MilnorKTheory S n, milnorKTheoryMap S.val.toRingHom n y = x}
      zero_mem' := ⟨⊥, inferInstance, 0, map_zero _⟩
      add_mem' := by
        rintro x y ⟨S, hS, a, ha⟩ ⟨T, hT, b, hb⟩
        let := hS
        let := hT
        refine ⟨S ⊔ T, inferInstance,
          milnorKTheoryMap (IntermediateField.inclusion le_sup_left).toRingHom n a +
            milnorKTheoryMap (IntermediateField.inclusion le_sup_right).toRingHom n b, ?_⟩
        rw [map_add, milnorKTheoryMap_val_inclusion, milnorKTheoryMap_val_inclusion, ha, hb]
      neg_mem' := by
        rintro x ⟨S, hS, a, ha⟩
        refine ⟨S, hS, -a, ?_⟩
        rw [map_neg, ha] }
  have h : QuotientAddGroup.mk' H = 0 := by
    apply milnorKTheory_addHom_ext
    intro a
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    obtain ⟨S, hS, b, hb⟩ := IntermediateField.exists_finite_units k E a
    refine ⟨S, hS, milnorKTupleSymbol b, ?_⟩
    rw [milnorKTheoryMap_tupleSymbol, hb]
  exact (QuotientAddGroup.eq_zero_iff x).mp (DFunLike.congr_fun h x)

/-- Finitely many native homogeneous classes, even in different degrees,
descend simultaneously to the same actual finite intermediate field. -/
theorem exists_finite_milnorKTheory_family {ι : Type w} [Finite ι]
    (d : ι → ℕ) (x : ∀ i, MilnorKTheory E (d i)) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ y : ∀ i, MilnorKTheory S (d i),
        ∀ i, milnorKTheoryMap S.val.toRingHom (d i) (y i) = x i := by
  classical
  let := Fintype.ofFinite ι
  have h (s : Finset ι) :
      ∃ S : IntermediateField k E, FiniteDimensional k S ∧
        ∀ i ∈ s, ∃ y : MilnorKTheory S (d i),
          milnorKTheoryMap S.val.toRingHom (d i) y = x i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨⊥, inferInstance, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨S, hS, a, ha⟩ := exists_finite_milnorKTheory k E (d i) (x i)
        obtain ⟨T, hT, hb⟩ := ih
        let := hS
        let := hT
        refine ⟨S ⊔ T, inferInstance, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          refine ⟨milnorKTheoryMap
            (IntermediateField.inclusion le_sup_left).toRingHom (d i) a, ?_⟩
          rw [milnorKTheoryMap_val_inclusion, ha]
        · obtain ⟨b, hb⟩ := hb j hj
          refine ⟨milnorKTheoryMap
            (IntermediateField.inclusion le_sup_right).toRingHom (d j) b, ?_⟩
          rw [milnorKTheoryMap_val_inclusion, hb]
  obtain ⟨S, hS, hy⟩ := h Finset.univ
  choose y hy using fun i => hy i (Finset.mem_univ i)
  exact ⟨S, hS, y, hy⟩

/-- Simultaneous finite descent can retain any prescribed finite intermediate
field of coefficients. The displayed lifts use the actual inclusion into the
compositum; neither a replacement field nor a universe lift is introduced. -/
theorem exists_finite_milnorKTheory_family_over {ι : Type w} [Finite ι]
    (S₀ : IntermediateField k E) [FiniteDimensional k S₀]
    (d : ι → ℕ) (x : ∀ i, MilnorKTheory E (d i)) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧ S₀ ≤ S ∧
      ∃ y : ∀ i, MilnorKTheory S (d i),
        ∀ i, milnorKTheoryMap S.val.toRingHom (d i) (y i) = x i := by
  obtain ⟨T, hT, y, hy⟩ := exists_finite_milnorKTheory_family k E d x
  let := hT
  refine ⟨S₀ ⊔ T, inferInstance, le_sup_left,
    fun i => milnorKTheoryMap
      (IntermediateField.inclusion le_sup_right).toRingHom (d i) (y i), ?_⟩
  intro i
  rw [milnorKTheoryMap_val_inclusion, hy]

add_to_stacks 0EAY
  "Derived finite-stage descent in the native homogeneous quotient, not stated by the tag"
  exists_finite_milnorKTheory

attribute [colib_tag "COL-0263"]
  exists_finite_milnorKTheory
  exists_finite_milnorKTheory_family
  exists_finite_milnorKTheory_family_over

attribute [colib_ref "aglib_principal_euler_pin"
  "KTheory/MilnorK/FiniteRelationDescent.lean:83-100" "ingredient"
  "Finite-unit fields; native generation and finite composita yield simultaneous class descent"]
  exists_finite_milnorKTheory_family_over
