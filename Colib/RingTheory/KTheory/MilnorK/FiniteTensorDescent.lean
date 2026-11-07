/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.IntermediateField.FiniteUnits
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTransport

/-!
# Finite descent in the native Milnor tensor algebra

Every native tensor and every element of the native two-sided Steinberg ideal
over an algebraic extension comes from the corresponding object over a finite
intermediate field. Addition and multiplication combine witnesses by the
actual compositum of intermediate fields.

These are existence-of-preimage statements, not reflection of equality or
ideal membership along `milnorKTensorMap`. A field embedding need not induce
an injective tensor-algebra map over the integers. In particular, the ideal
preimage theorem alone does not prove finite-stage vanishing of a prescribed
Milnor class. No second tensor algebra, relation span, or Milnor quotient is
introduced here.
-/

@[expose] public noncomputable section

universe u v

variable {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E]

/-- The native tensor map commutes with inclusion of actual intermediate fields. -/
theorem milnorKTensorMap_val_inclusion {S T : IntermediateField k E} (h : S ≤ T)
    (x : MilnorKTensorAlgebra S) :
    milnorKTensorMap T.val.toRingHom
        (milnorKTensorMap (IntermediateField.inclusion h).toRingHom x) =
      milnorKTensorMap S.val.toRingHom x := by
  change ((milnorKTensorMap T.val.toRingHom).comp
    (milnorKTensorMap (IntermediateField.inclusion h).toRingHom)) x = _
  rw [milnorKTensorMap_comp]
  rfl

/-- Native tensor transport respects a chain of actual intermediate-field inclusions. -/
theorem milnorKTensorMap_inclusion_inclusion {S T U : IntermediateField k E}
    (hST : S ≤ T) (hTU : T ≤ U) (x : MilnorKTensorAlgebra S) :
    milnorKTensorMap (IntermediateField.inclusion hTU).toRingHom
        (milnorKTensorMap (IntermediateField.inclusion hST).toRingHom x) =
      milnorKTensorMap (IntermediateField.inclusion (hST.trans hTU)).toRingHom x := by
  change ((milnorKTensorMap _).comp (milnorKTensorMap _)) x = _
  rw [milnorKTensorMap_comp]
  rfl

variable (k E) [Algebra.IsAlgebraic k E]

/-- Every element of the actual tensor algebra is defined over a finite
intermediate field. The base and extension universes are independent. -/
theorem exists_finite_milnorKTensor (x : MilnorKTensorAlgebra E) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ y : MilnorKTensorAlgebra S, milnorKTensorMap S.val.toRingHom y = x := by
  induction x using TensorAlgebra.induction with
  | algebraMap z =>
      exact ⟨⊥, inferInstance, algebraMap ℤ _ z, (milnorKTensorMap _).commutes z⟩
  | ι a =>
      obtain ⟨S, hS, b, hb⟩ :=
        IntermediateField.exists_finite_units k E (fun _ : Unit => a.toMul)
      refine ⟨S, hS, TensorAlgebra.ι ℤ (Additive.ofMul (b ())), ?_⟩
      rw [milnorKTensorMap_ι, milnorKUnitsMap_ofMul]
      exact congrArg (fun z : Eˣ => TensorAlgebra.ι ℤ (Additive.ofMul z))
        (congrFun hb ())
  | mul x y hx hy =>
      obtain ⟨S, hS, a, ha⟩ := hx
      obtain ⟨T, hT, b, hb⟩ := hy
      let := hS
      let := hT
      refine ⟨S ⊔ T, inferInstance,
        milnorKTensorMap (IntermediateField.inclusion le_sup_left).toRingHom a *
          milnorKTensorMap (IntermediateField.inclusion le_sup_right).toRingHom b, ?_⟩
      rw [map_mul, milnorKTensorMap_val_inclusion, milnorKTensorMap_val_inclusion, ha, hb]
  | add x y hx hy =>
      obtain ⟨S, hS, a, ha⟩ := hx
      obtain ⟨T, hT, b, hb⟩ := hy
      let := hS
      let := hT
      refine ⟨S ⊔ T, inferInstance,
        milnorKTensorMap (IntermediateField.inclusion le_sup_left).toRingHom a +
          milnorKTensorMap (IntermediateField.inclusion le_sup_right).toRingHom b, ?_⟩
      rw [map_add, milnorKTensorMap_val_inclusion, milnorKTensorMap_val_inclusion, ha, hb]

/-- An actual Steinberg generator is the image of a Steinberg generator over
one finite intermediate field, not merely of an arbitrary tensor. -/
theorem exists_finite_milnorKSteinbergRelation (x : MilnorKTensorAlgebra E)
    (hx : x ∈ milnorKSteinbergRelations E) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ y : MilnorKTensorAlgebra S, y ∈ milnorKSteinbergRelations S ∧
        milnorKTensorMap S.val.toRingHom y = x := by
  obtain ⟨a, rfl⟩ := hx
  let S := IntermediateField.adjoin k ({a.1} : Set E)
  have hS : FiniteDimensional k S := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  let b : S := ⟨a.1, IntermediateField.subset_adjoin k _ (Set.mem_singleton _)⟩
  have hb0 : b ≠ 0 := fun h => a.2.1 (congrArg (fun z : S => (z : E)) h)
  have hb1 : b ≠ 1 := fun h => a.2.2 (congrArg (fun z : S => (z : E)) h)
  let y : MilnorKTensorAlgebra S :=
    TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 b hb0)) *
      TensorAlgebra.ι ℤ (Additive.ofMul (Units.mk0 (1 - b) (sub_ne_zero.mpr hb1.symm)))
  refine ⟨S, hS, y, ⟨⟨b, hb0, hb1⟩, rfl⟩, ?_⟩
  have hleft : Units.map S.val.toRingHom.toMonoidHom (Units.mk0 b hb0) =
      Units.mk0 a.1 a.2.1 := Units.ext rfl
  have hright : Units.map S.val.toRingHom.toMonoidHom
      (Units.mk0 (1 - b) (sub_ne_zero.mpr hb1.symm)) =
      Units.mk0 (1 - a.1) (sub_ne_zero.mpr a.2.2.symm) := Units.ext rfl
  simp only [y, map_mul, milnorKTensorMap_ι, milnorKUnitsMap_ofMul]
  exact congrArg₂ (fun x y : MilnorKTensorAlgebra E => x * y)
    (congrArg (fun z : Eˣ => TensorAlgebra.ι ℤ (Additive.ofMul z)) hleft)
    (congrArg (fun z : Eˣ => TensorAlgebra.ι ℤ (Additive.ofMul z)) hright)

/-- Every element of the actual two-sided Steinberg ideal has a preimage in
the Steinberg ideal of one finite intermediate field. This assertion does not
reflect ideal membership for a prescribed preimage under a tensor map. -/
theorem exists_finite_milnorKSteinbergIdeal (x : MilnorKTensorAlgebra E)
    (hx : x ∈ milnorKSteinbergIdeal E) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ y : MilnorKTensorAlgebra S, y ∈ milnorKSteinbergIdeal S ∧
        milnorKTensorMap S.val.toRingHom y = x := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
      obtain ⟨S, hS, y, hy, hxy⟩ := exists_finite_milnorKSteinbergRelation k E x hx
      exact ⟨S, hS, y, TwoSidedIdeal.subset_span hy, hxy⟩
  | zero =>
      exact ⟨⊥, inferInstance, 0, (milnorKSteinbergIdeal _).zero_mem, map_zero _⟩
  | add x y _ _ hx hy =>
      obtain ⟨S, hS, a, ha, hax⟩ := hx
      obtain ⟨T, hT, b, hb, hby⟩ := hy
      let := hS
      let := hT
      let iS := (IntermediateField.inclusion (show S ≤ S ⊔ T from le_sup_left)).toRingHom
      let iT := (IntermediateField.inclusion (show T ≤ S ⊔ T from le_sup_right)).toRingHom
      refine ⟨S ⊔ T, inferInstance, milnorKTensorMap iS a + milnorKTensorMap iT b,
        (milnorKSteinbergIdeal _).add_mem
          (milnorKTensorMap_mem_milnorKSteinbergIdeal iS ha)
          (milnorKTensorMap_mem_milnorKSteinbergIdeal iT hb), ?_⟩
      rw [map_add, milnorKTensorMap_val_inclusion, milnorKTensorMap_val_inclusion, hax, hby]
  | neg x _ hx =>
      obtain ⟨S, hS, a, ha, hax⟩ := hx
      refine ⟨S, hS, -a, (milnorKSteinbergIdeal _).neg_mem ha, ?_⟩
      rw [map_neg, hax]
  | left_absorb a x _ hx =>
      obtain ⟨S, hS, b, hb⟩ := exists_finite_milnorKTensor k E a
      obtain ⟨T, hT, y, hy, hyx⟩ := hx
      let := hS
      let := hT
      let iS := (IntermediateField.inclusion (show S ≤ S ⊔ T from le_sup_left)).toRingHom
      let iT := (IntermediateField.inclusion (show T ≤ S ⊔ T from le_sup_right)).toRingHom
      refine ⟨S ⊔ T, inferInstance, milnorKTensorMap iS b * milnorKTensorMap iT y,
        (milnorKSteinbergIdeal _).mul_mem_left _ _
          (milnorKTensorMap_mem_milnorKSteinbergIdeal iT hy), ?_⟩
      rw [map_mul, milnorKTensorMap_val_inclusion, milnorKTensorMap_val_inclusion, hb, hyx]
  | right_absorb b x _ hx =>
      obtain ⟨S, hS, y, hy, hyx⟩ := hx
      obtain ⟨T, hT, a, hab⟩ := exists_finite_milnorKTensor k E b
      let := hS
      let := hT
      let iS := (IntermediateField.inclusion (show S ≤ S ⊔ T from le_sup_left)).toRingHom
      let iT := (IntermediateField.inclusion (show T ≤ S ⊔ T from le_sup_right)).toRingHom
      refine ⟨S ⊔ T, inferInstance, milnorKTensorMap iS y * milnorKTensorMap iT a,
        (milnorKSteinbergIdeal _).mul_mem_right _ _
          (milnorKTensorMap_mem_milnorKSteinbergIdeal iS hy), ?_⟩
      rw [map_mul, milnorKTensorMap_val_inclusion, milnorKTensorMap_val_inclusion, hyx, hab]
