/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Symbols.Descent
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTransport

/-!
# Field transport across independent universes

The pinned Stacks transport uses a common universe for its fields. The universal property
extends that same map to fields in independent universes, without changing the native
`MilnorKTheory` object. In a common universe it is proved equal to `milnorKTransport`.

This adapts `Aglib.KTheory.MilnorK.Map` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The additive map is the existing
`LinearMap.toAddMonoidHom`, rather than a separately maintained operation.
-/

@[expose] public noncomputable section

universe u v w

variable {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L] {n : ℕ}

/-- Applying a field map to each entry preserves the defining symbol conditions. -/
theorem milnorKTupleSymbol_comp_unitsMap_isSymbolMap (φ : k →+* K) :
    IsMilnorKSymbolMap (fun a : Fin n → kˣ =>
      milnorKTupleSymbol (Units.map φ.toMonoidHom ∘ a)) where
  map_mul a i b c := by
    simp only [Function.comp_update, map_mul]
    exact milnorKTupleSymbol_update_mul _ i _ _
  steinberg a i j hij h := by
    apply milnorKTupleSymbol_steinberg _ i j hij
    change φ (a i : k) + φ (a j : k) = 1
    rw [← map_add, h, map_one]

/-- The native homogeneous Milnor group is functorial in fields of independent universes. -/
def milnorKTheoryMap (φ : k →+* K) (n : ℕ) :
    MilnorKTheory k n →ₗ[ℤ] MilnorKTheory K n :=
  (milnorKTupleSymbol_comp_unitsMap_isSymbolMap (n := n) φ).lift

/-- Field transport sends an ordered tuple symbol to the symbol of the field images. -/
@[simp] theorem milnorKTheoryMap_tupleSymbol (φ : k →+* K) (a : Fin n → kˣ) :
    milnorKTheoryMap φ n (milnorKTupleSymbol a) =
      milnorKTupleSymbol (Units.map φ.toMonoidHom ∘ a) :=
  (milnorKTupleSymbol_comp_unitsMap_isSymbolMap φ).lift_symbol a

/-- Identity field transport is the identity on the native homogeneous group. -/
@[simp] theorem milnorKTheoryMap_id :
    milnorKTheoryMap (RingHom.id k) n = LinearMap.id := by
  apply milnorKTheory_linearMap_ext
  intro a
  simp [Units.map, Function.comp_def]

/-- Composition of field maps is preserved, with all three universes independent. -/
theorem milnorKTheoryMap_comp (φ : k →+* K) (ψ : K →+* L) :
    milnorKTheoryMap (ψ.comp φ) n =
      (milnorKTheoryMap ψ n).comp (milnorKTheoryMap φ n) := by
  apply milnorKTheory_linearMap_ext
  intro a
  simp only [LinearMap.comp_apply, milnorKTheoryMap_tupleSymbol]
  rfl

section CommonUniverse

variable {k' : Type u} [Field k']

/-- The existing native ring map sends a degree-one symbol to the field-image symbol. -/
@[simp] theorem milnorKRingMap_symbol (φ : k →+* k') (a : kˣ) :
    milnorKRingMap φ (milnorKSymbol k a) =
      milnorKSymbol k' (Units.map φ.toMonoidHom a) := by
  change milnorKRingMap φ ((milnorKSteinbergIdeal k).ringCon.mk'
    (TensorAlgebra.ι ℤ (Additive.ofMul a))) = _
  rw [milnorKRingMap_mk', milnorKTensorMap_ι]
  rfl

/-- The existing native transport has the coordinatewise tuple-symbol formula. -/
@[simp] theorem milnorKTransport_tupleSymbol (φ : k →+* k') (a : Fin n → kˣ) :
    milnorKTransport φ n (milnorKTupleSymbol a) =
      milnorKTupleSymbol (Units.map φ.toMonoidHom ∘ a) := by
  apply Subtype.ext
  simp [milnorKSymbolProd, map_list_prod, List.map_ofFn, Function.comp_def]

/-- In a common universe the extension is exactly the existing Stacks transport. -/
theorem milnorKTheoryMap_eq_transport (φ : k →+* k') :
    milnorKTheoryMap φ n = (milnorKTransport φ n).toIntLinearMap := by
  apply milnorKTheory_linearMap_ext
  intro a
  exact (milnorKTheoryMap_tupleSymbol φ a).trans (milnorKTransport_tupleSymbol φ a).symm

end CommonUniverse

attribute [colib_tag "COL-0115"] milnorKTheoryMap milnorKTheoryMap_tupleSymbol
  milnorKTheoryMap_id milnorKTheoryMap_comp milnorKTheoryMap_eq_transport

add_to_stacks 0EAY
  "Construction consequence: field transport; independent universes are not stated in the tag"
  milnorKTheoryMap
add_to_stacks 0EAY
  "Construction background: both field maps act identically on the defining ordered symbols"
  milnorKTheoryMap_eq_transport
