/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.SymbolMap
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Ext
public import Colib.LinearAlgebra.TensorAlgebra.IdealVanishing

/-!
# Descent of symbol maps through the native Steinberg ideal

A multilinear tuple function satisfying the adjacent Steinberg relation extends through the
actual Stacks tensor-algebra quotient. The proof verifies annihilation of the whole two-sided
ideal, not only its named generators. Source: `Aglib.KTheory.MilnorK.Basic` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`; the target uses only `MilnorKTheory`.
-/

@[expose] public noncomputable section

universe u v

variable {k : Type u} [Field k] {n : ℕ} {A : Type v} [AddCommGroup A]

namespace IsMilnorKSymbolMap

variable {s : (Fin n → kˣ) → A} (hs : IsMilnorKSymbolMap s)

/-- The homogeneous tensor extension kills the entire native Steinberg ideal. -/
theorem liftHomogeneous_eq_zero_of_mem {z : MilnorKTensorAlgebra k}
    (hz : z ∈ milnorKSteinbergIdeal k) :
    TensorAlgebra.liftHomogeneous hs.toMultilinear z = 0 := by
  apply TensorAlgebra.map_eq_zero_of_mem_span_of_tprod _ (milnorKSteinbergRelations k) _ hz
  intro i j a b r hr
  obtain ⟨x, rfl⟩ := hr
  let u : Additive kˣ := Additive.ofMul (Units.mk0 x.1 x.2.1)
  let v : Additive kˣ :=
    Additive.ofMul (Units.mk0 (1 - x.1) (sub_ne_zero.mpr x.2.2.symm))
  let c : Fin ((i + 2) + j) → Additive kˣ := Fin.append (Fin.append a ![u, v]) b
  have hp : TensorAlgebra.tprod ℤ (Additive kˣ) ((i + 2) + j) c =
      TensorAlgebra.tprod ℤ (Additive kˣ) i a *
        (TensorAlgebra.ι ℤ u * TensorAlgebra.ι ℤ v) *
          TensorAlgebra.tprod ℤ (Additive kˣ) j b := by
    simp only [c, TensorAlgebra.tprod_append]
    congr 2
    simp [TensorAlgebra.tprod_apply, List.ofFn_succ]
  change TensorAlgebra.liftHomogeneous hs.toMultilinear
    (TensorAlgebra.tprod ℤ (Additive kˣ) i a *
      (TensorAlgebra.ι ℤ u * TensorAlgebra.ι ℤ v) *
        TensorAlgebra.tprod ℤ (Additive kˣ) j b) = 0
  rw [← hp]
  by_cases hdeg : (i + 2) + j = n
  · subst n
    rw [TensorAlgebra.liftHomogeneous_tprod, toMultilinear_apply]
    apply hs.steinberg (Additive.toMul ∘ c)
      (Fin.castAdd j (Fin.natAdd i (0 : Fin 2)))
      (Fin.castAdd j (Fin.natAdd i (1 : Fin 2)))
    · rfl
    · simp [c, u, v]
  · exact TensorAlgebra.liftHomogeneous_tprod_of_ne _ hdeg c

/-- The tensor extension descends to an additive map on the native quotient ring. -/
def quotientAddHom : MilnorKRing k →+ A :=
  (milnorKSteinbergIdeal k).ringCon.toAddCon.lift
    (TensorAlgebra.liftHomogeneous hs.toMultilinear).toAddMonoidHom (by
      intro x y hxy
      change TensorAlgebra.liftHomogeneous hs.toMultilinear x =
        TensorAlgebra.liftHomogeneous hs.toMultilinear y
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact hs.liftHomogeneous_eq_zero_of_mem
        (((milnorKSteinbergIdeal k).rel_iff x y).mp hxy))

/-- A genuine symbol map extends to an integer-linear map from the native homogeneous group. -/
def lift : MilnorKTheory k n →ₗ[ℤ] A :=
  ((quotientAddHom hs).comp (milnorKGrading k n).subtype).toIntLinearMap

private theorem mk_tprod (a : Fin n → kˣ) :
    (milnorKSteinbergIdeal k).ringCon.mk'
      (TensorAlgebra.tprod ℤ (Additive kˣ) n (Additive.ofMul ∘ a)) =
        milnorKSymbolProd k (List.ofFn a) := by
  simp [TensorAlgebra.tprod_apply, milnorKSymbolProd, milnorKSymbol,
    List.map_ofFn, Function.comp_def, map_list_prod]

/-- Quotient descent retains exactly the prescribed ordered tuple values. -/
@[simp] theorem lift_symbol (a : Fin n → kˣ) : hs.lift (milnorKTupleSymbol a) = s a := by
  change (quotientAddHom hs) (milnorKSymbolProd k (List.ofFn a)) = s a
  rw [← mk_tprod]
  change TensorAlgebra.liftHomogeneous hs.toMultilinear
    (TensorAlgebra.tprod ℤ (Additive kˣ) n (Additive.ofMul ∘ a)) = s a
  rw [TensorAlgebra.liftHomogeneous_tprod, toMultilinear_apply]
  rfl

include hs in
/-- Every genuine symbol map has a unique integer-linear extension in every nonnegative degree. -/
theorem existsUnique_lift :
    ∃! f : MilnorKTheory k n →ₗ[ℤ] A, ∀ a : Fin n → kˣ, f (milnorKTupleSymbol a) = s a := by
  refine ⟨hs.lift, hs.lift_symbol, ?_⟩
  intro f hf
  apply milnorKTheory_linearMap_ext
  intro a
  exact (hf a).trans (hs.lift_symbol a).symm

end IsMilnorKSymbolMap

attribute [colib_tag "COL-0042"] IsMilnorKSymbolMap.lift IsMilnorKSymbolMap.lift_symbol
  IsMilnorKSymbolMap.existsUnique_lift

add_to_stacks 0EAY
  "Construction background only: homogeneous descent through the native tensor Steinberg quotient"
  IsMilnorKSymbolMap.lift
add_to_stacks 0EAY
  "Derived universal property; the tag defines the quotient but does not state this exact theorem"
  IsMilnorKSymbolMap.existsUnique_lift
