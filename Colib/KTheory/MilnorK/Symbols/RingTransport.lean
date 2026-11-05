/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Symbols.Transport

/-!
# Cross-universe transport on the native Milnor ring

The pinned Stacks ring transport has a common-universe signature. Mathlib's tensor-algebra
and congruence lifts extend that same construction directly to fields in independent universes.
The source and target are the existing native quotient rings. On each homogeneous group this
map is the existing `milnorKTheoryMap`; in a common universe it is the native `milnorKRingMap`.
No second quotient, grading, or independently maintained homogeneous map is introduced.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

variable {k : Type u} {K : Type v} [Field k] [Field K]

/-- Cross-universe extension of the native ring transport, by its tensor/quotient universal maps. -/
def milnorKRingMapLift (f : k →+* K) : MilnorKRing k →+* MilnorKRing K := by
  let s : Additive kˣ →ₗ[ℤ] MilnorKRing K := AddMonoidHom.toIntLinearMap
    { toFun a := milnorKSymbol K (Units.map f.toMonoidHom a.toMul)
      map_zero' := by simp
      map_add' a b := by simp }
  let t := TensorAlgebra.lift ℤ s
  refine (milnorKSteinbergIdeal k).ringCon.lift t.toRingHom ?_
  change (milnorKSteinbergIdeal k).ringCon ≤ (TwoSidedIdeal.ker t.toRingHom).ringCon
  rw [← TwoSidedIdeal.ringCon_le_iff]
  apply TwoSidedIdeal.span_le.mpr
  intro x hx
  apply (TwoSidedIdeal.mem_ker t.toRingHom).mpr
  obtain ⟨a, rfl⟩ := hx
  change t (_ * _) = 0
  simp only [map_mul, t, TensorAlgebra.lift_ι_apply]
  apply milnorKSymbol_mul_steinberg
  change f a.1 + f (1 - a.1) = 1
  rw [← map_add, add_sub_cancel, map_one]

/-- Cross-universe ring transport retains the native degree-one symbol formula. -/
@[simp] theorem milnorKRingMapLift_symbol (f : k →+* K) (a : kˣ) :
    milnorKRingMapLift f (milnorKSymbol k a) =
      milnorKSymbol K (Units.map f.toMonoidHom a) :=
  TensorAlgebra.lift_ι_apply _ _

/-- The ring transport maps every ordered list symbol coordinatewise. -/
@[simp] theorem milnorKRingMapLift_symbolProd (f : k →+* K) (l : List kˣ) :
    milnorKRingMapLift f (milnorKSymbolProd k l) =
      milnorKSymbolProd K (l.map (Units.map f.toMonoidHom)) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [milnorKSymbolProd_cons, map_mul, ih]

/-- Restriction to every homogeneous group is exactly the previously constructed field map. -/
theorem milnorKRingMapLift_coe (f : k →+* K) (n : ℕ) (x : MilnorKTheory k n) :
    milnorKRingMapLift f (x : MilnorKRing k) = (milnorKTheoryMap f n x : MilnorKRing K) := by
  have h : (milnorKRingMapLift f).toAddMonoidHom.comp (milnorKGrading k n).subtype =
      (milnorKGrading K n).subtype.comp (milnorKTheoryMap f n).toAddMonoidHom := by
    apply milnorKTheory_addHom_ext
    intro a
    simp [coe_milnorKTupleSymbol, List.map_ofFn, Function.comp_def]
  exact DFunLike.congr_fun h x

/-- In a common universe the universal extension equals Stacks' original ring map. -/
theorem milnorKRingMapLift_eq {k' : Type u} [Field k'] (f : k →+* k') :
    milnorKRingMapLift f = milnorKRingMap f := by
  apply RingHom.ext
  intro x
  obtain ⟨t, rfl⟩ := milnorKRing_mk'_surjective k x
  induction t using TensorAlgebra.induction with
  | algebraMap r => simp [milnorKRingMapLift]
  | ι a =>
    exact (milnorKRingMapLift_symbol f a.toMul).trans (milnorKRingMap_symbol f a.toMul).symm
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]

end Stacks.Chow

attribute [colib_tag "COL-0111"] Stacks.Chow.milnorKRingMapLift
  Stacks.Chow.milnorKRingMapLift_symbol Stacks.Chow.milnorKRingMapLift_symbolProd
  Stacks.Chow.milnorKRingMapLift_coe Stacks.Chow.milnorKRingMapLift_eq

add_to_stacks 0EAY "Construction consequence: universe-general transport on the native Milnor ring"
  Stacks.Chow.milnorKRingMapLift
