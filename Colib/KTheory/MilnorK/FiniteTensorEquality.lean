/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.FreeAlgebra.Map
public import Colib.KTheory.MilnorK.FiniteTensorDescent
import all Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# Finite-stage equality in the native Milnor tensor algebra

An equality between tensors from a finite intermediate field, after mapping
to an algebraic extension, already holds after a finite enlargement. The proof
descends the actual `RingConGen.Rel` derivation defining Mathlib's tensor
algebra. Injectivity is used only before quotienting, on `FreeAlgebra`.

The implementation import exposes only the existing native tensor congruence
for this proof. Public statements use the original tensors and field maps.
Local notation below expands to native types, lifts, and quotient maps; it
introduces no new presentation or transport declaration.
-/

@[expose] public noncomputable section

universe u v

local notation "A[" K "]" => FreeAlgebra ℤ (Additive Kˣ)
local notation "F[" φ "]" =>
  FreeAlgebra.lift ℤ (FreeAlgebra.ι ℤ ∘ milnorKUnitsMap φ)
local notation "Q[" K "]" =>
  RingCon.mkₐ ℤ (TensorAlgebra.ringCon ℤ (Additive Kˣ))

private theorem freeMap_injective {K L : Type v} [Field K] [Field L] (φ : K →+* L) :
    Function.Injective F[φ] := by
  apply FreeAlgebra.lift_ι_injective
  intro a b h
  exact Units.map_injective φ.injective h

private theorem quotient_freeMap {K L : Type v} [Field K] [Field L]
    (φ : K →+* L) (x : A[K]) :
    Q[L] (F[φ] x) = milnorKTensorMap φ (Q[K] x) := by
  have h : Q[L].comp F[φ] = (milnorKTensorMap φ).comp Q[K] := by
    apply FreeAlgebra.hom_ext
    funext a
    change Q[L] (F[φ] (FreeAlgebra.ι ℤ a)) =
      milnorKTensorMap φ (Q[K] (FreeAlgebra.ι ℤ a))
    simp only [Function.comp_apply, FreeAlgebra.lift_ι_apply,
      TensorAlgebra.ringQuot_mkAlgHom_freeAlgebra_ι_eq_ι, milnorKTensorMap_ι]
    rfl
  exact DFunLike.congr_fun h x

variable {k : Type u} {E : Type v} [Field k] [Field E] [Algebra k E]

private theorem freeMap_val_inclusion {S T : IntermediateField k E} (h : S ≤ T)
    (x : A[S]) :
    F[T.val.toRingHom] (F[(IntermediateField.inclusion h).toRingHom] x) =
      F[S.val.toRingHom] x := by
  have hcomp : F[T.val.toRingHom].comp F[(IntermediateField.inclusion h).toRingHom] =
      F[S.val.toRingHom] := by
    apply FreeAlgebra.hom_ext
    funext a
    simp only [AlgHom.coe_comp, Function.comp_apply, FreeAlgebra.lift_ι_apply]
    exact congrArg (FreeAlgebra.ι ℤ) (congrArg Additive.ofMul (Units.ext rfl))
  exact DFunLike.congr_fun hcomp x

variable (k E) [Algebra.IsAlgebraic k E]

private theorem exists_finite_freeAlgebra (x : A[E]) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ a : A[S], F[S.val.toRingHom] a = x := by
  induction x using FreeAlgebra.induction with
  | grade0 z =>
      exact ⟨⊥, inferInstance, algebraMap ℤ _ z, by simp only [AlgHom.commutes]⟩
  | grade1 a =>
      obtain ⟨S, hS, b, hb⟩ :=
        IntermediateField.exists_finite_units k E (fun _ : Unit => a.toMul)
      refine ⟨S, hS, FreeAlgebra.ι ℤ (Additive.ofMul (b ())), ?_⟩
      simp only [FreeAlgebra.lift_ι_apply, Function.comp_apply, milnorKUnitsMap_ofMul]
      exact congrArg (fun z : Eˣ => FreeAlgebra.ι ℤ (Additive.ofMul z))
        (congrFun hb ())
  | mul x y hx hy =>
      obtain ⟨S, hS, a, ha⟩ := hx
      obtain ⟨T, hT, b, hb⟩ := hy
      let := hS
      let := hT
      refine ⟨S ⊔ T, inferInstance,
        F[(IntermediateField.inclusion le_sup_left).toRingHom] a *
          F[(IntermediateField.inclusion le_sup_right).toRingHom] b, ?_⟩
      rw [map_mul, freeMap_val_inclusion, freeMap_val_inclusion, ha, hb]
  | add x y hx hy =>
      obtain ⟨S, hS, a, ha⟩ := hx
      obtain ⟨T, hT, b, hb⟩ := hy
      let := hS
      let := hT
      refine ⟨S ⊔ T, inferInstance,
        F[(IntermediateField.inclusion le_sup_left).toRingHom] a +
          F[(IntermediateField.inclusion le_sup_right).toRingHom] b, ?_⟩
      rw [map_add, freeMap_val_inclusion, freeMap_val_inclusion, ha, hb]

private theorem exists_finite_tensorRel {x y : A[E]}
    (h : TensorAlgebra.Rel ℤ (Additive Eˣ) x y) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ a b : A[S], Q[S] a = Q[S] b ∧
        F[S.val.toRingHom] a = x ∧ F[S.val.toRingHom] b = y := by
  cases h with
  | @add a b =>
      obtain ⟨S, hS, c, hc⟩ := IntermediateField.exists_finite_units k E
        (fun j : Bool => match j with | false => a.toMul | true => b.toMul)
      let a' := Additive.ofMul (c false)
      let b' := Additive.ofMul (c true)
      have ha : milnorKUnitsMap S.val.toRingHom a' = a :=
        congrArg Additive.ofMul (congrFun hc false)
      have hb : milnorKUnitsMap S.val.toRingHom b' = b :=
        congrArg Additive.ofMul (congrFun hc true)
      refine ⟨S, hS, FreeAlgebra.ι ℤ (a' + b'),
        FreeAlgebra.ι ℤ a' + FreeAlgebra.ι ℤ b', ?_, ?_, ?_⟩
      · simp only [map_add, TensorAlgebra.ringQuot_mkAlgHom_freeAlgebra_ι_eq_ι]
        rfl
      · simp only [FreeAlgebra.lift_ι_apply, Function.comp_apply, map_add, ha, hb]
      · simp only [map_add, FreeAlgebra.lift_ι_apply, Function.comp_apply, ha, hb]
  | @smul z a =>
      obtain ⟨S, hS, b, hb⟩ :=
        IntermediateField.exists_finite_units k E (fun _ : Unit => a.toMul)
      let a' := Additive.ofMul (b ())
      have ha : milnorKUnitsMap S.val.toRingHom a' = a :=
        congrArg Additive.ofMul (congrFun hb ())
      refine ⟨S, hS, FreeAlgebra.ι ℤ (z • a'),
        algebraMap ℤ A[S] z * FreeAlgebra.ι ℤ a', ?_, ?_, ?_⟩
      · simp only [map_mul, AlgHom.commutes,
          TensorAlgebra.ringQuot_mkAlgHom_freeAlgebra_ι_eq_ι, map_smul,
          Algebra.smul_def]
        rfl
      · simp only [FreeAlgebra.lift_ι_apply, Function.comp_apply, map_smul, ha]
      · simp only [map_mul, AlgHom.commutes, FreeAlgebra.lift_ι_apply,
          Function.comp_apply, ha]

private theorem exists_finite_tensorCongruence {x y : A[E]}
    (h : TensorAlgebra.ringCon ℤ (Additive Eˣ) x y) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ a b : A[S], Q[S] a = Q[S] b ∧
        F[S.val.toRingHom] a = x ∧ F[S.val.toRingHom] b = y := by
  change RingConGen.Rel (TensorAlgebra.Rel ℤ (Additive Eˣ)) x y at h
  induction h with
  | of x y h => exact exists_finite_tensorRel k E h
  | refl x =>
      obtain ⟨S, hS, a, ha⟩ := exists_finite_freeAlgebra k E x
      exact ⟨S, hS, a, a, rfl, ha, ha⟩
  | symm h ih =>
      obtain ⟨S, hS, a, b, hab, ha, hb⟩ := ih
      exact ⟨S, hS, b, a, hab.symm, hb, ha⟩
  | @trans x y z hxy hyz ihxy ihyz =>
      obtain ⟨S, hS, a, b, hab, ha, hb⟩ := ihxy
      obtain ⟨T, hT, c, d, hcd, hc, hd⟩ := ihyz
      let := hS
      let := hT
      let iS := (IntermediateField.inclusion (show S ≤ S ⊔ T from le_sup_left)).toRingHom
      let iT := (IntermediateField.inclusion (show T ≤ S ⊔ T from le_sup_right)).toRingHom
      have hmid : F[iS] b = F[iT] c := by
        apply freeMap_injective (S ⊔ T).val.toRingHom
        rw [freeMap_val_inclusion, freeMap_val_inclusion, hb, hc]
      refine ⟨S ⊔ T, inferInstance, F[iS] a, F[iT] d, ?_, ?_, ?_⟩
      · calc
          Q[↥(S ⊔ T)] (F[iS] a) = Q[↥(S ⊔ T)] (F[iS] b) := by
            rw [quotient_freeMap, quotient_freeMap, hab]
          _ = Q[↥(S ⊔ T)] (F[iT] c) := congrArg Q[↥(S ⊔ T)] hmid
          _ = Q[↥(S ⊔ T)] (F[iT] d) := by
            rw [quotient_freeMap, quotient_freeMap, hcd]
      · rw [freeMap_val_inclusion, ha]
      · rw [freeMap_val_inclusion, hd]
  | add hxy hzw ihxy ihzw =>
      obtain ⟨S, hS, a, b, hab, ha, hb⟩ := ihxy
      obtain ⟨T, hT, c, d, hcd, hc, hd⟩ := ihzw
      let := hS
      let := hT
      let iS := (IntermediateField.inclusion (show S ≤ S ⊔ T from le_sup_left)).toRingHom
      let iT := (IntermediateField.inclusion (show T ≤ S ⊔ T from le_sup_right)).toRingHom
      refine ⟨S ⊔ T, inferInstance, F[iS] a + F[iT] c, F[iS] b + F[iT] d,
        ?_, ?_, ?_⟩
      · simp only [map_add, quotient_freeMap, hab, hcd]
      · rw [map_add, freeMap_val_inclusion, freeMap_val_inclusion, ha, hc]
      · rw [map_add, freeMap_val_inclusion, freeMap_val_inclusion, hb, hd]
  | mul hxy hzw ihxy ihzw =>
      obtain ⟨S, hS, a, b, hab, ha, hb⟩ := ihxy
      obtain ⟨T, hT, c, d, hcd, hc, hd⟩ := ihzw
      let := hS
      let := hT
      let iS := (IntermediateField.inclusion (show S ≤ S ⊔ T from le_sup_left)).toRingHom
      let iT := (IntermediateField.inclusion (show T ≤ S ⊔ T from le_sup_right)).toRingHom
      refine ⟨S ⊔ T, inferInstance, F[iS] a * F[iT] c, F[iS] b * F[iT] d,
        ?_, ?_, ?_⟩
      · simp only [map_mul, quotient_freeMap, hab, hcd]
      · rw [map_mul, freeMap_val_inclusion, freeMap_val_inclusion, ha, hc]
      · rw [map_mul, freeMap_val_inclusion, freeMap_val_inclusion, hb, hd]

/-- Equality of two prescribed tensors from a finite intermediate field,
after extension, is witnessed in a finite enlargement of that same field. -/
theorem exists_finite_milnorKTensor_eq (S : IntermediateField k E)
    [FiniteDimensional k S] (x y : MilnorKTensorAlgebra S)
    (hxy : milnorKTensorMap S.val.toRingHom x = milnorKTensorMap S.val.toRingHom y) :
    ∃ T : IntermediateField k E, FiniteDimensional k T ∧
      ∃ hST : S ≤ T,
        milnorKTensorMap (IntermediateField.inclusion hST).toRingHom x =
          milnorKTensorMap (IntermediateField.inclusion hST).toRingHom y := by
  obtain ⟨a, rfl⟩ :=
    (TensorAlgebra.ringCon ℤ (Additive Sˣ)).mkₐ_surjective (α := ℤ) x
  obtain ⟨b, rfl⟩ :=
    (TensorAlgebra.ringCon ℤ (Additive Sˣ)).mkₐ_surjective (α := ℤ) y
  have hab : TensorAlgebra.ringCon ℤ (Additive Eˣ)
      (F[S.val.toRingHom] a) (F[S.val.toRingHom] b) := by
    apply (TensorAlgebra.ringCon ℤ (Additive Eˣ)).eq.mp
    change Q[E] (F[S.val.toRingHom] a) = Q[E] (F[S.val.toRingHom] b)
    rw [quotient_freeMap, quotient_freeMap]
    exact hxy
  obtain ⟨T, hT, c, d, hcd, hc, hd⟩ := exists_finite_tensorCongruence k E hab
  let := hT
  let iS := (IntermediateField.inclusion (show S ≤ S ⊔ T from le_sup_left)).toRingHom
  let iT := (IntermediateField.inclusion (show T ≤ S ⊔ T from le_sup_right)).toRingHom
  have ha : F[iT] c = F[iS] a := by
    apply freeMap_injective (S ⊔ T).val.toRingHom
    rw [freeMap_val_inclusion, freeMap_val_inclusion, hc]
  have hb : F[iT] d = F[iS] b := by
    apply freeMap_injective (S ⊔ T).val.toRingHom
    rw [freeMap_val_inclusion, freeMap_val_inclusion, hd]
  refine ⟨S ⊔ T, inferInstance, le_sup_left, ?_⟩
  change milnorKTensorMap iS (Q[S] a) = milnorKTensorMap iS (Q[S] b)
  rw [← quotient_freeMap, ← quotient_freeMap, ← ha, ← hb,
    quotient_freeMap, quotient_freeMap, hcd]
