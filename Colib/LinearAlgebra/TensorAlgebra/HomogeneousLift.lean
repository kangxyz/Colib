/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
# Linear extension from a fixed tensor degree

A multilinear map on `n` vectors extends linearly to the tensor algebra by setting its values
in every other degree to zero. This uses the native equivalence with the direct sum of tensor
powers and the universal property of `PiTensorProduct`; no presentation is reconstructed.

The intended consumer is quotient descent for homogeneous Milnor symbol maps. The quotient's
ideal-annihilation condition is a separate proof obligation, not an assumption silently supplied
by this construction.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

namespace TensorAlgebra

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {n : ℕ}

/-- Ordered tensors multiply by concatenating their tuples. -/
theorem tprod_append {m n : ℕ} (a : Fin m → M) (b : Fin n → M) :
    tprod R M (m + n) (Fin.append a b) = tprod R M m a * tprod R M n b := by
  simp only [tprod_apply, List.ofFn_comp', List.ofFn_fin_append, List.map_append,
    List.prod_append]

/-- Extend a multilinear map to the tensor algebra, with zero on all other tensor degrees. -/
def liftHomogeneous (f : MultilinearMap R (fun _ : Fin n => M) N) :
    TensorAlgebra R M →ₗ[R] N :=
  (PiTensorProduct.lift f).comp
    ((DirectSum.component R ℕ (fun i => TensorPower R i M) n).comp
      (TensorAlgebra.toDirectSum.toLinearMap))

/-- The homogeneous extension retains the prescribed value on a tensor of the chosen degree. -/
theorem liftHomogeneous_tprod (f : MultilinearMap R (fun _ : Fin n => M) N)
    (a : Fin n → M) : liftHomogeneous f (tprod R M n a) = f a := by
  simp only [liftHomogeneous, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    toDirectSum_tensorPower_tprod]
  change PiTensorProduct.lift f
    ((DirectSum.of (fun i => TensorPower R i M) n (PiTensorProduct.tprod R a)) n) = f a
  rw [DirectSum.of_eq_same, PiTensorProduct.lift.tprod]

/-- The homogeneous extension is zero on a pure tensor of any other degree. -/
theorem liftHomogeneous_tprod_of_ne (f : MultilinearMap R (fun _ : Fin n => M) N)
    {m : ℕ} (hmn : m ≠ n) (a : Fin m → M) :
    liftHomogeneous f (tprod R M m a) = 0 := by
  simp only [liftHomogeneous, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    toDirectSum_tensorPower_tprod]
  change PiTensorProduct.lift f
    ((DirectSum.of (fun i => TensorPower R i M) m (PiTensorProduct.tprod R a)) n) = 0
  rw [DirectSum.of_eq_of_ne _ _ _ hmn.symm, map_zero]

/-- Linear maps from the tensor algebra agree if they agree on ordered tensors of every degree. -/
theorem linearMap_ext_tprod (f g : TensorAlgebra R M →ₗ[R] N)
    (h : ∀ (n : ℕ) (a : Fin n → M), f (tprod R M n a) = g (tprod R M n a)) : f = g := by
  have hcomp : f.comp TensorAlgebra.ofDirectSum.toLinearMap =
      g.comp TensorAlgebra.ofDirectSum.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro n
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      DirectSum.lof_eq_of, AlgHom.toLinearMap_apply,
      ofDirectSum_of_tprod] using h n a
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hcomp (TensorAlgebra.toDirectSum x)
  simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, ofDirectSum_toDirectSum] using hx

/-- The homogeneous extension is the unique linear map with the prescribed pure-tensor values. -/
theorem liftHomogeneous_unique (f : MultilinearMap R (fun _ : Fin n => M) N)
    (g : TensorAlgebra R M →ₗ[R] N) (hn : ∀ a, g (tprod R M n a) = f a)
    (hother : ∀ (m : ℕ), m ≠ n → ∀ a, g (tprod R M m a) = 0) :
    g = liftHomogeneous f := by
  apply linearMap_ext_tprod
  intro m a
  by_cases hmn : m = n
  · subst m
    rw [liftHomogeneous_tprod, hn]
  · rw [liftHomogeneous_tprod_of_ne f hmn, hother m hmn]

end TensorAlgebra
