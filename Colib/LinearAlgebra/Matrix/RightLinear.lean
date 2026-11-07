/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/Aglib/LinearAlgebra/Matrix/RightLinear.lean`.
The original hypotheses and maps are retained.

# Matrices acting on finite free right modules

For an arbitrary ring, left multiplication by a matrix is linear on right
modules, represented as modules over the opposite ring. Recovering the matrix
from the images of the standard vectors gives an explicit equivalence. Matrix
multiplication corresponds to composition in the original order.
-/
@[expose] public section

noncomputable section

universe u v w

namespace Matrix.RightModule

open Matrix

variable {R : Type u} [Ring R]

/-- The right regular module is free, via the explicit opposite linear equivalence. -/
instance rightRegular_free : Module.Free Rᵐᵒᵖ R :=
  Module.Free.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm

instance rightRegular_finite : Module.Finite Rᵐᵒᵖ R :=
  Module.Finite.equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm

variable {n : Type v} {m : Type w} [Fintype n]

/-- Ordinary matrix multiplication on column vectors is right-module linear. -/
def linearMap (A : Matrix m n R) : (n → R) →ₗ[Rᵐᵒᵖ] (m → R) :=
  Matrix.mulVecBilin R Rᵐᵒᵖ A

@[simp] lemma linearMap_apply (A : Matrix m n R) (x : n → R) :
    linearMap A x = A *ᵥ x := rfl

variable [DecidableEq n]

/-- Recover the entries from the images of the standard column vectors. -/
def ofLinearMap (f : (n → R) →ₗ[Rᵐᵒᵖ] (m → R)) : Matrix m n R :=
  Matrix.of fun i j => f (Pi.single j 1) i

@[simp] lemma ofLinearMap_linearMap (A : Matrix m n R) :
    ofLinearMap (linearMap A) = A := by
  ext i j
  simp [ofLinearMap, linearMap, Matrix.mulVec, dotProduct, Pi.single_apply]

@[simp] lemma linearMap_ofLinearMap (f : (n → R) →ₗ[Rᵐᵒᵖ] (m → R)) :
    linearMap (ofLinearMap f) = f := by
  apply LinearMap.ext
  intro x
  have hx : (∑ j, MulOpposite.op (x j) • Pi.single j (1 : R)) = x := by
    ext i
    simp [Pi.single_apply]
  rw [← hx, map_sum, map_sum]
  congr 1
  funext j
  rw [map_smul, map_smul]
  congr 1
  ext i
  simp [linearMap, ofLinearMap, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Matrices are explicitly equivalent to right-module linear maps. -/
def equiv : Matrix m n R ≃ ((n → R) →ₗ[Rᵐᵒᵖ] (m → R)) where
  toFun := linearMap
  invFun := ofLinearMap
  left_inv := ofLinearMap_linearMap
  right_inv := linearMap_ofLinearMap

variable {l : Type*} [Fintype m]

omit [DecidableEq n] in
/-- The order of matrix multiplication is exactly the order of composition. -/
lemma linearMap_mul (A : Matrix l m R) (B : Matrix m n R) :
    linearMap (A * B) = (linearMap A).comp (linearMap B) := by
  apply LinearMap.ext
  intro x
  exact (Matrix.mulVec_mulVec x A B).symm

@[simp] lemma linearMap_one : linearMap (1 : Matrix n n R) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact Matrix.one_mulVec x

/-- Square matrices form the actual endomorphism ring of the right free module. -/
def endRingEquiv : Matrix n n R ≃+* Module.End Rᵐᵒᵖ (n → R) where
  __ := equiv
  map_mul' A B := linearMap_mul A B
  map_add' A B := by
    apply LinearMap.ext
    intro x
    exact Matrix.add_mulVec A B x

end Matrix.RightModule
