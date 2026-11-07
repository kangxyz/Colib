/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.RightLinear

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/Aglib/LinearAlgebra/Matrix/RightScalarExtension.lean`.
The original hypotheses and maps are retained.

# Scalar extension of finite free right modules

For an arbitrary ring homomorphism, entrywise change of coefficients is the
universal semilinear map from a finite free right module to a right module over
the target ring. The extension is the explicit sum of the images of the standard
vectors with their right coefficients. The construction retains the original
rectangular-matrix actions and is natural in every target-module linear map.

All modules are left modules over opposite rings. The rings, finite index types,
and ambient target modules may have independent universes. No commutativity,
flatness, nontriviality, or invariant-basis-number hypothesis is used.
-/
@[expose] public section

noncomputable section

universe u v w a b

namespace Matrix.RightModule

open MulOpposite

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable {n : Type a} {m : Type b}

/-- The canonical semilinear unit changes every coordinate by the given ring map. -/
def coordinateBaseChange (f : R →+* S) : (n → R) →ₛₗ[f.op] (n → S) where
  toFun x i := f (x i)
  map_add' x y := by ext i; exact f.map_add (x i) (y i)
  map_smul' r x := by
    ext i
    change f (x i * unop r) = f (x i) * f (unop r)
    exact f.map_mul _ _

@[simp] lemma coordinateBaseChange_apply (f : R →+* S) (x : n → R) (i : n) :
    coordinateBaseChange f x i = f (x i) := rfl

/-- Entrywise scalar extension commutes with every original rectangular matrix. -/
lemma coordinateBaseChange_linearMap [Fintype n] (f : R →+* S)
    (A : Matrix m n R) (x : n → R) :
    coordinateBaseChange f (linearMap A x) =
      linearMap (A.map f) (coordinateBaseChange f x) := by
  ext i
  simp [linearMap_apply, Matrix.mulVec, dotProduct]

variable [Fintype n] [DecidableEq n]

omit [Fintype n] in
@[simp] lemma coordinateBaseChange_single (f : R →+* S) (i : n) (r : R) :
    coordinateBaseChange f (Pi.single i r) = Pi.single i (f r) := by
  ext j
  by_cases h : i = j <;> simp [h]

/-- Every right-module vector is the sum of its standard vectors with right coefficients. -/
lemma sum_standard_right (x : n → R) :
    (∑ i, op (x i) • Pi.single i (1 : R)) = x := by
  ext j
  simp [Pi.single_apply]

variable {N : Type w} [AddCommGroup N] [Module Sᵐᵒᵖ N]

/-- Extend a semilinear map by its values on the standard vectors. -/
def extendSemilinear (f : R →+* S) (h : (n → R) →ₛₗ[f.op] N) :
    (n → S) →ₗ[Sᵐᵒᵖ] N where
  toFun y := ∑ i, op (y i) • h (Pi.single i 1)
  map_add' y z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' s y := by
    simp [Pi.smul_apply, MulOpposite.smul_eq_mul_unop, op_mul, mul_smul, Finset.smul_sum]

@[simp] lemma extendSemilinear_apply (f : R →+* S)
    (h : (n → R) →ₛₗ[f.op] N) (y : n → S) :
    extendSemilinear f h y = ∑ i, op (y i) • h (Pi.single i 1) := rfl

/-- The extension recovers the prescribed semilinear map on the canonical unit. -/
lemma extendSemilinear_coordinateBaseChange (f : R →+* S)
    (h : (n → R) →ₛₗ[f.op] N) (x : n → R) :
    extendSemilinear f h (coordinateBaseChange f x) = h x := by
  conv_rhs => rw [← sum_standard_right x]
  simp [extendSemilinear, map_sum, map_smulₛₗ]

/-- Precomposing an extension with the canonical unit is exactly the original map. -/
@[simp] lemma extendSemilinear_comp_coordinateBaseChange (f : R →+* S)
    (h : (n → R) →ₛₗ[f.op] N) :
    (extendSemilinear f h).comp (coordinateBaseChange f) = h := by
  ext x
  exact extendSemilinear_coordinateBaseChange f h x

/-- Extending the restriction of a linear map returns that original linear map. -/
@[simp] lemma extendSemilinear_restrict (f : R →+* S)
    (g : (n → S) →ₗ[Sᵐᵒᵖ] N) :
    extendSemilinear f (g.comp (coordinateBaseChange f)) = g := by
  apply LinearMap.ext
  intro y
  change (∑ i, op (y i) • g (coordinateBaseChange f (Pi.single i 1))) = g y
  simp only [coordinateBaseChange_single, map_one]
  simp only [← map_smul]
  rw [← map_sum, sum_standard_right]

/-- The actual finite free scalar-extension universal property, additive on Hom groups. -/
def freeScalarExtensionEquiv (f : R →+* S) :
    ((n → S) →ₗ[Sᵐᵒᵖ] N) ≃+ ((n → R) →ₛₗ[f.op] N) where
  toFun g := g.comp (coordinateBaseChange f)
  invFun := extendSemilinear f
  left_inv := extendSemilinear_restrict f
  right_inv := extendSemilinear_comp_coordinateBaseChange f
  map_add' _ _ := rfl

@[simp] lemma freeScalarExtensionEquiv_apply (f : R →+* S)
    (g : (n → S) →ₗ[Sᵐᵒᵖ] N) :
    freeScalarExtensionEquiv f g = g.comp (coordinateBaseChange f) := rfl

@[simp] lemma freeScalarExtensionEquiv_symm_apply (f : R →+* S)
    (h : (n → R) →ₛₗ[f.op] N) :
    (freeScalarExtensionEquiv f).symm h = extendSemilinear f h := rfl

omit [Fintype n] [DecidableEq n] in
/-- A linear map out of the target free module is determined by its original unit values. -/
lemma freeScalarExtension_hom_ext [Finite n] (f : R →+* S)
    {g k : (n → S) →ₗ[Sᵐᵒᵖ] N}
    (h : g.comp (coordinateBaseChange f) = k.comp (coordinateBaseChange f)) : g = k := by
  classical
  let := Fintype.ofFinite n
  exact (freeScalarExtensionEquiv f).injective h

/-- Uniqueness of the actual linear extension. -/
lemma extendSemilinear_unique (f : R →+* S) (h : (n → R) →ₛₗ[f.op] N)
    (g : (n → S) →ₗ[Sᵐᵒᵖ] N) (hg : g.comp (coordinateBaseChange f) = h) :
    g = extendSemilinear f h := by
  apply freeScalarExtension_hom_ext f
  simpa only [extendSemilinear_comp_coordinateBaseChange] using hg

/-- Scalar extension is natural under every linear map between ambient target modules. -/
lemma extendSemilinear_postcomp {N' : Type*} [AddCommGroup N'] [Module Sᵐᵒᵖ N']
    (f : R →+* S) (h : (n → R) →ₛₗ[f.op] N) (g : N →ₗ[Sᵐᵒᵖ] N') :
    extendSemilinear f (g.comp h) = g.comp (extendSemilinear f h) := by
  apply freeScalarExtension_hom_ext f
  apply LinearMap.ext
  intro x
  change extendSemilinear f (g.comp h) (coordinateBaseChange f x) =
    g (extendSemilinear f h (coordinateBaseChange f x))
  simp only [extendSemilinear_coordinateBaseChange, LinearMap.comp_apply]

/-- The Hom equivalence is natural under every linear map of target modules. -/
lemma freeScalarExtensionEquiv_postcomp {N' : Type*} [AddCommGroup N']
    [Module Sᵐᵒᵖ N'] (f : R →+* S) (h : (n → S) →ₗ[Sᵐᵒᵖ] N)
    (g : N →ₗ[Sᵐᵒᵖ] N') :
    freeScalarExtensionEquiv f (g.comp h) = g.comp (freeScalarExtensionEquiv f h) := rfl

omit [DecidableEq n] in
/-- The canonical unit square as an equality of semilinear maps. -/
lemma coordinateBaseChange_comp_linearMap (f : R →+* S) (A : Matrix m n R) :
    (coordinateBaseChange f).comp (linearMap A) =
      (linearMap (A.map f)).comp (coordinateBaseChange f) := by
  apply LinearMap.ext
  intro x
  exact coordinateBaseChange_linearMap f A x

variable [Fintype m] [DecidableEq m]

/-- The universal extension retains every rectangular matrix, with its original orientation. -/
lemma extendSemilinear_precomp_matrix (f : R →+* S) (A : Matrix m n R)
    (h : (m → R) →ₛₗ[f.op] N) :
    extendSemilinear f (h.comp (linearMap A)) =
      (extendSemilinear f h).comp (linearMap (A.map f)) := by
  apply freeScalarExtension_hom_ext f
  ext x
  simp only [LinearMap.comp_apply, extendSemilinear_coordinateBaseChange]
  rw [← coordinateBaseChange_linearMap, extendSemilinear_coordinateBaseChange]

/-- The Hom equivalence is natural in the actual rectangular-matrix maps. -/
lemma freeScalarExtensionEquiv_precomp_matrix (f : R →+* S) (A : Matrix m n R)
    (g : (m → S) →ₗ[Sᵐᵒᵖ] N) :
    freeScalarExtensionEquiv f (g.comp (linearMap (A.map f))) =
      (freeScalarExtensionEquiv f g).comp (linearMap A) := by
  ext x
  change g (linearMap (A.map f) (coordinateBaseChange f x)) =
    g (coordinateBaseChange f (linearMap A x))
  rw [coordinateBaseChange_linearMap]

end Matrix.RightModule
