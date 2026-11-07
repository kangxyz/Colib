/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.TorComparison.TopHomology
public import StacksFrontier.RingTheory.Koszul.Augmentation
public import Colib.Algebra.Category.ModuleCat.ChangeOfRings.Quotient

/-!
# Scalar extension of the native Koszul complex

The degreewise exterior-power base-change equivalence preserves the differential,
augmentation coordinate and ordered top generator. No flatness or regularity is
needed. All statements include length zero.

The exterior-power construction and differential identity are those of pinned
Stacks `KoszulC.extPow_baseChange_natEquiv` and `KoszulC.d_baseChange_comm`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace Koszul

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

/-- Exterior-power scalar extension with its canonical multilinear normalization. -/
def seqExteriorBaseChange (n k : ℕ) :
    (A ⊗[R] (⋀[R]^k (Fin n → R))) ≃ₗ[A] (⋀[A]^k (Fin n → A)) :=
  (KoszulC.extPow_baseChange_natEquiv (R := R) (S := A) (r := n) k).choose

@[simp]
theorem seqExteriorBaseChange_ιMulti (k : ℕ) (v : Fin k → Fin n → R) :
    seqExteriorBaseChange (R := R) (A := A) n k (1 ⊗ₜ[R] exteriorPower.ιMulti R k v) =
      exteriorPower.ιMulti A k (fun i j => algebraMap R A (v i j)) :=
  (KoszulC.extPow_baseChange_natEquiv (R := R) (S := A) (r := n) k).choose_spec v

/-- The scalar-extension comparison preserves the ordered top wedge, including the empty wedge. -/
@[simp]
theorem seqExteriorBaseChange_topGen :
    seqExteriorBaseChange (R := R) (A := A) n n (1 ⊗ₜ[R] topGen R n) = topGen A n := by
  rw [topGen, seqExteriorBaseChange_ιMulti, topGen]
  congr 1
  funext i j
  simp [Pi.basisFun_apply, Pi.single_apply]

/-- The standard top coordinate after scalar extension on a pure tensor. -/
theorem seqExteriorBaseChange_topEquiv (a : A) (x : ⋀[R]^n (Fin n → R)) :
    topEquiv A n (seqExteriorBaseChange (R := R) (A := A) n n (a ⊗ₜ[R] x)) =
      a * algebraMap R A (topEquiv R n x) := by
  conv_lhs => rw [eq_smul_topGen x]
  rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul A,
    map_smul, map_smul]
  have ha : a ⊗ₜ[R] topGen R n = a • (1 ⊗ₜ[R] topGen R n) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ha, map_smul, seqExteriorBaseChange_topGen, map_smul, topEquiv_topGen]
  simp [mul_comm]

/-- The degree-zero coordinate is the scalar extension of the original coefficient. -/
theorem seqExteriorBaseChange_zeroEquiv (a : A) (x : ⋀[R]^0 (Fin n → R)) :
    exteriorPower.zeroEquiv A (Fin n → A)
      (seqExteriorBaseChange (R := R) (A := A) n 0 (a ⊗ₜ[R] x)) =
      a * algebraMap R A (exteriorPower.zeroEquiv R (Fin n → R) x) := by
  let b : ⋀[R]^0 (Fin n → R) := exteriorPower.ιMulti R 0 Fin.elim0
  have hx : x = (exteriorPower.zeroEquiv R (Fin n → R) x) • b := by
    apply (exteriorPower.zeroEquiv R (Fin n → R)).injective
    simp [b]
  rw [hx, TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul A,
    map_smul, map_smul]
  have ha : a ⊗ₜ[R] b = a • (1 ⊗ₜ[R] b) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ha, map_smul]
  simp [b, mul_comm]

/-- Scalar extension intertwines the actual Koszul differentials. -/
theorem seqExteriorBaseChange_d (f : Fin n → R) (k : ℕ)
    (a : A) (x : ⋀[R]^(k + 1) (Fin n → R)) :
    seqExteriorBaseChange (R := R) (A := A) n k (a ⊗ₜ[R] d (seqDual f) k x) =
      d (seqDual (fun i => algebraMap R A (f i))) k
        (seqExteriorBaseChange (R := R) (A := A) n (k + 1) (a ⊗ₜ[R] x)) := by
  have ht {j : ℕ} (y : ⋀[R]^j (Fin n → R)) : a ⊗ₜ[R] y = a • (1 ⊗ₜ[R] y) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ht, ht, map_smul, map_smul, map_smul]
  congr 1
  exact KoszulC.d_baseChange_comm f (seqExteriorBaseChange n)
    (fun j v => seqExteriorBaseChange_ιMulti j v) k x

set_option backward.isDefEq.respectTransparency false in
/-- The actual scalar-extended Koszul chain complex is the native Koszul complex over `A`. -/
def seqComplexBaseChangeIso (f : Fin n → R) :
    ((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex (.down ℕ)).obj
      (seqComplex f) ≅ seqComplex (fun i => algebraMap R A (f i)) := by
  letI : Algebra R A := (algebraMap R A).toAlgebra
  exact HomologicalComplex.Hom.isoOfComponents
    (fun k => (seqExteriorBaseChange (R := R) (A := A) n k).toModuleIso)
    (by
      intro i j hij
      obtain rfl : j + 1 = i := hij
      rw [Functor.mapHomologicalComplex_obj_d, seqComplex_d, seqComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a x => exact (seqExteriorBaseChange_d (R := R) (A := A) f j a x).symm
      | add x y hx hy => simp only [map_add, hx, hy])

/-- The scalar-extended sequence quotient, with its literal mapped sequence as target. -/
def seqQuotientBaseChangeIso (f : Fin n → R) :
    (ModuleCat.extendScalars (algebraMap R A)).obj
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) ≅
        ModuleCat.of A (A ⧸ Ideal.span (Set.range (fun i => algebraMap R A (f i)))) :=
  ModuleCat.extendScalarsQuotientIso (A := A) (Ideal.span (Set.range f)) ≪≫
    (Ideal.quotientEquivAlgOfEq A
      (ModuleCat.map_span_range_algebraMap (A := A) f)).toLinearEquiv.toModuleIso

@[simp]
theorem seqQuotientBaseChangeIso_hom_tmul (f : Fin n → R) (a : A) (r : R) :
    (seqQuotientBaseChangeIso (A := A) f).hom
      (a ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range f)) r) =
        Ideal.Quotient.mk (Ideal.span (Set.range (fun i => algebraMap R A (f i))))
          (algebraMap R A r * a) := by
  change Ideal.quotientEquivAlgOfEq A (ModuleCat.map_span_range_algebraMap (A := A) f)
    ((ModuleCat.extendScalarsQuotientIso (A := A) _).hom (a ⊗ₜ[R] Ideal.Quotient.mk _ r)) = _
  rw [ModuleCat.extendScalarsQuotientIso_hom_tmul, Ideal.quotientEquivAlgOfEq_mk]

/-- The degree-zero chain comparison commutes with the literal quotient augmentation. -/
theorem seqComplexBaseChangeIso_augmentation (f : Fin n → R) :
    (seqComplexBaseChangeIso (A := A) f).hom.f 0 ≫
        (koszulAugmentation (fun i => algebraMap R A (f i))).f 0 =
      (ModuleCat.extendScalars (algebraMap R A)).map ((koszulAugmentation f).f 0) ≫
        (seqQuotientBaseChangeIso (A := A) f).hom := by
  let : Algebra R A := (algebraMap R A).toAlgebra
  rw [koszulAugmentation_f_zero, koszulAugmentation_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    change Ideal.Quotient.mk _ (exteriorPower.zeroEquiv A (Fin n → A)
      (seqExteriorBaseChange (R := R) (A := A) n 0 (a ⊗ₜ[R] x))) =
    (seqQuotientBaseChangeIso (A := A) f).hom
      (a ⊗ₜ[R] Ideal.Quotient.mk _ (exteriorPower.zeroEquiv R (Fin n → R) x))
    rw [seqQuotientBaseChangeIso_hom_tmul, seqExteriorBaseChange_zeroEquiv, mul_comm]

/-- Scalar extension preserves the literal top-coordinate cocycle of every coefficient. -/
theorem seqComplexBaseChangeIso_topCocycle (f : Fin n → R) (N : ModuleCat.{u} R) (m : N) :
    (seqComplexBaseChangeIso (A := A) f).hom.f n ≫
      (topEquiv A n).toModuleIso.hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton A
          ((ModuleCat.extendScalars (algebraMap R A)).obj N)
          ((1 : A) ⊗ₜ[R, algebraMap R A] m)) =
    (ModuleCat.extendScalars (algebraMap R A)).map
      ((topEquiv R n).toModuleIso.hom ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R N m)) := by
  let : Algebra R A := (algebraMap R A).toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    change topEquiv A n (seqExteriorBaseChange (R := R) (A := A) n n (a ⊗ₜ[R] x)) •
      ((1 : A) ⊗ₜ[R] m) = a ⊗ₜ[R] (topEquiv R n x • m)
    rw [seqExteriorBaseChange_topEquiv, TensorProduct.tmul_smul,
      ← IsScalarTower.algebraMap_smul A]
    simp [TensorProduct.smul_tmul', mul_comm]
    rfl

end Koszul
