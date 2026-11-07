/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.GroupTheory.StableGeneralLinear.QuotientInvariance
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
Implementation provenance: `Quillen/Algebra/Group/StableFieldDeterminant.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native mathematical owners replace the
source namespaces; the original comparisons, representatives, and hypotheses are retained.

# Determinants of stable matrices over fields

The finite determinants induce `det` on the actual stable general linear group
of any commutative ring, and `quotientDet` on its actual elementary quotient.
Both retain their finite-matrix values and commute with change of rings.

Over every field, `finiteClass_eq_unitClass_det` reduces the quotient class of a
matrix to its rank-one determinant class. Its proof uses transvection elimination
and the block-sum formula for the existing stable quotient. Consequently `ker_det`
identifies the kernel with the existing stable elementary subgroup, and
`quotientDetEquiv` identifies the existing elementary quotient with the field's
units. All ranks, including zero, and all field cardinalities are included.
-/
@[expose] public section

noncomputable section

universe u

namespace StableGeneralLinear

variable (R : Type u) [CommRing R]

/-- Finite determinants are invariant under one stabilization. -/
lemma finiteDet_step (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup.det (step R n g) = Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R))) = Matrix.det g.val
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- Finite determinants are invariant under every finite-rank transition. -/
lemma finiteDet_transition {n m : ℕ} (h : n ≤ m) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup.det (transition R n m h g) =
      Matrix.GeneralLinearGroup.det g := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le m h ih =>
    rw [transition_step R h g, finiteDet_step, ih]

/-- The determinant of an actual stable matrix over a commutative ring. -/
def det : Group R →* Rˣ :=
  lift R (fun _ => Matrix.GeneralLinearGroup.det) (by
    intro n m h g
    exact (finiteDet_transition R h g).symm)

@[simp] lemma det_of (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    det R (of R n g) = Matrix.GeneralLinearGroup.det g := rfl

@[simp] lemma det_comp_of (n : ℕ) :
    (det R).comp (of R n) = Matrix.GeneralLinearGroup.det := rfl

/-- Stable determinants commute with entrywise change of coefficient rings. -/
lemma det_naturality {S : Type*} [CommRing S] (f : R →+* S) :
    (det S).comp (map f) = (Units.map f.toMonoidHom).comp (det R) := by
  apply hom_ext
  intro n g
  apply Units.ext
  exact (f.map_det g.val).symm

/-- The existing elementary matrix is mathlib's transvection matrix. -/
lemma elementary_matrix_eq_transvection (n : ℕ) (i j : Fin n) (a : R) :
    (1 + Matrix.single i j a) = Matrix.transvection i j a := rfl

lemma det_elementary_unit (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : R) :
    det R (of R n (Matrix.GeneralLinearGroup.elementary i j hij a)) = 1 := by
  apply Units.ext
  exact Matrix.det_transvection_of_ne i j hij a

/-- Every actual stable elementary matrix has determinant one. -/
lemma elementary_le_ker_det : elementary R ≤ (det R).ker := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨n, i, j, hij, a, rfl⟩
  exact det_elementary_unit R n i j hij a

/-- The determinant descended to the actual stable elementary quotient. -/
def quotientDet : ElementaryQuotient R →* Rˣ := quotientLift R (det R)

@[simp] lemma quotientDet_quotientMap (g : Group R) :
    quotientDet R (quotientMap R g) = det R g := rfl

/-- Determinants on the actual elementary quotients commute with ring maps. -/
lemma quotientDet_naturality {S : Type*} [CommRing S] (f : R →+* S) :
    (quotientDet S).comp (quotientRingMap f) =
      (Units.map f.toMonoidHom).comp (quotientDet R) := by
  apply quotient_hom_ext
  intro g
  exact DFunLike.congr_fun (det_naturality R f) g

/-- A unit gives a rank-one stable matrix, providing a section of the determinant. -/
def unitSection : Rˣ →* Group R :=
  (of R 1).comp (Matrix.GeneralLinearGroup.scalar (Fin 1))

@[simp] lemma det_unitSection (a : Rˣ) : det R (unitSection R a) = a := by
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) a) = a
  simp

lemma det_surjective : Function.Surjective (det R) := fun a =>
  ⟨unitSection R a, det_unitSection R a⟩

/-- The actual stable quotient class of a rank-one unit matrix. -/
def unitClass : Rˣ →* ElementaryQuotient R :=
  (quotientMap R).comp (unitSection R)

@[simp] lemma quotientDet_unitClass (a : Rˣ) :
    quotientDet R (unitClass R a) = a := by
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) a) = a
  simp

private def diagonalUnit {n : ℕ} (d : Fin n → Rˣ) : Matrix.GeneralLinearGroup (Fin n) R where
  val := Matrix.diagonal (fun i => (d i).val)
  inv := Matrix.diagonal (fun i => (d i).inv)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

private lemma diagonalUnit_succ (n : ℕ) (d : Fin (n + 1) → Rˣ) :
    diagonalUnit R d = (Units.mapEquiv (Matrix.reindexRingEquiv R finSumFinEquiv).toMulEquiv)
      (Matrix.GeneralLinearGroup.blockSum (diagonalUnit R (fun i => d i.castSucc))
        (Matrix.GeneralLinearGroup.scalar (Fin 1) (d (Fin.last n)))) := by
  apply Units.ext
  ext i j
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp [diagonalUnit, Matrix.GeneralLinearGroup.blockSum,
      Matrix.reindexRingEquiv, Matrix.reindex_apply, Matrix.diagonal_apply,
      Matrix.GeneralLinearGroup.scalar, eq_comm]

private lemma finiteClass_diagonalUnit (n : ℕ) (d : Fin n → Rˣ) :
    finiteClass R n (diagonalUnit R d) = unitClass R (∏ i, d i) := by
  induction n with
  | zero =>
    have h : diagonalUnit R d = 1 := by
      apply Units.ext
      ext i
      exact i.elim0
    simp [h]
  | succ n ih =>
    rw [diagonalUnit_succ, finiteClass_blockSum, ih, Fin.prod_univ_castSucc, map_mul]
    rfl

section Field

variable (F : Type u) [Field F]

/-- Over a field, every original finite matrix class is its rank-one determinant class. -/
lemma finiteClass_eq_unitClass_det (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) F) :
    finiteClass F n g = unitClass F (Matrix.GeneralLinearGroup.det g) := by
  let P : Matrix (Fin n) (Fin n) F → Prop := fun M =>
    ∀ a : Matrix.GeneralLinearGroup (Fin n) F, a.val = M →
      finiteClass F n a = unitClass F (Matrix.GeneralLinearGroup.det a)
  have hP : P g.val := by
    apply Matrix.diagonal_transvection_induction_of_det_ne_zero P g.val
      (Matrix.GeneralLinearGroup.det_ne_zero g)
    · intro D hD a ha
      have hne (i : Fin n) : D i ≠ 0 := by
        rw [Matrix.det_diagonal] at hD
        exact (Finset.prod_ne_zero_iff.mp hD) i (Finset.mem_univ i)
      let d : Fin n → Fˣ := fun i => Units.mk0 (D i) (hne i)
      have hea : a = diagonalUnit F d := Units.ext ha
      rw [hea, finiteClass_diagonalUnit]
      congr 1
      apply Units.ext
      simp [diagonalUnit, Matrix.GeneralLinearGroup.det]
    · intro t a ha
      have hea : a = Matrix.GeneralLinearGroup.elementary t.i t.j t.hij t.c := Units.ext ha
      rw [hea]
      have hq : finiteClass F n (Matrix.GeneralLinearGroup.elementary t.i t.j t.hij t.c) = 1 :=
        (quotientMap_eq_one F _).mpr (unit_mem_elementary F n t.i t.j t.hij t.c)
      have hd : Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.elementary t.i t.j t.hij t.c) = 1 :=
        det_elementary_unit F n t.i t.j t.hij t.c
      rw [hq, hd, map_one]
    · intro A B hA hB hPA hPB a ha
      let aA := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
      let aB := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB
      have hea : a = aA * aB := Units.ext ha
      rw [hea, map_mul, map_mul, hPA aA rfl, hPB aB rfl, map_mul]
  exact hP g rfl

/-- Every class in the actual field quotient is represented by its determinant. -/
lemma unitClass_quotientDet (x : ElementaryQuotient F) :
    unitClass F (quotientDet F x) = x := by
  obtain ⟨a, rfl⟩ := quotientMap_surjective F x
  obtain ⟨n, g, rfl⟩ := exists_of F a
  exact (finiteClass_eq_unitClass_det F n g).symm

/-- Over every field, the actual stable determinant has the actual elementary kernel. -/
theorem ker_det : (det F).ker = elementary F := by
  apply le_antisymm _ (elementary_le_ker_det F)
  intro g hg
  apply (quotientMap_eq_one F g).mp
  rw [← unitClass_quotientDet F (quotientMap F g), quotientDet_quotientMap]
  rw [MonoidHom.mem_ker.mp hg, map_one]

/-- The determinant equivalence on the actual stable elementary quotient of a field. -/
def quotientDetEquiv : ElementaryQuotient F ≃* Fˣ :=
  { quotientDet F with
    invFun := unitClass F
    left_inv := unitClass_quotientDet F
    right_inv := quotientDet_unitClass F }

@[simp] lemma quotientDetEquiv_quotientMap (g : Group F) :
    quotientDetEquiv F (quotientMap F g) = det F g := rfl

@[simp] lemma quotientDetEquiv_of (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) F) :
    quotientDetEquiv F (quotientMap F (of F n g)) = Matrix.GeneralLinearGroup.det g := rfl

/-- The field determinant equivalences retain the original change-of-rings square. -/
lemma quotientDetEquiv_naturality {K : Type*} [Field K] (f : F →+* K) :
    (quotientDetEquiv K).toMonoidHom.comp (quotientRingMap f) =
      (Units.map f.toMonoidHom).comp (quotientDetEquiv F).toMonoidHom := by
  apply quotient_hom_ext
  intro g
  exact DFunLike.congr_fun (det_naturality F f) g

end Field

end StableGeneralLinear
