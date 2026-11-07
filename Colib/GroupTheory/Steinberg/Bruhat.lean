/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.GroupTheory.Steinberg.Parabolic

/-!
# Source-word Bruhat coverage in the original defect quotient

The original pivot torus becomes a homomorphism in the quotient by the subgroup C
of original ordered defects. It normalizes the actual old-stage/column parabolic.
The enlarged subgroup B has a torus-times-old-stage-times-column factorization.

Let V be the image of the actual last-row subgroup. `stage_quotient_BVB` proves
that every original word in stage `n+1` belongs to `B * V * B`, for every `n ≥ 2`.
This is a source-word coverage theorem, not an inference from matrix membership.
To prove closure, actual old-stage row transitivity normalizes the first V vector,
nonpivot columns are collected into B, and the proved pivot-pair rank-two result
validates one Gauss identity modulo C. The zero-pivot case uses the literal Weyl
word, whose conjugation sends all remaining row roots into the parabolic.

The quotient is by the original ordered defects throughout. There is no field-size
restriction, larger unstated relation subgroup, or kernel-generation premise.
Kernel detection and the resulting Milnor-map surjectivity are proved separately.

## Implementation provenance

Adapted from `Quillen/Algebra/Group/StableSteinbergBruhat.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The selected native stable group,
elementary units, root generators and canonical maps remain unchanged.
-/
@[expose] public section

noncomputable section
universe u

namespace StableSteinberg.KernelGeneration.TorusParabolic
open RootRelocation Parabolic
open scoped Matrix
variable (F : Type u) [Field F]

/-- The literal finite elementary-matrix product representing the ordered Weyl word. -/
def pairWGL (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) : Matrix.GeneralLinearGroup (Fin n) F :=
  Matrix.GeneralLinearGroup.elementary i j hij (a : F) *
    Matrix.GeneralLinearGroup.elementary j i hij.symm (-((a⁻¹ : Fˣ) : F)) *
      Matrix.GeneralLinearGroup.elementary i j hij (a : F)

/-- The literal finite matrix representing the normalized torus word. -/
def pairHGL (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) : Matrix.GeneralLinearGroup (Fin n) F :=
  pairWGL F n i j hij a * pairWGL F n i j hij (-1)

lemma pairW_image (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    toStableGeneralLinear F (pairW F n i j hij a) =
      StableGeneralLinear.of F n (pairWGL F n i j hij a) := by
  simp only [pairW, pairWGL, map_mul, toStableGeneralLinear_x]

lemma pairH_image (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    toStableGeneralLinear F (pairH F n i j hij a) =
      StableGeneralLinear.of F n (pairHGL F n i j hij a) := by
  simp only [pairH, pairHGL, map_mul, pairW_image]

lemma pairW_mem_stage (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    pairW F n i j hij a ∈ stage F n :=
  (stage F n).mul_mem ((stage F n).mul_mem (x_mem_stage F n i j hij a)
    (x_mem_stage F n j i hij.symm (-((a⁻¹ : Fˣ) : F)))) (x_mem_stage F n i j hij a)

lemma pairH_mem_stage (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    pairH F n i j hij a ∈ stage F n :=
  (stage F n).mul_mem (pairW_mem_stage F n i j hij a) (pairW_mem_stage F n i j hij (-1))

private lemma elementary_mulVec (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) (v : Fin n → F) :
    (Matrix.GeneralLinearGroup.elementary i j hij a).val *ᵥ v = Pi.single i (a * v j) + v := by
  rw [Matrix.GeneralLinearGroup.elementary_val, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec, add_comm]
  rfl

lemma pairWGL_mulVec (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) (v : Fin n → F) :
    (pairWGL F n i j hij a).val *ᵥ v =
      Function.update (Function.update v i ((a : F) * v j)) j (-((a⁻¹ : Fˣ) : F) * v i) := by
  simp only [pairWGL, Units.val_mul, ← Matrix.mulVec_mulVec, elementary_mulVec]
  ext k
  by_cases hki : k = i
  · subst k
    simp [hij, hij.symm, Function.update_of_ne, mul_add]
  · by_cases hkj : k = j
    · subst k
      simp [hij.symm, mul_add]
    · simp [hki, hkj]

lemma pairHGL_mulVec (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) (v : Fin n → F) :
    (pairHGL F n i j hij a).val *ᵥ v =
      Function.update (Function.update v i ((a : F) * v i)) j (((a⁻¹ : Fˣ) : F) * v j) := by
  simp only [pairHGL, Units.val_mul, ← Matrix.mulVec_mulVec, pairWGL_mulVec]
  ext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hij]
    · simp [hki, hkj]

/-- The diagonal scaling factors of the marked finite torus matrix. -/
def pairScale (n : ℕ) (i j : Fin n) (a : Fˣ) (k : Fin n) : F :=
  if k = i then a else if k = j then ((a⁻¹ : Fˣ) : F) else 1

lemma pairScale_ne_zero (n : ℕ) (i j k : Fin n) (a : Fˣ) : pairScale F n i j a k ≠ 0 := by
  unfold pairScale
  split_ifs <;> simp

lemma pairHGL_val (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    (pairHGL F n i j hij a).val = Matrix.diagonal (pairScale F n i j a) := by
  apply Matrix.ext_of_mulVec_single
  intro k
  rw [pairHGL_mulVec, Matrix.diagonal_mulVec_single]
  ext l
  by_cases hli : l = i
  · subst l
    by_cases hki : k = i <;> simp [hki, hij, hij.symm, pairScale, Pi.single_apply, eq_comm]
  · by_cases hlj : l = j
    · subst l
      by_cases hkj : k = j <;> simp [hkj, hij, hij.symm, pairScale, Pi.single_apply, eq_comm]
    · by_cases hlk : l = k
      · subst l
        simp [hli, hlj, pairScale]
      · simp [hli, hlj, hlk, Pi.single_apply]

lemma pairScale_inv (n : ℕ) (i j k : Fin n) (a : Fˣ) :
    pairScale F n i j a⁻¹ k = (pairScale F n i j a k)⁻¹ := by
  unfold pairScale
  split_ifs <;> simp

lemma pairHGL_inv_val (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    ((pairHGL F n i j hij a)⁻¹).val = Matrix.diagonal (fun k => (pairScale F n i j a k)⁻¹) := by
  have hmul : pairHGL F n i j hij a * pairHGL F n i j hij a⁻¹ = 1 := by
    apply Units.ext
    rw [Units.val_mul, pairHGL_val, pairHGL_val, Matrix.diagonal_mul_diagonal]
    ext k l
    by_cases hkl : k = l
    · subst l
      simp [pairScale_inv, pairScale_ne_zero]
    · simp [hkl]
  have he := eq_inv_of_mul_eq_one_right hmul
  rw [← he, pairHGL_val]
  congr 1
  funext k
  exact pairScale_inv F n i j k a

lemma pairH_conj_root (n : ℕ) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (a : Fˣ) (t : F) :
    pairH F n i j hij a * x F n k l hkl t * (pairH F n i j hij a)⁻¹ =
      x F n k l hkl (pairScale F n i j a k * t * (pairScale F n i j a l)⁻¹) := by
  apply conj_root_of_vectors n (pairH F n i j hij a) (pairH_mem_stage F n i j hij a)
    (pairHGL F n i j hij a) (pairH_image F n i j hij a) k l k l hkl hkl t
  · rw [pairHGL_val, Matrix.diagonal_mulVec_single]
  · rw [pairHGL_inv_val, Matrix.single_vecMul_diagonal]
    simp

/-- The original finite roots whose row index differs from the last coordinate. -/
def rootsAwayFromLast (n : ℕ) : Set (Group F) :=
  {g | ∃ (i j : Fin (n + 1)) (hij : i ≠ j), i ≠ Fin.last n ∧ ∃ t : F,
    g = x F (n + 1) i j hij t}

lemma upperParabolic_eq_rootSpan (n : ℕ) :
    upperParabolic F n = Subgroup.closure (rootsAwayFromLast F n) := by
  apply le_antisymm
  · apply sup_le
    · apply (Subgroup.closure_le _).mpr
      rintro g ⟨i, j, hij, t, rfl⟩
      rw [x_stabilize]
      exact Subgroup.subset_closure ⟨i.castSucc, j.castSucc, by simpa using hij,
        Fin.castSucc_ne_last i, t, rfl⟩
    · intro g hg
      obtain ⟨v, rfl⟩ := (mem_columnSubgroup F n g).mp hg
      have hh : (freshColumnHom F n).range ≤
          (Subgroup.closure (rootsAwayFromLast F n)).toAddSubgroup := by
        unfold freshColumnHom
        erw [AddMonoidHom.noncommPiCoprod_range]
        apply iSup_le
        intro i
        rintro z ⟨a, rfl⟩
        change x F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a ∈
          Subgroup.closure (rootsAwayFromLast F n)
        exact Subgroup.subset_closure ⟨i.castSucc, Fin.last n, Fin.castSucc_ne_last i,
          Fin.castSucc_ne_last i, a, rfl⟩
      exact hh ⟨v, rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, j, hij, hi, t, rfl⟩
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    cases j using Fin.lastCases with
    | last =>
      apply (show columnSubgroup F n ≤ upperParabolic F n from le_sup_right)
      exact (mem_columnSubgroup F n _).mpr ⟨Pi.single i t, columnWord_single F n i t⟩
    | cast j =>
      apply (show stage F n ≤ upperParabolic F n from le_sup_left)
      have hij' : i ≠ j := by simpa using hij
      rw [← x_stabilize F n i j hij' t]
      exact x_mem_stage F n i j hij' t

lemma pairH_normalizes_upperParabolic (n : ℕ) (i j : Fin (n + 1)) (hij : i ≠ j) (a : Fˣ) :
    pairH F (n + 1) i j hij a ∈ Subgroup.normalizer (upperParabolic F n) := by
  rw [upperParabolic_eq_rootSpan]
  apply Subgroup.normalizer_le_normalizer_closure
  apply Subgroup.mem_set_normalizer_iff.mpr
  intro g
  constructor
  · rintro ⟨k, l, hkl, hk, t, rfl⟩
    rw [pairH_conj_root]
    exact ⟨k, l, hkl, hk, _, rfl⟩
  · rintro ⟨k, l, hkl, hk, t, ht⟩
    let c := pairScale F (n + 1) i j a k * (pairScale F (n + 1) i j a l)⁻¹
    have hc : c ≠ 0 := mul_ne_zero (pairScale_ne_zero F _ _ _ _ a)
      (inv_ne_zero (pairScale_ne_zero F _ _ _ _ a))
    have hconj : pairH F (n + 1) i j hij a * x F (n + 1) k l hkl (t / c) *
        (pairH F (n + 1) i j hij a)⁻¹ = x F (n + 1) k l hkl t := by
      rw [pairH_conj_root]
      congr 1
      calc
        _ = c * (t / c) := by dsimp [c]; ring
        _ = t := by exact mul_div_cancel₀ t hc
    have heq : g = x F (n + 1) k l hkl (t / c) := by
      apply (MulAut.conj (pairH F (n + 1) i j hij a)).injective
      exact ht.trans hconj.symm
    exact ⟨k, l, hkl, hk, t / c, heq⟩

lemma pairW_neg (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    pairW F n i j hij (-a) = (pairW F n i j hij a)⁻¹ := by
  simp [pairW, x_neg, mul_inv_rev, mul_assoc]

lemma pairH_one (n : ℕ) (i j : Fin n) (hij : i ≠ j) : pairH F n i j hij (1 : Fˣ) = 1 := by
  rw [pairH, pairW_neg, mul_inv_cancel]

/-- The marked pivot torus in the original defect quotient. -/
def pivotTorusHom (n : ℕ) (hn : 1 ≤ n) : Fˣ →* DefectQuotient F where
  toFun a := (QuotientGroup.mk' (defectSubgroup F))
    (pairH F (n + 1) ⟨0, by omega⟩ (Fin.last n) (by exact Fin.ne_of_val_ne (by simp; omega)) a)
  map_one' := by rw [pairH_one, map_one]
  map_mul' a b := by
    symm
    exact pivot_h_mul_in_quotient F (n + 1) (by omega) (Fin.last n)
      (by exact Fin.ne_of_val_ne (by simp; omega)) a b

/-- The actual old parabolic image, enlarged by the marked pivot torus. -/
def fullParabolic (n : ℕ) (hn : 1 ≤ n) : Subgroup (DefectQuotient F) :=
  (pivotTorusHom F n hn).range ⊔ (upperParabolic F n).map (QuotientGroup.mk' (defectSubgroup F))

lemma torus_normalizes_parabolic_image (n : ℕ) (hn : 1 ≤ n) :
    (pivotTorusHom F n hn).range ≤
      Subgroup.normalizer ((upperParabolic F n).map (QuotientGroup.mk' (defectSubgroup F))) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro t ⟨a, rfl⟩ p ⟨g, hg, rfl⟩
  let h := pairH F (n + 1) (⟨0, by omega⟩ : Fin (n + 1)) (Fin.last n)
    (Fin.ne_of_val_ne (by simp; omega)) a
  refine ⟨h * g * h⁻¹, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (pairH_normalizes_upperParabolic F n _ _ _ a) g).mp hg
  · simp only [map_mul, map_inv]
    rfl

theorem mem_fullParabolic (n : ℕ) (hn : 1 ≤ n) (z : DefectQuotient F) :
    z ∈ fullParabolic F n hn ↔ ∃ a : Fˣ, ∃ p : Group F, p ∈ upperParabolic F n ∧
      z = pivotTorusHom F n hn a * (QuotientGroup.mk' (defectSubgroup F)) p := by
  rw [← SetLike.mem_coe, fullParabolic,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (torus_normalizes_parabolic_image F n hn)]
  constructor
  · rintro ⟨t, ⟨a, rfl⟩, q, ⟨p, hp, rfl⟩, hz⟩
    exact ⟨a, p, hp, hz.symm⟩
  · rintro ⟨a, p, hp, rfl⟩
    exact ⟨_, ⟨a, rfl⟩, _, ⟨p, hp, rfl⟩, rfl⟩

end StableSteinberg.KernelGeneration.TorusParabolic

namespace StableSteinberg.KernelGeneration.RowColumnClosure
open Parabolic RootRelocation TorusParabolic StageRowReduction
open scoped Matrix
variable (F : Type u) [Field F]

lemma columnWord_mem_of_roots (n : ℕ) (K : Subgroup (Group F)) (v : Fin n → F)
    (hv : ∀ i : Fin n,
      x F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) (v i) ∈ K) :
    columnWord F n v ∈ K := by
  change freshColumnHom F n v ∈ K.toAddSubgroup
  unfold freshColumnHom AddMonoidHom.noncommPiCoprod
  change (Finset.univ : Finset (Fin n)).noncommSum
    (fun i => rootCoefficientHom F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) (v i))
    (by
      intro i _ j _ _
      exact x_commute F (n + 1) i.castSucc (Fin.last n) j.castSucc (Fin.last n)
        (Fin.castSucc_ne_last i) (Fin.castSucc_ne_last j)
        (Fin.castSucc_ne_last j).symm (Fin.castSucc_ne_last i).symm (v i) (v j))
      ∈ K.toAddSubgroup
  apply AddSubgroup.noncommSum_mem
  intro i _
  exact hv i

lemma rowWord_mem_of_roots (n : ℕ) (K : Subgroup (Group F)) (v : Fin n → F)
    (hv : ∀ i : Fin n,
      x F (n + 1) (Fin.last n) i.castSucc (Fin.castSucc_ne_last i).symm (v i) ∈ K) :
    rowWord F n v ∈ K := by
  change freshRowHom F n v ∈ K.toAddSubgroup
  unfold freshRowHom AddMonoidHom.noncommPiCoprod
  change (Finset.univ : Finset (Fin n)).noncommSum
    (fun i => rootCoefficientHom F (n + 1) (Fin.last n) i.castSucc
      (Fin.castSucc_ne_last i).symm (v i))
    (by
      intro i _ j _ _
      exact x_commute F (n + 1) (Fin.last n) i.castSucc (Fin.last n) j.castSucc
        (Fin.castSucc_ne_last i).symm (Fin.castSucc_ne_last j).symm
        (Fin.castSucc_ne_last i) (Fin.castSucc_ne_last j) (v i) (v j)) ∈ K.toAddSubgroup
  apply AddSubgroup.noncommSum_mem
  intro i _
  exact hv i

/-- The subgroup parametrized by the original fresh last-row homomorphism. -/
def rowSubgroup (n : ℕ) : Subgroup (Group F) := (freshRowHom F n).toMultiplicative.range

lemma mem_rowSubgroup (n : ℕ) (g : Group F) :
    g ∈ rowSubgroup F n ↔ ∃ v : Fin n → F, rowWord F n v = g := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v.toAdd, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨Multiplicative.ofAdd v, hv⟩

lemma rowSubgroup_eq_closure (n : ℕ) :
    rowSubgroup F n = Subgroup.closure {g | ∃ j : Fin n, ∃ t : F,
      g = x F (n + 1) (Fin.last n) j.castSucc (Fin.castSucc_ne_last j).symm t} := by
  apply le_antisymm
  · intro g hg
    obtain ⟨v, rfl⟩ := (mem_rowSubgroup F n g).mp hg
    apply rowWord_mem_of_roots
    intro i
    exact Subgroup.subset_closure ⟨i, v i, rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨j, t, rfl⟩
    exact (mem_rowSubgroup F n _).mpr ⟨Pi.single j t, rowWord_single F n j t⟩

lemma stage_normalizes_rows (n : ℕ) : stage F n ≤ Subgroup.normalizer (rowSubgroup F n) := by
  intro g hg
  obtain ⟨A, _, _, hrow⟩ := exists_stage_matrix_actions F n g hg
  obtain ⟨B, _, _, hrowInv⟩ := exists_stage_matrix_actions F n g⁻¹ ((stage F n).inv_mem hg)
  apply Subgroup.mem_normalizer_iff.mpr
  intro z
  constructor
  · intro hz
    obtain ⟨v, rfl⟩ := (mem_rowSubgroup F n z).mp hz
    rw [hrow]
    exact (mem_rowSubgroup F n _).mpr ⟨v ᵥ* (A⁻¹).val, rfl⟩
  · intro hz
    obtain ⟨v, hv⟩ := (mem_rowSubgroup F n _).mp hz
    have he : z = rowWord F n (v ᵥ* (B⁻¹).val) := by
      rw [← hrowInv, hv]
      simp [mul_assoc]
    rw [he]
    exact (mem_rowSubgroup F n _).mpr ⟨_, rfl⟩

lemma pairH_normalizes_rows (n : ℕ) (i j : Fin (n + 1)) (hij : i ≠ j) (a : Fˣ) :
    pairH F (n + 1) i j hij a ∈ Subgroup.normalizer (rowSubgroup F n) := by
  rw [rowSubgroup_eq_closure]
  apply Subgroup.normalizer_le_normalizer_closure
  apply Subgroup.mem_set_normalizer_iff.mpr
  intro g
  constructor
  · rintro ⟨k, t, rfl⟩
    rw [pairH_conj_root]
    exact ⟨k, _, rfl⟩
  · rintro ⟨k, t, ht⟩
    let c := pairScale F (n + 1) i j a (Fin.last n) *
      (pairScale F (n + 1) i j a k.castSucc)⁻¹
    have hc : c ≠ 0 := mul_ne_zero (pairScale_ne_zero F _ _ _ _ a)
      (inv_ne_zero (pairScale_ne_zero F _ _ _ _ a))
    have hconj : pairH F (n + 1) i j hij a *
        x F (n + 1) (Fin.last n) k.castSucc (Fin.castSucc_ne_last k).symm (t / c) *
        (pairH F (n + 1) i j hij a)⁻¹ =
          x F (n + 1) (Fin.last n) k.castSucc (Fin.castSucc_ne_last k).symm t := by
      rw [pairH_conj_root]
      congr 1
      calc
        _ = c * (t / c) := by dsimp [c]; ring
        _ = t := mul_div_cancel₀ t hc
    have heq : g = x F (n + 1) (Fin.last n) k.castSucc
        (Fin.castSucc_ne_last k).symm (t / c) := by
      apply (MulAut.conj (pairH F (n + 1) i j hij a)).injective
      exact ht.trans hconj.symm
    exact ⟨k, t / c, heq⟩

lemma normalizer_maps {A B : Type*} [_root_.Group A] [_root_.Group B]
    (q : A →* B) (K : Subgroup A) (g : A) (hg : g ∈ Subgroup.normalizer K) :
    q g ∈ Subgroup.normalizer (K.map q) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg a).mp ha, by simp⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨g⁻¹ * a * g, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff''.mp hg a).mp ha
    · simp only [map_mul, map_inv, he]
      simp [mul_assoc]

/-- The original fresh-column word in the quotient by the original ordered defects. -/
def qColumn (n : ℕ) (v : Fin n → F) : DefectQuotient F :=
  (QuotientGroup.mk' (defectSubgroup F)) (columnWord F n v)

/-- The original fresh-row word in the quotient by the original ordered defects. -/
def qRow (n : ℕ) (v : Fin n → F) : DefectQuotient F :=
  (QuotientGroup.mk' (defectSubgroup F)) (rowWord F n v)

/-- The image of the actual fresh-row subgroup in the original defect quotient. -/
def rowImage (n : ℕ) : Subgroup (DefectQuotient F) :=
  (rowSubgroup F n).map (QuotientGroup.mk' (defectSubgroup F))

lemma mem_rowImage (n : ℕ) (z : DefectQuotient F) :
    z ∈ rowImage F n ↔ ∃ v : Fin n → F, qRow F n v = z := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨v, rfl⟩ := (mem_rowSubgroup F n g).mp hg
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨rowWord F n v, (mem_rowSubgroup F n _).mpr ⟨v, rfl⟩, rfl⟩

lemma qColumn_mem_fullParabolic (n : ℕ) (hn : 1 ≤ n) (v : Fin n → F) :
    qColumn F n v ∈ fullParabolic F n hn := by
  apply (show (upperParabolic F n).map (QuotientGroup.mk' (defectSubgroup F)) ≤
    fullParabolic F n hn from le_sup_right)
  refine ⟨columnWord F n v, ?_, rfl⟩
  exact (show columnSubgroup F n ≤ upperParabolic F n from le_sup_right)
    ((mem_columnSubgroup F n _).mpr ⟨v, rfl⟩)

lemma qOld_mem_fullParabolic (n : ℕ) (hn : 1 ≤ n) (g : Group F) (hg : g ∈ stage F n) :
    (QuotientGroup.mk' (defectSubgroup F)) g ∈ fullParabolic F n hn := by
  apply (show (upperParabolic F n).map (QuotientGroup.mk' (defectSubgroup F)) ≤
    fullParabolic F n hn from le_sup_right)
  exact ⟨g, (show stage F n ≤ upperParabolic F n from le_sup_left) hg, rfl⟩

lemma fullParabolic_levi_column (n : ℕ) (hn : 1 ≤ n) (b : DefectQuotient F)
    (hb : b ∈ fullParabolic F n hn) :
    ∃ l : DefectQuotient F, l ∈ fullParabolic F n hn ∧ l ∈ Subgroup.normalizer (rowImage F n) ∧
      ∃ v : Fin n → F, b = l * qColumn F n v := by
  obtain ⟨a, p, hp, rfl⟩ := (mem_fullParabolic F n hn b).mp hb
  obtain ⟨g, hg, v, rfl⟩ := (mem_upperParabolic F n p).mp hp
  refine ⟨pivotTorusHom F n hn a * (QuotientGroup.mk' (defectSubgroup F)) g, ?_, ?_, v, ?_⟩
  · exact (fullParabolic F n hn).mul_mem
      ((show (pivotTorusHom F n hn).range ≤ fullParabolic F n hn from le_sup_left) ⟨a, rfl⟩)
      (qOld_mem_fullParabolic F n hn g hg)
  · apply (Subgroup.normalizer (rowImage F n : Set (DefectQuotient F))).mul_mem
    · apply normalizer_maps
      exact pairH_normalizes_rows F n _ _ _ a
    · exact normalizer_maps _ _ _ (stage_normalizes_rows F n hg)
  · simp only [map_mul, mul_assoc]
    rfl

lemma row_normalize_by_old_stage (n : ℕ) (hn : 2 ≤ n) (v : Fin n → F) (hv : v ≠ 0)
    (i : Fin n) : ∃ g : Group F, g ∈ stage F n ∧
      g⁻¹ * rowWord F n v * g = rowWord F n (Pi.single i 1) := by
  obtain ⟨g, hg, A, hA, hrow⟩ := rowReach_nonzero_to_single F n hn v hv i
  obtain ⟨B, hB, _, haction⟩ := exists_stage_matrix_actions F n g⁻¹ ((stage F n).inv_mem hg)
  have he : B = A⁻¹ := by
    apply StableGeneralLinear.of_injective F n
    rw [← hB, map_inv, hA, map_inv]
  refine ⟨g, hg, ?_⟩
  have hh := haction v
  rw [he] at hh
  simpa only [inv_inv, hrow] using hh

end StableSteinberg.KernelGeneration.RowColumnClosure

namespace StableSteinberg.KernelGeneration.PivotGauss
open Parabolic RootRelocation TorusParabolic RowColumnClosure
open scoped Matrix commutatorElement
variable (F : Type u) [Field F]

private lemma elementary_mulVec (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) (v : Fin n → F) :
    (Matrix.GeneralLinearGroup.elementary i j hij a).val *ᵥ v = Pi.single i (a * v j) + v := by
  rw [Matrix.GeneralLinearGroup.elementary_val, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec, add_comm]
  rfl

lemma pairWGL_entry (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) (k l : Fin n) :
    (pairWGL F n i j hij a).val k l =
      if k = j then if l = i then -((a⁻¹ : Fˣ) : F) else 0
      else if k = i then if l = j then (a : F) else 0 else if k = l then 1 else 0 := by
  have hh := congrArg (fun v : Fin n → F => v k)
    (pairWGL_mulVec F n i j hij a (Pi.single l 1))
  simpa [Matrix.mulVec_single_one, Matrix.col_apply, Function.update_apply,
    Pi.single_apply, eq_comm] using hh

lemma pairWGL_inv (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    (pairWGL F n i j hij a)⁻¹ = pairWGL F n i j hij (-a) := by
  apply StableGeneralLinear.of_injective F n
  rw [map_inv, ← pairW_image, ← map_inv, ← pairW_neg, pairW_image]

lemma pairW_conj_opposite (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) (t : F) :
    pairW F n i j hij a * x F n j i hij.symm t * (pairW F n i j hij a)⁻¹ =
      x F n i j hij (-(a : F) ^ 2 * t) := by
  have hc : (pairWGL F n i j hij a).val *ᵥ Pi.single j t = Pi.single i ((a : F) * t) := by
    rw [pairWGL_mulVec]
    ext k
    by_cases hki : k = i
    · subst k
      simp [hij]
    · by_cases hkj : k = j
      · subst k
        simp [hij, hij.symm]
      · simp [hki, hkj]
  have hr : Pi.single i (1 : F) ᵥ* ((pairWGL F n i j hij a)⁻¹).val =
      Pi.single j (-(a : F)) := by
    rw [pairWGL_inv, Matrix.single_vecMul]
    ext k
    simp [pairWGL_entry, hij, Pi.single_apply, eq_comm]
  have h := conj_root_of_vectors n (pairW F n i j hij a) (pairW_mem_stage F n i j hij a)
    (pairWGL F n i j hij a) (pairW_image F n i j hij a) j i i j hij.symm hij
    t ((a : F) * t) (-(a : F)) hc hr
  convert h using 1
  congr 1
  ring

lemma gaussGL (n : ℕ) (i j : Fin n) (hij : i ≠ j) (t : F) (hd : 1 + t ≠ 0) :
    Matrix.GeneralLinearGroup.elementary j i hij.symm 1 *
      Matrix.GeneralLinearGroup.elementary i j hij t =
      Matrix.GeneralLinearGroup.elementary i j hij (t / (1 + t)) *
        pairHGL F n i j hij (Units.mk0 (1 + t) hd)⁻¹ *
          Matrix.GeneralLinearGroup.elementary j i hij.symm (1 / (1 + t)) := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro k
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, elementary_mulVec, pairHGL_mulVec]
  ext l
  by_cases hli : l = i
  · subst l
    simp [hij]
    field_simp
    ring
  · by_cases hlj : l = j
    · subst l
      simp [hij, hij.symm]
      field_simp
      ring
    · simp [hli, hlj]

lemma pivot_pairW_mem (n : ℕ) (hn : 1 ≤ n) (a : Fˣ) :
    pairW F (n + 1) ⟨0, by omega⟩ (Fin.last n) (Fin.ne_of_val_ne (by simp; omega)) a ∈
      pivotStage F (n + 1) (by omega) (Fin.last n) (Fin.ne_of_val_ne (by simp; omega)) := by
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · exact Subgroup.subset_closure ⟨a, Or.inl rfl⟩
    · exact Subgroup.subset_closure ⟨-((a⁻¹ : Fˣ) : F), Or.inr rfl⟩
  · exact Subgroup.subset_closure ⟨a, Or.inl rfl⟩

lemma pivot_pairH_mem (n : ℕ) (hn : 1 ≤ n) (a : Fˣ) :
    pairH F (n + 1) ⟨0, by omega⟩ (Fin.last n) (Fin.ne_of_val_ne (by simp; omega)) a ∈
      pivotStage F (n + 1) (by omega) (Fin.last n) (Fin.ne_of_val_ne (by simp; omega)) :=
  Subgroup.mul_mem _ (pivot_pairW_mem F n hn a) (pivot_pairW_mem F n hn (-1))

lemma pivot_gauss (n : ℕ) (hn : 1 ≤ n) (t : F) (hd : 1 + t ≠ 0) :
    qRow F n (Pi.single ⟨0, by omega⟩ 1) * qColumn F n (Pi.single ⟨0, by omega⟩ t) =
      qColumn F n (Pi.single ⟨0, by omega⟩ (t / (1 + t))) *
        pivotTorusHom F n hn (Units.mk0 (1 + t) hd)⁻¹ *
          qRow F n (Pi.single ⟨0, by omega⟩ (1 / (1 + t))) := by
  simp only [qRow, qColumn, rowWord_single, columnWord_single, pivotTorusHom,
    MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul]
  apply pivot_quotient_eq_of_same_image F (n + 1) (by omega) (Fin.last n)
    (Fin.ne_of_val_ne (by simp; omega))
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨1, Or.inr rfl⟩)
      (Subgroup.subset_closure ⟨t, Or.inl rfl⟩)
  · exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.subset_closure ⟨t / (1 + t), Or.inl rfl⟩)
        (pivot_pairH_mem F n hn _))
      (Subgroup.subset_closure ⟨1 / (1 + t), Or.inr rfl⟩)
  · apply Subtype.ext
    change toStableGeneralLinear F _ = toStableGeneralLinear F _
    simp only [map_mul, toStableGeneralLinear_x, pairH_image]
    have hh := congrArg (StableGeneralLinear.of F (n + 1))
      (gaussGL F (n + 1) (⟨0, by omega⟩ : Fin n).castSucc (Fin.last n)
        (Fin.castSucc_ne_last _) t hd)
    simp only [map_mul] at hh
    exact hh

private lemma conj_chain (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) :
    x F n i j hij a * x F n j k hjk b * (x F n i j hij a)⁻¹ =
      x F n i k hik (a * b) * x F n j k hjk b := by
  have hh := x_commutator F n i j k hij hjk hik a b
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul] at hh
  exact hh

lemma pairW_conj_outgoing (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a : Fˣ) (t : F) :
    pairW F n i j hij a * x F n j k hjk t * (pairW F n i j hij a)⁻¹ =
      x F n i k hik ((a : F) * t) := by
  let A := x F n i j hij (a : F)
  let B := x F n j i hij.symm (-((a⁻¹ : Fˣ) : F))
  let X := x F n j k hjk t
  let Y := x F n i k hik ((a : F) * t)
  have hAX : A * X * A⁻¹ = Y * X := conj_chain F n i j k hij hjk hik a t
  have hBY : B * Y * B⁻¹ = X⁻¹ * Y := by
    have hh := conj_chain F n j i k hij.symm hik hjk (-((a⁻¹ : Fˣ) : F)) ((a : F) * t)
    simpa [B, X, Y, mul_assoc, x_neg] using hh
  have hBX : B * X * B⁻¹ = X := by
    rw [(x_commute F n j i j k hij.symm hjk hij hjk.symm _ t).eq, mul_inv_cancel_right]
  have hAY : A * Y * A⁻¹ = Y := by
    rw [(x_commute F n i j i k hij hik hij.symm hik.symm _ _).eq, mul_inv_cancel_right]
  have hXY : Commute X Y := x_commute F n j k i k hjk hik hik.symm hjk.symm _ _
  calc
    _ = A * (B * (A * X * A⁻¹) * B⁻¹) * A⁻¹ := by
      simp only [pairW, A, B, X, mul_inv_rev, mul_assoc]
    _ = A * ((B * Y * B⁻¹) * (B * X * B⁻¹)) * A⁻¹ := by
      rw [hAX]
      simp only [mul_assoc, inv_mul_cancel_left]
    _ = Y := by rw [hBY, hBX, hXY.inv_mul_cancel, hAY]

lemma pivotW_conj_rows_mem_parabolic (n : ℕ) (hn : 1 ≤ n) (a : Fˣ) (v : Fin n → F) :
    pairW F (n + 1) ⟨0, by omega⟩ (Fin.last n) (Fin.ne_of_val_ne (by simp; omega)) a *
      rowWord F n v *
        (pairW F (n + 1) ⟨0, by omega⟩ (Fin.last n) (Fin.ne_of_val_ne (by simp; omega)) a)⁻¹ ∈
          upperParabolic F n := by
  let i : Fin n := ⟨0, by omega⟩
  let s := pairW F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a
  change (MulAut.conj s) (rowWord F n v) ∈ upperParabolic F n
  change rowWord F n v ∈ (upperParabolic F n).comap (MulAut.conj s).toMonoidHom
  apply rowWord_mem_of_roots
  intro j
  change s * x F (n + 1) (Fin.last n) j.castSucc (Fin.castSucc_ne_last j).symm (v j) * s⁻¹ ∈
    upperParabolic F n
  by_cases hji : j = i
  · subst j
    rw [show s = pairW F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a from rfl,
      pairW_conj_opposite]
    apply (show columnSubgroup F n ≤ upperParabolic F n from le_sup_right)
    exact (mem_columnSubgroup F n _).mpr ⟨Pi.single i _, columnWord_single F n i _⟩
  · have hij : i ≠ j := Ne.symm hji
    rw [show s = pairW F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a from rfl,
      pairW_conj_outgoing F (n + 1) i.castSucc (Fin.last n) j.castSucc
        (Fin.castSucc_ne_last i) (Fin.castSucc_ne_last j).symm (by simpa using hij)]
    rw [← x_stabilize F n i j hij]
    exact (show stage F n ≤ upperParabolic F n from le_sup_left) (x_mem_stage F n i j hij _)

end StableSteinberg.KernelGeneration.PivotGauss

namespace StableSteinberg.KernelGeneration.BruhatCoverage
open Parabolic RootRelocation TorusParabolic RowColumnClosure PivotGauss
open scoped Matrix commutatorElement
variable (F : Type u) [Field F]

private def DoubleRow {G : Type*} [_root_.Group G] (B V : Subgroup G) (z : G) : Prop :=
  ∃ b₁ : G, b₁ ∈ B ∧ ∃ v : G, v ∈ V ∧ ∃ b₂ : G, b₂ ∈ B ∧ z = b₁ * v * b₂

private lemma doubleRow_left {G : Type*} [_root_.Group G] (B V : Subgroup G)
    {z b : G} (hz : DoubleRow B V z) (hb : b ∈ B) : DoubleRow B V (b * z) := by
  obtain ⟨a, ha, v, hv, c, hc, rfl⟩ := hz
  exact ⟨b * a, B.mul_mem hb ha, v, hv, c, hc, by simp only [mul_assoc]⟩

private lemma doubleRow_right {G : Type*} [_root_.Group G] (B V : Subgroup G)
    {z b : G} (hz : DoubleRow B V z) (hb : b ∈ B) : DoubleRow B V (z * b) := by
  obtain ⟨a, ha, v, hv, c, hc, rfl⟩ := hz
  exact ⟨a, ha, v, hv, c * b, B.mul_mem hc hb, by simp only [mul_assoc]⟩

private lemma doubleRow_of_row {G : Type*} [_root_.Group G] (B V : Subgroup G)
    {v : G} (hv : v ∈ V) : DoubleRow B V v :=
  ⟨1, B.one_mem, v, hv, 1, B.one_mem, by simp⟩

private lemma doubleRow_of_B {G : Type*} [_root_.Group G] (B V : Subgroup G)
    {b : G} (hb : b ∈ B) : DoubleRow B V b :=
  ⟨b, hb, 1, V.one_mem, 1, B.one_mem, by simp⟩

/-- The original finite pivot Weyl word in the original defect quotient. -/
def pivotWQ (n : ℕ) (hn : 1 ≤ n) (a : Fˣ) : DefectQuotient F :=
  (QuotientGroup.mk' (defectSubgroup F))
    (pairW F (n + 1) ⟨0, by omega⟩ (Fin.last n) (Fin.ne_of_val_ne (by simp; omega)) a)

private lemma qParabolic_mem_B (n : ℕ) (hn : 1 ≤ n) (g : Group F)
    (hg : g ∈ upperParabolic F n) :
    (QuotientGroup.mk' (defectSubgroup F)) g ∈ fullParabolic F n hn :=
  (show (upperParabolic F n).map (QuotientGroup.mk' (defectSubgroup F)) ≤
    fullParabolic F n hn from le_sup_right) ⟨g, hg, rfl⟩

private lemma pivotWQ_doubleRow (n : ℕ) (hn : 1 ≤ n) (a : Fˣ) :
    DoubleRow (fullParabolic F n hn) (rowImage F n) (pivotWQ F n hn a) := by
  refine ⟨qColumn F n (Pi.single ⟨0, by omega⟩ a), qColumn_mem_fullParabolic F n hn _,
    qRow F n (Pi.single ⟨0, by omega⟩ (-((a⁻¹ : Fˣ) : F))),
    (mem_rowImage F n _).mpr ⟨_, rfl⟩,
    qColumn F n (Pi.single ⟨0, by omega⟩ a), qColumn_mem_fullParabolic F n hn _, ?_⟩
  simp only [pivotWQ, pairW, map_mul, qColumn, qRow, columnWord_single, rowWord_single]
  rfl

lemma pivot_row_conj_column_away (n : ℕ) (hn : 1 ≤ n) (v : Fin n → F)
    (hv : v ⟨0, by omega⟩ = 0) :
    rowWord F n (Pi.single ⟨0, by omega⟩ 1) * columnWord F n v *
      (rowWord F n (Pi.single ⟨0, by omega⟩ 1))⁻¹ ∈ upperParabolic F n := by
  let i : Fin n := ⟨0, by omega⟩
  let r := rowWord F n (Pi.single i 1)
  change columnWord F n v ∈ (upperParabolic F n).comap (MulAut.conj r).toMonoidHom
  apply columnWord_mem_of_roots
  intro j
  change r * x F (n + 1) j.castSucc (Fin.last n) (Fin.castSucc_ne_last j) (v j) * r⁻¹ ∈
    upperParabolic F n
  by_cases hji : j = i
  · subst j
    rw [hv, x_zero, mul_one, mul_inv_cancel]
    exact (upperParabolic F n).one_mem
  · have hji' : j.castSucc ≠ i.castSucc := by simpa using hji
    have hc : ⁅r, x F (n + 1) j.castSucc (Fin.last n) (Fin.castSucc_ne_last j) (v j)⁆ =
        x F n j i hji (-v j) := by
      dsimp only [r]
      rw [rowWord_single, ← commutatorElement_inv,
        x_commutator F (n + 1) j.castSucc (Fin.last n) i.castSucc
          (Fin.castSucc_ne_last j) (Fin.castSucc_ne_last i).symm hji', mul_one,
        ← x_neg, ← x_stabilize]
    have he : r * x F (n + 1) j.castSucc (Fin.last n) (Fin.castSucc_ne_last j) (v j) * r⁻¹ =
        x F n j i hji (-v j) *
          x F (n + 1) j.castSucc (Fin.last n) (Fin.castSucc_ne_last j) (v j) := by
      rw [commutatorElement_def, mul_inv_eq_iff_eq_mul] at hc
      exact hc
    rw [he]
    apply (upperParabolic F n).mul_mem
    · exact (show stage F n ≤ upperParabolic F n from le_sup_left) (x_mem_stage F n j i hji _)
    · exact (show columnSubgroup F n ≤ upperParabolic F n from le_sup_right)
        ((mem_columnSubgroup F n _).mpr ⟨Pi.single j _, columnWord_single F n j _⟩)

lemma pivot_singular (n : ℕ) (hn : 1 ≤ n) :
    qRow F n (Pi.single ⟨0, by omega⟩ 1) * qColumn F n (Pi.single ⟨0, by omega⟩ (-1)) =
      qColumn F n (Pi.single ⟨0, by omega⟩ 1) * pivotWQ F n hn (-1) := by
  simp only [qRow, qColumn, pivotWQ, rowWord_single, columnWord_single, ← map_mul]
  apply congrArg (QuotientGroup.mk' (defectSubgroup F))
  let i : Fin n := ⟨0, by omega⟩
  change x F (n + 1) (Fin.last n) i.castSucc (Fin.castSucc_ne_last i).symm 1 *
    x F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) (-1) =
      x F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) 1 *
        pairW F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) (-1)
  simp only [pairW, Units.val_neg, Units.val_one, inv_neg, inv_one, neg_neg,
    ← mul_assoc, x_add, add_neg_cancel, x_zero, one_mul]

private lemma normalized_row_column_row (n : ℕ) (hn : 1 ≤ n) (v w : Fin n → F) :
    DoubleRow (fullParabolic F n hn) (rowImage F n)
      (qRow F n (Pi.single ⟨0, by omega⟩ 1) * qColumn F n v * qRow F n w) := by
  let i : Fin n := ⟨0, by omega⟩
  let r := qRow F n (Pi.single i 1)
  let t := v i
  let v' := v - Pi.single i t
  let u := qColumn F n v'
  have hv' : v' i = 0 := by simp [v', t]
  have hv : qColumn F n v = u * qColumn F n (Pi.single i t) := by
    change (QuotientGroup.mk' _) (columnWord F n v) =
      (QuotientGroup.mk' _) (columnWord F n v') * (QuotientGroup.mk' _) (columnWord F n _)
    rw [← map_mul, ← columnWord_add]
    congr 2
    exact (sub_add_cancel v (Pi.single i t)).symm
  have hb : r * u * r⁻¹ ∈ fullParabolic F n hn := by
    have hh := qParabolic_mem_B F n hn _ (pivot_row_conj_column_away F n hn v' hv')
    simp only [map_mul, map_inv] at hh
    exact hh
  have he : r * qColumn F n v * qRow F n w =
      (r * u * r⁻¹) * (r * qColumn F n (Pi.single i t) * qRow F n w) := by
    rw [hv]
    simp only [mul_assoc, inv_mul_cancel_left]
  change DoubleRow _ _ (r * qColumn F n v * qRow F n w)
  rw [he]
  apply doubleRow_left _ _ _ hb
  by_cases hd : 1 + t = 0
  · have ht : t = -1 := eq_neg_of_add_eq_zero_right hd
    rw [ht, pivot_singular F n hn]
    have hh : pivotWQ F n hn (-1) * qRow F n w * (pivotWQ F n hn (-1))⁻¹ ∈
        fullParabolic F n hn := by
      have hm := qParabolic_mem_B F n hn _ (pivotW_conj_rows_mem_parabolic F n hn (-1) w)
      simp only [map_mul, map_inv] at hm
      exact hm
    have he' : qColumn F n (Pi.single i 1) * pivotWQ F n hn (-1) * qRow F n w =
        qColumn F n (Pi.single i 1) *
          (pivotWQ F n hn (-1) * qRow F n w * (pivotWQ F n hn (-1))⁻¹) * pivotWQ F n hn (-1) := by
      simp [mul_assoc]
    rw [he']
    exact doubleRow_left _ _ (pivotWQ_doubleRow F n hn (-1))
      ((fullParabolic F n hn).mul_mem (qColumn_mem_fullParabolic F n hn _) hh)
  · rw [pivot_gauss F n hn t hd]
    have hrow : qRow F n (Pi.single i (1 / (1 + t))) * qRow F n w ∈ rowImage F n :=
      (rowImage F n).mul_mem ((mem_rowImage F n _).mpr ⟨_, rfl⟩)
        ((mem_rowImage F n _).mpr ⟨_, rfl⟩)
    have ht : pivotTorusHom F n hn (Units.mk0 (1 + t) hd)⁻¹ ∈ fullParabolic F n hn :=
      (show (pivotTorusHom F n hn).range ≤ fullParabolic F n hn from le_sup_left) ⟨_, rfl⟩
    have hh := doubleRow_left _ _ (doubleRow_of_row _ _ hrow)
      ((fullParabolic F n hn).mul_mem
        (qColumn_mem_fullParabolic F n hn (Pi.single i (t / (1 + t)))) ht)
    simpa only [mul_assoc] using hh

private lemma row_column_row (n : ℕ) (hn : 2 ≤ n) (v u w : Fin n → F) :
    DoubleRow (fullParabolic F n (by omega)) (rowImage F n)
      (qRow F n v * qColumn F n u * qRow F n w) := by
  by_cases hv : v = 0
  · subst v
    have he : qRow F n 0 = 1 := by simp [qRow, rowWord_zero]
    rw [he, one_mul]
    exact doubleRow_left _ _
      (doubleRow_of_row _ _ ((mem_rowImage F n _).mpr ⟨w, rfl⟩))
      (qColumn_mem_fullParabolic F n (by omega) u)
  · let i : Fin n := ⟨0, by omega⟩
    obtain ⟨g, hg, hrow⟩ := row_normalize_by_old_stage F n hn v hv i
    obtain ⟨A, _, hcol, hrowAll⟩ := exists_stage_matrix_actions F n g⁻¹ ((stage F n).inv_mem hg)
    have he : rowWord F n v * columnWord F n u * rowWord F n w =
        g * (rowWord F n (Pi.single i 1) * columnWord F n (A.val *ᵥ u) *
          rowWord F n (w ᵥ* (A⁻¹).val)) * g⁻¹ := by
      rw [← hrow, ← hcol, ← hrowAll]
      simp [mul_assoc]
    have heq := congrArg (QuotientGroup.mk' (defectSubgroup F)) he
    simp only [map_mul, map_inv] at heq
    change qRow F n v * qColumn F n u * qRow F n w =
      (QuotientGroup.mk' (defectSubgroup F)) g *
        (qRow F n (Pi.single i 1) * qColumn F n (A.val *ᵥ u) *
          qRow F n (w ᵥ* (A⁻¹).val)) * ((QuotientGroup.mk' (defectSubgroup F)) g)⁻¹ at heq
    rw [heq]
    apply doubleRow_right _ _
    · exact doubleRow_left _ _ (normalized_row_column_row F n (by omega) _ _)
        (qOld_mem_fullParabolic F n (by omega) g hg)
    · exact (fullParabolic F n (by omega)).inv_mem (qOld_mem_fullParabolic F n (by omega) g hg)

private lemma row_B_row (n : ℕ) (hn : 2 ≤ n) (v b w : DefectQuotient F)
    (hv : v ∈ rowImage F n) (hb : b ∈ fullParabolic F n (by omega)) (hw : w ∈ rowImage F n) :
    DoubleRow (fullParabolic F n (by omega)) (rowImage F n) (v * b * w) := by
  obtain ⟨l, hl, hnorm, u, rfl⟩ := fullParabolic_levi_column F n (by omega) b hb
  have hv' : l⁻¹ * v * l ∈ rowImage F n := (Subgroup.mem_normalizer_iff''.mp hnorm v).mp hv
  obtain ⟨v', hv'eq⟩ := (mem_rowImage F n _).mp hv'
  obtain ⟨w', rfl⟩ := (mem_rowImage F n w).mp hw
  have he : v * (l * qColumn F n u) * qRow F n w' =
      l * (qRow F n v' * qColumn F n u * qRow F n w') := by
    rw [hv'eq]
    simp [mul_assoc]
  rw [he]
  exact doubleRow_left _ _ (row_column_row F n hn v' u w') hl

private def collectedSubgroup (n : ℕ) (hn : 2 ≤ n) : Subgroup (DefectQuotient F) where
  carrier := {z | DoubleRow (fullParabolic F n (by omega)) (rowImage F n) z}
  one_mem' := doubleRow_of_row _ _ (rowImage F n).one_mem
  mul_mem' := by
    rintro a b ⟨a₁, ha₁, v, hv, a₂, ha₂, rfl⟩ ⟨b₁, hb₁, w, hw, b₂, hb₂, rfl⟩
    have hh := doubleRow_right _ _ (doubleRow_left _ _
      (row_B_row F n hn v (a₂ * b₁) w hv
        ((fullParabolic F n (by omega)).mul_mem ha₂ hb₁) hw) ha₁) hb₂
    change DoubleRow _ _ _
    simpa only [mul_assoc] using hh
  inv_mem' := by
    rintro a ⟨b₁, hb₁, v, hv, b₂, hb₂, rfl⟩
    exact ⟨b₂⁻¹, (fullParabolic F n (by omega)).inv_mem hb₂,
      v⁻¹, (rowImage F n).inv_mem hv,
      b₁⁻¹, (fullParabolic F n (by omega)).inv_mem hb₁, by simp only [mul_inv_rev, mul_assoc]⟩

/-- Every next-stage word is a product of a parabolic, row and parabolic element modulo C. -/
theorem stage_quotient_BVB (n : ℕ) (hn : 2 ≤ n) (g : Group F) (hg : g ∈ stage F (n + 1)) :
    ∃ b₁ : DefectQuotient F, b₁ ∈ fullParabolic F n (by omega) ∧
      ∃ v : DefectQuotient F, v ∈ rowImage F n ∧
        ∃ b₂ : DefectQuotient F, b₂ ∈ fullParabolic F n (by omega) ∧
          (QuotientGroup.mk' (defectSubgroup F)) g = b₁ * v * b₂ := by
  have hle : stage F (n + 1) ≤
      (collectedSubgroup F n hn).comap (QuotientGroup.mk' (defectSubgroup F)) := by
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨i, j, hij, t, rfl⟩
    change DoubleRow (fullParabolic F n (by omega)) (rowImage F n)
      ((QuotientGroup.mk' (defectSubgroup F)) (x F (n + 1) i j hij t))
    by_cases hi : i = Fin.last n
    · subst i
      have hj : j ≠ Fin.last n := Ne.symm hij
      obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      apply doubleRow_of_row
      apply (mem_rowImage F n _).mpr
      exact ⟨Pi.single j t, by simp only [qRow, rowWord_single]⟩
    · apply doubleRow_of_B
      apply qParabolic_mem_B
      rw [upperParabolic_eq_rootSpan]
      exact Subgroup.subset_closure ⟨i, j, hij, hi, t, rfl⟩
  exact hle hg

end StableSteinberg.KernelGeneration.BruhatCoverage
