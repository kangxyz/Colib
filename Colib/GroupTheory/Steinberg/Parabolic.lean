/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.GroupTheory.Steinberg.RankTwo

/-!
# Actual finite parabolic words and pivot-pair transport

This file supplies the source-word foundations for finite-rank kernel descent in
the original stable Steinberg presentation. The old stage normalizes its last-column
subgroup, and their generated subgroup has unique form `a * columnWord v`.
Literal finite matrix entries show that its elementary-map kernel is the old-stage
kernel. No injectivity of a finite Steinberg-stage embedding is assumed.

Explicit three-root Weyl shifts preserve positive coefficients and transport the
original rank-two defects to every pivot pair `(0,k)`. The proved rank-two Bruhat
result implies faithfulness modulo the original defect subgroup on each such pair.
Actual old-stage elementary words also act transitively on nonzero finite row
vectors in rank at least two. All constructions include fields of order two or three.

## Implementation provenance

Adapted from `Quillen/Algebra/Group/StableSteinbergParabolic.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The selected native stable group,
elementary units, root generators and canonical maps remain unchanged.
-/
@[expose] public section

noncomputable section
universe u

namespace StableSteinberg.KernelGeneration.Parabolic
open scoped Matrix Pointwise
variable (F : Type u) [Field F]

private def columnN (n : ℕ) (v : Fin n → F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  ∑ i : Fin n, Matrix.single i.castSucc (Fin.last n) (v i)

private lemma columnN_add (n : ℕ) (v w : Fin n → F) :
    columnN F n (v + w) = columnN F n v + columnN F n w := by
  simp [columnN, Matrix.single_add, Finset.sum_add_distrib]

private lemma columnN_zero (n : ℕ) : columnN F n 0 = 0 := by simp [columnN]

private lemma columnN_mul (n : ℕ) (v w : Fin n → F) :
    columnN F n v * columnN F n w = 0 := by
  simp only [columnN, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  exact Matrix.single_mul_single_of_ne (l := Fin (n + 1)) (m := Fin (n + 1))
    (n := Fin (n + 1)) (v j) j.castSucc (Fin.last n) i.castSucc (Fin.castSucc_ne_last i).symm (w i)

private lemma columnN_single (n : ℕ) (i : Fin n) (a : F) :
    columnN F n (Pi.single i a) = Matrix.single i.castSucc (Fin.last n) a := by
  simp [columnN, Pi.single_apply, apply_ite]

private lemma columnN_last_column (n : ℕ) (v : Fin n → F) (i : Fin n) :
    columnN F n v i.castSucc (Fin.last n) = v i := by
  simp [columnN, Matrix.single, Matrix.sum_apply, eq_comm]

private lemma columnMatrix_mul (n : ℕ) (v w : Fin n → F) :
    (1 + columnN F n v) * (1 + columnN F n w) = 1 + columnN F n (v + w) := by
  rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, columnN_mul, add_zero,
    columnN_add]
  abel

private def columnGL (n : ℕ) (v : Fin n → F) : Matrix.GeneralLinearGroup (Fin (n + 1)) F where
  val := 1 + columnN F n v
  inv := 1 + columnN F n (-v)
  val_inv := by rw [columnMatrix_mul, add_neg_cancel, columnN_zero, add_zero]
  inv_val := by rw [columnMatrix_mul, neg_add_cancel, columnN_zero, add_zero]

private lemma columnGL_zero (n : ℕ) : columnGL F n 0 = 1 := by
  apply Units.ext
  simp [columnGL, columnN_zero]

private lemma columnGL_add (n : ℕ) (v w : Fin n → F) :
    columnGL F n (v + w) = columnGL F n v * columnGL F n w := by
  apply Units.ext
  exact (columnMatrix_mul F n v w).symm

private lemma columnGL_single (n : ℕ) (i : Fin n) (a : F) :
    columnGL F n (Pi.single i a) =
      Matrix.GeneralLinearGroup.elementary i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a := by
  apply Units.ext
  change 1 + columnN F n (Pi.single i a) = _
  rw [columnN_single]
  rfl

private lemma columnGL_last_column (n : ℕ) (v : Fin n → F) (i : Fin n) :
    (columnGL F n v).val i.castSucc (Fin.last n) = v i := by
  change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i.castSucc (Fin.last n) +
    columnN F n v i.castSucc (Fin.last n) = v i
  rw [columnN_last_column]
  simp

private def columnGLHom (n : ℕ) :
    (Fin n → F) →+ Additive (Matrix.GeneralLinearGroup (Fin (n + 1)) F) where
  toFun v := Additive.ofMul (columnGL F n v)
  map_zero' := columnGL_zero F n
  map_add' v w := columnGL_add F n v w

private lemma toStableGeneralLinear_columnWord (n : ℕ) (v : Fin n → F) :
    toStableGeneralLinear F (columnWord F n v) =
      StableGeneralLinear.of F (n + 1) (columnGL F n v) := by
  have hh : (toStableGeneralLinear F).toAdditive.comp (freshColumnHom F n) =
      (StableGeneralLinear.of F (n + 1)).toAdditive.comp (columnGLHom F n) := by
    apply AddMonoidHom.pi_ext
    intro i a
    change toStableGeneralLinear F (columnWord F n (Pi.single i a)) =
      StableGeneralLinear.of F (n + 1) (columnGL F n (Pi.single i a))
    rw [columnWord_single, toStableGeneralLinear_x, columnGL_single]
  exact congrArg Additive.toMul (congrArg (fun k => k v) hh)

/-- The original fresh-column word retains every coefficient in its literal matrix. -/
lemma columnWord_injective (n : ℕ) : Function.Injective (columnWord F n) := by
  intro v w hvw
  have he : columnGL F n v = columnGL F n w := by
    apply StableGeneralLinear.of_injective F (n + 1)
    rw [← toStableGeneralLinear_columnWord, ← toStableGeneralLinear_columnWord, hvw]
  ext i
  have hh := congrArg (fun B : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
    B.val i.castSucc (Fin.last n)) he
  simpa only [columnGL_last_column] using hh

/-- Negating the fresh-column vector inverts the original source word. -/
lemma columnWord_neg (n : ℕ) (v : Fin n → F) :
    columnWord F n (-v) = (columnWord F n v)⁻¹ :=
  congrArg Additive.toMul (map_neg (freshColumnHom F n) v)

/-- A fresh-column word with an old finite-block image must be the identity. -/
lemma columnWord_eq_one_of_old_image (n : ℕ) (v : Fin n → F)
    (A : Matrix.GeneralLinearGroup (Fin n) F)
    (hA : toStableGeneralLinear F (columnWord F n v) = StableGeneralLinear.of F n A) :
    columnWord F n v = 1 := by
  have he : columnGL F n v = StableGeneralLinear.step F n A := by
    apply StableGeneralLinear.of_injective F (n + 1)
    rw [← toStableGeneralLinear_columnWord, hA, ← StableGeneralLinear.transition_succ,
      StableGeneralLinear.of_transition]
  have hv : v = 0 := by
    ext i
    have hi := congrArg (fun B : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
      B.val i.castSucc (Fin.last n)) he
    change v i = 0
    simpa only [columnGL_last_column, StableGeneralLinear.step_val_castSucc_last] using hi
  rw [hv, columnWord_zero]

/-- The actual subgroup parametrized by the existing fresh-column homomorphism. -/
def columnSubgroup (n : ℕ) : Subgroup (Group F) := (freshColumnHom F n).toMultiplicative.range

/-- Membership retains an actual finite vector and its original column word. -/
lemma mem_columnSubgroup (n : ℕ) (g : Group F) :
    g ∈ columnSubgroup F n ↔ ∃ v : Fin n → F, columnWord F n v = g := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v.toAdd, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨Multiplicative.ofAdd v, hv⟩

/-- Every original fresh-column word lies in the next actual finite stage. -/
lemma columnWord_mem_stage (n : ℕ) (v : Fin n → F) : columnWord F n v ∈ stage F (n + 1) := by
  have hh : (freshColumnHom F n).range ≤ (stage F (n + 1)).toAddSubgroup := by
    unfold freshColumnHom
    erw [AddMonoidHom.noncommPiCoprod_range]
    apply iSup_le
    intro i
    rintro z ⟨a, rfl⟩
    exact x_mem_stage F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a
  exact hh ⟨v, rfl⟩

/-- The column subgroup is contained in the next original finite stage. -/
lemma columnSubgroup_le_stage (n : ℕ) : columnSubgroup F n ≤ stage F (n + 1) := by
  intro g hg
  obtain ⟨v, rfl⟩ := (mem_columnSubgroup F n g).mp hg
  exact columnWord_mem_stage F n v

/-- The accepted original matrix actions make the old stage normalize fresh columns. -/
lemma stage_normalizes_columns (n : ℕ) : stage F n ≤ Subgroup.normalizer (columnSubgroup F n) := by
  intro g hg
  obtain ⟨A, _, hcol, _⟩ := exists_stage_matrix_actions F n g hg
  obtain ⟨B, _, hcolInv, _⟩ := exists_stage_matrix_actions F n g⁻¹ ((stage F n).inv_mem hg)
  apply Subgroup.mem_normalizer_iff.mpr
  intro z
  constructor
  · intro hz
    obtain ⟨v, rfl⟩ := (mem_columnSubgroup F n z).mp hz
    rw [hcol]
    exact (mem_columnSubgroup F n _).mpr ⟨A.val *ᵥ v, rfl⟩
  · intro hz
    obtain ⟨v, hv⟩ := (mem_columnSubgroup F n _).mp hz
    have he : z = columnWord F n (B.val *ᵥ v) := by
      rw [← hcolInv, hv]
      simp [mul_assoc]
    rw [he]
    exact (mem_columnSubgroup F n _).mpr ⟨_, rfl⟩

/-- The subgroup generated by the old stage and its actual fresh last-column roots. -/
def upperParabolic (n : ℕ) : Subgroup (Group F) := stage F n ⊔ columnSubgroup F n

/-- The collected subgroup remains inside the next actual finite stage. -/
lemma upperParabolic_le_stage (n : ℕ) : upperParabolic F n ≤ stage F (n + 1) :=
  sup_le (stage_le_succ F n) (columnSubgroup_le_stage F n)

/-- Normalization gives an actual old-stage times column-word factorization. -/
lemma mem_upperParabolic (n : ℕ) (g : Group F) :
    g ∈ upperParabolic F n ↔
      ∃ a : Group F, a ∈ stage F n ∧ ∃ v : Fin n → F, g = a * columnWord F n v := by
  rw [← SetLike.mem_coe, upperParabolic,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (stage_normalizes_columns F n)]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨v, rfl⟩ := (mem_columnSubgroup F n b).mp hb
    exact ⟨a, ha, v, hab.symm⟩
  · rintro ⟨a, ha, v, rfl⟩
    exact ⟨a, ha, columnWord F n v, (mem_columnSubgroup F n _).mpr ⟨v, rfl⟩, rfl⟩

/-- Literal finite column detection makes the two factors unique. -/
lemma collected_product_unique (n : ℕ) (a b : Group F)
    (ha : a ∈ stage F n) (hb : b ∈ stage F n) (v w : Fin n → F)
    (heq : a * columnWord F n v = b * columnWord F n w) : a = b ∧ v = w := by
  have hword : columnWord F n (v - w) = a⁻¹ * b := by
    rw [sub_eq_add_neg, columnWord_add, columnWord_neg]
    calc
      _ = a⁻¹ * (a * columnWord F n v) * (columnWord F n w)⁻¹ := by simp
      _ = a⁻¹ * (b * columnWord F n w) * (columnWord F n w)⁻¹ := by rw [heq]
      _ = _ := by simp [mul_assoc]
  obtain ⟨A, hA, _, _⟩ := exists_stage_matrix_actions F n (a⁻¹ * b)
    ((stage F n).mul_mem ((stage F n).inv_mem ha) hb)
  have hz : columnWord F n (v - w) = 1 :=
    columnWord_eq_one_of_old_image F n (v - w) A (by rw [hword, hA])
  have hvw : v = w :=
    sub_eq_zero.mp (columnWord_injective F n (hz.trans (columnWord_zero F n).symm))
  subst w
  exact ⟨mul_right_cancel heq, rfl⟩

/-- Every element of the collected subgroup has a unique original source factorization. -/
theorem unique_upperParabolic_normalForm (n : ℕ) (g : Group F) (hg : g ∈ upperParabolic F n) :
    ∃! z : stage F n × (Fin n → F), g = (z.1 : Group F) * columnWord F n z.2 := by
  obtain ⟨a, ha, v, hav⟩ := (mem_upperParabolic F n g).mp hg
  refine ⟨(⟨a, ha⟩, v), hav, ?_⟩
  intro z hz
  obtain ⟨heq, hvec⟩ := collected_product_unique F n z.1 a z.1.property ha z.2 v
    (hz.symm.trans hav)
  exact Prod.ext (Subtype.ext heq) hvec

/-- A kernel word in the collected subgroup descends to the old actual stage. -/
theorem upperParabolic_kernel_descent (n : ℕ) {g : Group F}
    (hg : g ∈ upperParabolic F n) (hk : toElementary F g = 1) : g ∈ stage F n := by
  obtain ⟨a, ha, v, rfl⟩ := (mem_upperParabolic F n g).mp hg
  obtain ⟨A, hA, _, _⟩ := exists_stage_matrix_actions F n a ha
  have hk' : toStableGeneralLinear F (a * columnWord F n v) = 1 := congrArg Subtype.val hk
  rw [map_mul, hA] at hk'
  have hcol : toStableGeneralLinear F (columnWord F n v) = StableGeneralLinear.of F n A⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right hk'
  rw [columnWord_eq_one_of_old_image F n v A⁻¹ hcol, mul_one]
  exact ha

/-- The collected subgroup introduces no kernel beyond the old-stage kernel. -/
theorem upperParabolic_inf_kernel (n : ℕ) :
    upperParabolic F n ⊓ (toElementary F).ker = stage F n ⊓ (toElementary F).ker := by
  apply le_antisymm
  · intro g hg
    exact ⟨upperParabolic_kernel_descent F n hg.1 hg.2, hg.2⟩
  · exact inf_le_inf le_sup_left le_rfl

/-- For old rank at least two, all original ordered defects lie in the collected subgroup. -/
lemma defects_le_upperParabolic (n : ℕ) (hn : 2 ≤ n) :
    defectSubgroup F ≤ upperParabolic F n :=
  (defectSubgroup_le_stage_two (F := F)).trans ((stage_mono F hn).trans le_sup_left)

/-- Modulo-C membership lifts because C already lies in the collected subgroup. -/
lemma mem_upperParabolic_of_quotient_mem (n : ℕ) (hn : 2 ≤ n) (g : Group F)
    (hg : (QuotientGroup.mk' (defectSubgroup F)) g ∈
      (upperParabolic F n).map (QuotientGroup.mk' (defectSubgroup F))) :
    g ∈ upperParabolic F n := by
  obtain ⟨a, ha, hag⟩ := hg
  have hga : g * a⁻¹ ∈ defectSubgroup F := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (defectSubgroup F)) (g * a⁻¹) = 1
    rw [map_mul, map_inv, hag, mul_inv_cancel]
  have hm := (upperParabolic F n).mul_mem (defects_le_upperParabolic F n hn hga) ha
  simpa only [inv_mul_cancel_right] using hm

/-- Quotient-parabolic membership suffices for actual old-stage kernel descent. -/
theorem stage_kernel_descent_of_quotient_parabolic (n : ℕ) (hn : 2 ≤ n) (g : Group F)
    (hk : toElementary F g = 1)
    (hp : (QuotientGroup.mk' (defectSubgroup F)) g ∈
      (upperParabolic F n).map (QuotientGroup.mk' (defectSubgroup F))) :
    g ∈ stage F n :=
  upperParabolic_kernel_descent F n (mem_upperParabolic_of_quotient_mem F n hn g hp) hk

/-- The frozen rank-two kernel theorem persists under actual inner conjugation. -/
lemma conjugate_stage_two_kernel_mem_defects (s a : Group F) (ha : a ∈ stage F 2)
    (hk : toElementary F (s * a * s⁻¹) = 1) : s * a * s⁻¹ ∈ defectSubgroup F := by
  have hka : toElementary F a = 1 := by
    have hh := congrArg (fun z => (toElementary F s)⁻¹ * z * toElementary F s) hk
    simpa [map_mul, map_inv, mul_assoc] using hh
  have hCa := stage_two_kernel_mem_defectSubgroup ha hka
  have hcomm := Subgroup.mem_center_iff.mp (defectSubgroup_le_center F hCa) s
  rw [hcomm, mul_inv_cancel_right]
  exact hCa

/-- For original rank-two words, equal elementary images imply equality modulo C. -/
lemma quotient_eq_of_stage_two_images (a b : Group F) (ha : a ∈ stage F 2)
    (hb : b ∈ stage F 2) (hab : toElementary F a = toElementary F b) :
    (QuotientGroup.mk' (defectSubgroup F)) a = (QuotientGroup.mk' (defectSubgroup F)) b := by
  apply mul_inv_eq_one.mp
  rw [← map_inv, ← map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply stage_two_kernel_mem_defectSubgroup ((stage F 2).mul_mem ha ((stage F 2).inv_mem hb))
  simp [map_mul, map_inv, hab]

/-- Equal original elementary images have a central source difference. -/
lemma central_difference_of_same_image (a b : Group F)
    (hab : toElementary F a = toElementary F b) : a * b⁻¹ ∈ Subgroup.center (Group F) :=
  ker_toElementary_le_center F (by simp [MonoidHom.mem_ker, map_mul, map_inv, hab])

/-- Conjugated replacement retains its exact central source discrepancy. -/
lemma conjugate_replace_same_image (s a b : Group F)
    (hab : toElementary F a = toElementary F b) :
    s * a * s⁻¹ = (a * b⁻¹) * (s * b * s⁻¹) := by
  have hc : s * (a * b⁻¹) = (a * b⁻¹) * s :=
    Subgroup.mem_center_iff.mp (central_difference_of_same_image F a b hab) s
  calc
    _ = s * (a * b⁻¹) * b * s⁻¹ := by simp [mul_assoc]
    _ = _ := by rw [hc]; simp only [mul_assoc]

/-- Replacement of old-stage words retains a central error in that same old stage. -/
lemma conjugate_old_stage_replacement (n : ℕ) (s a b : Group F)
    (ha : a ∈ stage F n) (hb : b ∈ stage F n)
    (hab : toElementary F a = toElementary F b) :
    ∃ k : Group F, k ∈ stage F n ∧ toElementary F k = 1 ∧
      s * a * s⁻¹ = k * (s * b * s⁻¹) := by
  refine ⟨a * b⁻¹, (stage F n).mul_mem ha ((stage F n).inv_mem hb), ?_, ?_⟩
  · simp [map_mul, map_inv, hab]
  · exact conjugate_replace_same_image F s a b hab

end StableSteinberg.KernelGeneration.Parabolic

namespace StableSteinberg.KernelGeneration.RootRelocation
open scoped commutatorElement
variable (F : Type u) [Field F]

private lemma conjugate_of_commute (a b : Group F) (hab : Commute a b) : a * b * a⁻¹ = b := by
  rw [hab.eq, mul_inv_cancel_right]

private lemma root_conj_chain (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) :
    x F n i j hij a * x F n j k hjk b * (x F n i j hij a)⁻¹ =
      x F n i k hik (a * b) * x F n j k hjk b := by
  calc
    _ = ⁅x F n i j hij a, x F n j k hjk b⁆ * x F n j k hjk b := by
      simp [commutatorElement_def, mul_assoc]
    _ = _ := by rw [x_commutator]

private lemma root_conj_reverse (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) :
    x F n j k hjk b * x F n i j hij a * (x F n j k hjk b)⁻¹ =
      x F n i k hik (-(a * b)) * x F n i j hij a := by
  calc
    _ = ⁅x F n j k hjk b, x F n i j hij a⁆ * x F n i j hij a := by
      simp [commutatorElement_def, mul_assoc]
    _ = (⁅x F n i j hij a, x F n j k hjk b⁆)⁻¹ * x F n i j hij a := by
      rw [commutatorElement_inv]
    _ = _ := by rw [x_commutator, x_neg]

/-- The literal finite Weyl shift with coefficients -1, 1, -1. -/
def rootShift (n : ℕ) (j k : Fin n) (hjk : j ≠ k) : Group F :=
  x F n j k hjk (-1) * x F n k j hjk.symm 1 * x F n j k hjk (-1)

/-- The literal shift moves an upper ordered root with its positive coefficient unchanged. -/
lemma rootShift_conj_upper (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (t : F) :
    rootShift F n j k hjk * x F n i j hij t * (rootShift F n j k hjk)⁻¹ =
      x F n i k hik t := by
  let A := x F n j k hjk (-1)
  let B := x F n k j hjk.symm 1
  let X := x F n i j hij t
  let Y := x F n i k hik t
  have hAX : A * X * A⁻¹ = Y * X := by
    simpa [A, X, Y] using root_conj_reverse F n i j k hij hjk hik t (-1)
  have hBY : B * Y * B⁻¹ = X⁻¹ * Y := by
    simpa [B, X, Y, x_neg] using root_conj_reverse F n i k j hik hjk.symm hij t 1
  have hBX : B * X * B⁻¹ = X :=
    conjugate_of_commute F B X (x_commute F n k j i j hjk.symm hij hij.symm hjk 1 t)
  have hAY : A * Y * A⁻¹ = Y :=
    conjugate_of_commute F A Y (x_commute F n j k i k hjk hik hik.symm hjk.symm (-1) t)
  have hXY : Commute X Y := x_commute F n i j i k hij hik hij.symm hik.symm t t
  calc
    _ = A * (B * (A * X * A⁻¹) * B⁻¹) * A⁻¹ := by
      simp only [rootShift, A, B, X, mul_inv_rev, mul_assoc]
    _ = A * ((B * Y * B⁻¹) * (B * X * B⁻¹)) * A⁻¹ := by
      rw [hAX]
      simp only [mul_assoc, inv_mul_cancel_left]
    _ = Y := by rw [hBY, hBX, hXY.inv_mul_cancel, hAY]

/-- The same literal shift moves the reversed root with its positive coefficient unchanged. -/
lemma rootShift_conj_lower (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (t : F) :
    rootShift F n j k hjk * x F n j i hij.symm t * (rootShift F n j k hjk)⁻¹ =
      x F n k i hik.symm t := by
  let A := x F n j k hjk (-1)
  let B := x F n k j hjk.symm 1
  let X := x F n j i hij.symm t
  let Y := x F n k i hik.symm t
  have hAX : A * X * A⁻¹ = X :=
    conjugate_of_commute F A X (x_commute F n j k j i hjk hij.symm hjk.symm hij (-1) t)
  have hBX : B * X * B⁻¹ = Y * X := by
    simpa [B, X, Y] using root_conj_chain F n k j i hjk.symm hij.symm hik.symm 1 t
  have hAY : A * Y * A⁻¹ = X⁻¹ * Y := by
    simpa [A, X, Y, x_neg] using root_conj_chain F n j k i hjk hik.symm hij.symm (-1) t
  have hXY : Commute X Y := x_commute F n j i k i hij.symm hik.symm hik hij t t
  calc
    _ = A * (B * (A * X * A⁻¹) * B⁻¹) * A⁻¹ := by
      simp only [rootShift, A, B, X, mul_inv_rev, mul_assoc]
    _ = (A * Y * A⁻¹) * (A * X * A⁻¹) := by
      conv_lhs => rw [hAX, hBX]
      simp only [mul_assoc, inv_mul_cancel_left]
    _ = Y := by rw [hAY, hAX, hXY.inv_mul_cancel]

/-- The original three-root Weyl word at an arbitrary actual finite ordered pair. -/
def pairW (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) : Group F :=
  x F n i j hij (a : F) * x F n j i hij.symm (-((a⁻¹ : Fˣ) : F)) * x F n i j hij a

/-- The original normalized torus word at an actual finite ordered pair. -/
def pairH (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) : Group F :=
  pairW F n i j hij a * pairW F n i j hij (-1 : Fˣ)

/-- The ordered torus defect at an actual finite pair. -/
def pairDefect (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a b : Fˣ) : Group F :=
  pairH F n i j hij a * pairH F n i j hij b * (pairH F n i j hij (a * b))⁻¹

/-- The literal shift conjugates the complete Weyl word to the moved pair. -/
lemma rootShift_conj_pairW (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a : Fˣ) :
    rootShift F n j k hjk * pairW F n i j hij a * (rootShift F n j k hjk)⁻¹ =
      pairW F n i k hik a := by
  let s := rootShift F n j k hjk
  calc
    _ = (s * x F n i j hij a * s⁻¹) *
        (s * x F n j i hij.symm (-((a⁻¹ : Fˣ) : F)) * s⁻¹) *
        (s * x F n i j hij a * s⁻¹) := by simp [pairW, s, mul_assoc]
    _ = _ := by
      change (rootShift F n j k hjk * _ * _) * (rootShift F n j k hjk * _ * _) *
        (rootShift F n j k hjk * _ * _) = _
      rw [rootShift_conj_upper F n i j k hij hjk hik,
        rootShift_conj_lower F n i j k hij hjk hik]
      rfl

/-- The literal shift retains the torus normalization. -/
lemma rootShift_conj_pairH (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a : Fˣ) :
    rootShift F n j k hjk * pairH F n i j hij a * (rootShift F n j k hjk)⁻¹ =
      pairH F n i k hik a := by
  let s := rootShift F n j k hjk
  calc
    _ = (s * pairW F n i j hij a * s⁻¹) * (s * pairW F n i j hij (-1) * s⁻¹) := by
      simp [pairH, s, mul_assoc]
    _ = _ := by
      change (rootShift F n j k hjk * _ * _) * (rootShift F n j k hjk * _ * _) = _
      rw [rootShift_conj_pairW F n i j k hij hjk hik,
        rootShift_conj_pairW F n i j k hij hjk hik]
      rfl

/-- The literal shift retains the ordered defect word. -/
lemma rootShift_conj_pairDefect (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : Fˣ) :
    rootShift F n j k hjk * pairDefect F n i j hij a b * (rootShift F n j k hjk)⁻¹ =
      pairDefect F n i k hik a b := by
  change (MulAut.conj (rootShift F n j k hjk)) (pairDefect F n i j hij a b) = _
  simp only [pairDefect, map_mul, map_inv]
  change (rootShift F n j k hjk * pairH F n i j hij a * (rootShift F n j k hjk)⁻¹) *
    (rootShift F n j k hjk * pairH F n i j hij b * (rootShift F n j k hjk)⁻¹) *
    (rootShift F n j k hjk * pairH F n i j hij (a * b) * (rootShift F n j k hjk)⁻¹)⁻¹ = _
  rw [rootShift_conj_pairH F n i j k hij hjk hik,
    rootShift_conj_pairH F n i j k hij hjk hik,
    rootShift_conj_pairH F n i j k hij hjk hik]

private lemma x_castLE {n m : ℕ} (hnm : n ≤ m) (i j : Fin n) (hij : i ≠ j) (a : F) :
    x F n i j hij a = x F m (i.castLE hnm) (j.castLE hnm)
      (by intro he; exact hij (Fin.ext (congrArg (fun z : Fin m => z.val) he))) a := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m h ih =>
    calc
      _ = x F m (i.castLE h) (j.castLE h) _ a := ih
      _ = _ := by simpa using x_stabilize F m (i.castLE h) (j.castLE h) _ a

/-- Iterated actual stabilization transports the entire Weyl word. -/
lemma pairW_castLE {n m : ℕ} (hnm : n ≤ m) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    pairW F n i j hij a = pairW F m (i.castLE hnm) (j.castLE hnm)
      (by intro he; exact hij (Fin.ext (congrArg (fun z : Fin m => z.val) he))) a := by
  simp only [pairW]
  rw [x_castLE F hnm i j hij (a : F),
    x_castLE F hnm j i hij.symm (-((a⁻¹ : Fˣ) : F))]

/-- Iterated actual stabilization transports the normalized torus word. -/
lemma pairH_castLE {n m : ℕ} (hnm : n ≤ m) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    pairH F n i j hij a = pairH F m (i.castLE hnm) (j.castLE hnm)
      (by intro he; exact hij (Fin.ext (congrArg (fun z : Fin m => z.val) he))) a := by
  simp only [pairH]
  rw [pairW_castLE F hnm i j hij a, pairW_castLE F hnm i j hij (-1)]

/-- Iterated actual stabilization retains the ordered defect. -/
lemma pairDefect_castLE {n m : ℕ} (hnm : n ≤ m) (i j : Fin n) (hij : i ≠ j) (a b : Fˣ) :
    pairDefect F n i j hij a b = pairDefect F m (i.castLE hnm) (j.castLE hnm)
      (by intro he; exact hij (Fin.ext (congrArg (fun z : Fin m => z.val) he))) a b := by
  simp only [pairDefect]
  rw [pairH_castLE F hnm i j hij a, pairH_castLE F hnm i j hij b,
    pairH_castLE F hnm i j hij (a * b)]

/-- Every pivot pair starting at zero has exactly the original positive ordered defect. -/
lemma pivotDefect_eq (n : ℕ) (hn : 2 ≤ n) (k : Fin n)
    (hk : (0 : Fin 2).castLE hn ≠ k) (a b : Fˣ) :
    pairDefect F n ((0 : Fin 2).castLE hn) k hk a b = torusDefect a b := by
  let i : Fin n := (0 : Fin 2).castLE hn
  let j : Fin n := (1 : Fin 2).castLE hn
  have hij : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change (0 : ℕ) = 1 at hv
    omega
  have hbase : pairDefect F n i j hij a b = torusDefect a b :=
    (pairDefect_castLE F hn (0 : Fin 2) 1 (by decide) a b).symm
  by_cases hjk : j = k
  · subst k
    exact hbase
  · have hs := rootShift_conj_pairDefect F n i j k hij hjk hk a b
    rw [hbase] at hs
    calc
      _ = rootShift F n j k hjk * torusDefect a b * (rootShift F n j k hjk)⁻¹ := hs.symm
      _ = _ := by
        apply conjugate_of_commute
        exact Subgroup.mem_center_iff.mp
          (ker_toElementary_le_center F (toElementary_torusDefect a b)) _

/-- The literal pivot-pair torus becomes multiplicative in the original defect quotient. -/
lemma pivot_h_mul_in_quotient (n : ℕ) (hn : 2 ≤ n) (k : Fin n)
    (hk : (0 : Fin 2).castLE hn ≠ k) (a b : Fˣ) :
    (QuotientGroup.mk' (defectSubgroup F)) (pairH F n ((0 : Fin 2).castLE hn) k hk a) *
      (QuotientGroup.mk' (defectSubgroup F)) (pairH F n ((0 : Fin 2).castLE hn) k hk b) =
        (QuotientGroup.mk' (defectSubgroup F))
          (pairH F n ((0 : Fin 2).castLE hn) k hk (a * b)) := by
  apply mul_inv_eq_one.mp
  rw [← map_inv, ← map_mul, ← map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  change pairDefect F n ((0 : Fin 2).castLE hn) k hk a b ∈ defectSubgroup F
  rw [pivotDefect_eq F n hn k hk]
  exact Subgroup.subset_closure ⟨a, b, rfl⟩

/-- The subgroup generated by both original roots of the finite pivot pair. -/
def pivotStage (n : ℕ) (hn : 2 ≤ n) (k : Fin n)
    (hk : (0 : Fin 2).castLE hn ≠ k) : Subgroup (Group F) :=
  Subgroup.closure {g | ∃ t : F,
    g = x F n ((0 : Fin 2).castLE hn) k hk t ∨
      g = x F n k ((0 : Fin 2).castLE hn) hk.symm t}

/-- Actual conjugation transfers the rank-two kernel theorem to every pivot pair. -/
theorem pivot_stage_kernel_mem_defects (n : ℕ) (hn : 2 ≤ n) (k : Fin n)
    (hk : (0 : Fin 2).castLE hn ≠ k) (z : Group F)
    (hz : z ∈ pivotStage F n hn k hk) (hker : toElementary F z = 1) :
    z ∈ defectSubgroup F := by
  let i : Fin n := (0 : Fin 2).castLE hn
  let j : Fin n := (1 : Fin 2).castLE hn
  have hij : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change (0 : ℕ) = 1 at hv
    omega
  have hU (t : F) : x F 2 0 1 (by decide) t = x F n i j hij t :=
    x_castLE F hn (0 : Fin 2) 1 (by decide) t
  have hV (t : F) : x F 2 1 0 (by decide) t = x F n j i hij.symm t :=
    x_castLE F hn (1 : Fin 2) 0 (by decide) t
  by_cases hjk : j = k
  · subst k
    have hle : pivotStage F n hn j hk ≤ stage F 2 := by
      apply (Subgroup.closure_le _).mpr
      rintro a ⟨t, rfl | rfl⟩
      · change x F n i j hij t ∈ stage F 2
        rw [← hU]
        exact x_mem_stage F 2 0 1 (by decide) t
      · change x F n j i hij.symm t ∈ stage F 2
        rw [← hV]
        exact x_mem_stage F 2 1 0 (by decide) t
    exact stage_two_kernel_mem_defectSubgroup (hle hz) hker
  · let s := rootShift F n j k hjk
    have hUs (t : F) : s * x F 2 0 1 (by decide) t * s⁻¹ = x F n i k hk t := by
      rw [hU]
      exact rootShift_conj_upper F n i j k hij hjk hk t
    have hVs (t : F) : s * x F 2 1 0 (by decide) t * s⁻¹ = x F n k i hk.symm t := by
      rw [hV]
      exact rootShift_conj_lower F n i j k hij hjk hk t
    have hle : pivotStage F n hn k hk ≤ (stage F 2).map (MulAut.conj s).toMonoidHom := by
      apply (Subgroup.closure_le _).mpr
      rintro a ⟨t, rfl | rfl⟩
      · exact ⟨x F 2 0 1 (by decide) t, x_mem_stage F 2 0 1 (by decide) t, hUs t⟩
      · exact ⟨x F 2 1 0 (by decide) t, x_mem_stage F 2 1 0 (by decide) t, hVs t⟩
    obtain ⟨a, ha, haz⟩ := hle hz
    have haz' : s * a * s⁻¹ = z := haz
    have hker' : toElementary F (s * a * s⁻¹) = 1 :=
      (congrArg (toElementary F) haz').trans hker
    have hh := Parabolic.conjugate_stage_two_kernel_mem_defects F s a ha hker'
    rwa [haz'] at hh

/-- Matrix-image equality is valid modulo C for words in the same proved pivot subgroup. -/
theorem pivot_quotient_eq_of_same_image (n : ℕ) (hn : 2 ≤ n) (k : Fin n)
    (hk : (0 : Fin 2).castLE hn ≠ k) (a b : Group F)
    (ha : a ∈ pivotStage F n hn k hk) (hb : b ∈ pivotStage F n hn k hk)
    (hab : toElementary F a = toElementary F b) :
    (QuotientGroup.mk' (defectSubgroup F)) a = (QuotientGroup.mk' (defectSubgroup F)) b := by
  apply mul_inv_eq_one.mp
  rw [← map_inv, ← map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply pivot_stage_kernel_mem_defects F n hn k hk (a * b⁻¹)
    ((pivotStage F n hn k hk).mul_mem ha ((pivotStage F n hn k hk).inv_mem hb))
  simp [map_mul, map_inv, hab]

end StableSteinberg.KernelGeneration.RootRelocation

namespace StableSteinberg.KernelGeneration.StageRowReduction
open scoped Matrix
variable (F : Type u) [Field F]

/-- An actual old-stage word and its literal matrix carry the first row vector to the second. -/
def RowReach (n : ℕ) (v w : Fin n → F) : Prop :=
  ∃ g : Group F, g ∈ stage F n ∧ ∃ A : Matrix.GeneralLinearGroup (Fin n) F,
    toStableGeneralLinear F g = StableGeneralLinear.of F n A ∧ v ᵥ* A.val = w

lemma rowReach_refl (n : ℕ) (v : Fin n → F) : RowReach F n v v :=
  ⟨1, (stage F n).one_mem, 1, by simp, by simp⟩

lemma rowReach_trans (n : ℕ) {v w z : Fin n → F}
    (hvw : RowReach F n v w) (hwz : RowReach F n w z) : RowReach F n v z := by
  obtain ⟨g, hg, A, hA, hv⟩ := hvw
  obtain ⟨h, hh, B, hB, hw⟩ := hwz
  refine ⟨g * h, (stage F n).mul_mem hg hh, A * B, ?_, ?_⟩
  · simp only [map_mul, hA, hB]
  · change v ᵥ* (A.val * B.val) = z
    rw [← Matrix.vecMul_vecMul, hv, hw]

lemma rowReach_symm (n : ℕ) {v w : Fin n → F} (hvw : RowReach F n v w) :
    RowReach F n w v := by
  obtain ⟨g, hg, A, hA, hv⟩ := hvw
  refine ⟨g⁻¹, (stage F n).inv_mem hg, A⁻¹, ?_, ?_⟩
  · simp only [map_inv, hA]
  · rw [← hv, Matrix.vecMul_vecMul]
    have hAA : A.val * (A⁻¹).val = 1 := A.val_inv
    rw [hAA, Matrix.vecMul_one]

private lemma elementary_vecMul (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (a : F) (v : Fin n → F) :
    v ᵥ* (Matrix.GeneralLinearGroup.elementary i j hij a).val = v + Pi.single j (v i * a) := by
  rw [Matrix.GeneralLinearGroup.elementary_val, Matrix.vecMul_add,
    Matrix.vecMul_one]
  congr 1
  ext k
  by_cases hk : k = j
  · subst k
    simp [Matrix.vecMul, dotProduct, Matrix.single]
  · simp [Matrix.vecMul, dotProduct, Matrix.single, hk, (Ne.symm hk)]

lemma rowReach_add_single (n : ℕ) (v : Fin n → F) (i j : Fin n) (hij : i ≠ j) (a : F) :
    RowReach F n v (v + Pi.single j (v i * a)) :=
  ⟨x F n i j hij a, x_mem_stage F n i j hij a, Matrix.GeneralLinearGroup.elementary i j hij a,
    toStableGeneralLinear_x F n i j hij a, elementary_vecMul F n i j hij a v⟩

lemma rowReach_clear_coordinate (n : ℕ) (v : Fin n → F) (i j : Fin n)
    (hij : i ≠ j) (hi : v i ≠ 0) : RowReach F n v (v + Pi.single j (-v j)) := by
  convert rowReach_add_single F n v i j hij (-v j / v i) using 1
  congr 1
  field_simp

lemma rowReach_clear_finset (n : ℕ) (v : Fin n → F) (i : Fin n) (hi : v i ≠ 0)
    (s : Finset (Fin n)) :
    ∃ w : Fin n → F, RowReach F n v w ∧ w i = v i ∧ ∀ j ∈ s, j ≠ i → w j = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨v, rowReach_refl F n v, rfl, by simp⟩
  | @insert j s hjs ih =>
    obtain ⟨w, hw, hwi, hws⟩ := ih
    by_cases hji : j = i
    · refine ⟨w, hw, hwi, ?_⟩
      intro k hk hki
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact (hki hji).elim
      · exact hws k hk hki
    · refine ⟨w + Pi.single j (-w j),
        rowReach_trans F n hw (rowReach_clear_coordinate F n w i j (Ne.symm hji) (hwi ▸ hi)),
        ?_, ?_⟩
      · simp [hwi, (Ne.symm hji)]
      · intro k hk hki
        by_cases hkj : k = j
        · subst k
          simp
        · have hks : k ∈ s := (Finset.mem_insert.mp hk).resolve_left hkj
          simp [ hkj, hws k hks hki]

lemma rowReach_single_of_pivot (n : ℕ) (v : Fin n → F) (i : Fin n) (hi : v i ≠ 0) :
    RowReach F n v (Pi.single i (v i)) := by
  obtain ⟨w, hw, hwi, hws⟩ := rowReach_clear_finset F n v i hi Finset.univ
  have he : w = Pi.single i (v i) := by
    ext j
    by_cases hji : j = i
    · subst j
      simpa using hwi
    · simp [ hji, hws j (Finset.mem_univ _) hji]
  rwa [← he]

lemma rowReach_single_normalize (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (a : F) (ha : a ≠ 0) : RowReach F n (Pi.single i a) (Pi.single i 1) := by
  let v : Fin n → F := Pi.single i a
  let w : Fin n → F := v + Pi.single j a
  let z : Fin n → F := Pi.single i 1 + Pi.single j a
  have hvw : RowReach F n v w := by
    convert rowReach_add_single F n v i j hij 1 using 1
    simp [v, w]
  have hwz : RowReach F n w z := by
    convert rowReach_add_single F n w j i hij.symm (a⁻¹ - 1) using 1
    ext k
    by_cases hki : k = i
    · subst k
      simp [w, z, v, hij, hij.symm, mul_sub, ha]
    · by_cases hkj : k = j
      · subst k
        simp [w, z, v, hij.symm]
      · simp [w, z, v, hki, hkj]
  have hze : RowReach F n z (Pi.single i 1) := by
    convert rowReach_add_single F n z i j hij (-a) using 1
    ext k
    by_cases hki : k = i
    · subst k
      simp [z, hij]
    · by_cases hkj : k = j
      · subst k
        simp [z, hij, hij.symm]
      · simp [z, hki, hkj]
  exact rowReach_trans F n hvw (rowReach_trans F n hwz hze)

/-- Finite elementary row operations, with an actual source witness, normalize every nonzero row. -/
theorem rowReach_nonzero_to_single (n : ℕ) (hn : 2 ≤ n) (v : Fin n → F) (hv : v ≠ 0)
    (i : Fin n) : RowReach F n v (Pi.single i 1) := by
  have hpair : ∃ j : Fin n, i ≠ j := by
    let zero : Fin n := ⟨0, by omega⟩
    let one : Fin n := ⟨1, by omega⟩
    by_cases hi : i = zero
    · refine ⟨one, ?_⟩
      intro he
      have hz : zero = one := hi.symm.trans he
      have h01 := congrArg Fin.val hz
      change (0 : ℕ) = 1 at h01
      omega
    · exact ⟨zero, hi⟩
  obtain ⟨j, hij⟩ := hpair
  by_cases hvi : v i ≠ 0
  · exact rowReach_trans F n (rowReach_single_of_pivot F n v i hvi)
      (rowReach_single_normalize F n i j hij (v i) hvi)
  · have hvi0 : v i = 0 := not_not.mp hvi
    obtain ⟨k, hk⟩ : ∃ k : Fin n, v k ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    have hki : k ≠ i := by intro he; exact hk (he ▸ hvi0)
    let w := v + Pi.single i (v k)
    have hw : w i ≠ 0 := by simpa [w, hvi0] using hk
    have hvw : RowReach F n v w := by simpa only [mul_one] using rowReach_add_single F n v k i hki 1
    exact rowReach_trans F n hvw (rowReach_trans F n (rowReach_single_of_pivot F n w i hw)
      (rowReach_single_normalize F n i j hij (w i) hw))

/-- The original old-stage elementary words act transitively on nonzero finite row vectors. -/
theorem rowReach_nonzero (n : ℕ) (hn : 2 ≤ n) (v w : Fin n → F) (hv : v ≠ 0) (hw : w ≠ 0) :
    RowReach F n v w := by
  let i : Fin n := ⟨0, by omega⟩
  exact rowReach_trans F n (rowReach_nonzero_to_single F n hn v hv i)
    (rowReach_symm F n (rowReach_nonzero_to_single F n hn w hw i))

end StableSteinberg.KernelGeneration.StageRowReduction
