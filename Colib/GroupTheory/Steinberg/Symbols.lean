/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Centrality
public import Colib.GroupTheory.Steinberg.Torus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Actual Steinberg symbols in the original elementary kernel

The literal ordered defect `h(a) h(b) h(ab)⁻¹` is bimultiplicative and is one
when `a + b = 1`. These statements are proved in the existing finite-rank-labelled
Steinberg presentation, over every field without a cardinality restriction.

Accepted fresh-column and fresh-row matrix actions give the needed exact source
conjugations. A literal rank-three Weyl word moves roots `01,10` to `02,20` with
positive coefficients. Kernel centrality identifies the corresponding defects,
and the source identity `[h(a), h02(b)] = c(b,a)⁻¹` proves multiplicativity through
explicit central-commutator formulas. The Steinberg relation has a separate word
calculation using root addition and `a + b = 1`.

The latter calculation is guided by Weibel, The K-book, III, Lemma 5.10.2:
https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.III.pdf .
All its required source conjugation identities are proved here from the original
presentation and finite matrix actions; no symbol relation is assumed.

The kernel commutative structure copies the existing group operations and is
activated only locally. No kernel generation, injectivity, Matsumoto equivalence,
or comparison with Quillen K₂ is asserted. The native Milnor symbol map is built
separately in `Colib.KTheory.MilnorK.Steinberg`.

## Implementation provenance

Adapted from the group-theoretic part of
`Quillen/Algebra/Group/StableSteinbergSymbols.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No Aglib model or API is imported.
-/
@[expose] public section

noncomputable section

universe u v

namespace StableSteinberg

open scoped commutatorElement Matrix

variable {F : Type u} [Field F]

private lemma stage_actions_of_image (n : ℕ) (g : Group F) (hg : g ∈ stage F n)
    (A : Matrix.GeneralLinearGroup (Fin n) F)
    (hA : toStableGeneralLinear F g = StableGeneralLinear.of F n A) :
    (∀ v, g * columnWord F n v * g⁻¹ = columnWord F n (A.val *ᵥ v)) ∧
      (∀ v, g * rowWord F n v * g⁻¹ = rowWord F n (v ᵥ* (A⁻¹).val)) := by
  obtain ⟨B, hB, hc, hr⟩ := exists_stage_matrix_actions F n g hg
  have he : B = A := StableGeneralLinear.of_injective F n (hB.symm.trans hA)
  simpa only [he] using And.intro hc hr

private lemma stage_conj_root_of_vectors (n : ℕ) (g : Group F) (hg : g ∈ stage F n)
    (A : Matrix.GeneralLinearGroup (Fin n) F)
    (hA : toStableGeneralLinear F g = StableGeneralLinear.of F n A)
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l) (t p q : F)
    (hc : A.val *ᵥ Pi.single i t = Pi.single k p)
    (hr : Pi.single j 1 ᵥ* (A⁻¹).val = Pi.single l q) :
    g * x F n i j hij t * g⁻¹ = x F n k l hkl (p * q) := by
  obtain ⟨hcol, hrow⟩ := stage_actions_of_image n g hg A hA
  have hi : g * x F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) t * g⁻¹ =
      x F (n + 1) k.castSucc (Fin.last n) (Fin.castSucc_ne_last k) p := by
    rw [← columnWord_single F n i t, hcol, hc, columnWord_single]
  have hj : g * x F (n + 1) (Fin.last n) j.castSucc (Fin.castSucc_ne_last j).symm 1 *
      g⁻¹ = x F (n + 1) (Fin.last n) l.castSucc (Fin.castSucc_ne_last l).symm q := by
    rw [← rowWord_single F n j 1, hrow, hr, rowWord_single]
  calc
    _ = ⁅g * x F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) t * g⁻¹,
        g * x F (n + 1) (Fin.last n) j.castSucc (Fin.castSucc_ne_last j).symm 1 * g⁻¹⁆ := by
      rw [x_eq_commutator_succ, conjugate_commutatorElement]
    _ = ⁅x F (n + 1) k.castSucc (Fin.last n) (Fin.castSucc_ne_last k) p,
        x F (n + 1) (Fin.last n) l.castSucc (Fin.castSucc_ne_last l).symm q⁆ := by rw [hi, hj]
    _ = x F (n + 1) k.castSucc l.castSucc (by simpa using hkl) (p * q) :=
      x_commutator F (n + 1) k.castSucc (Fin.last n) l.castSucc
        (Fin.castSucc_ne_last k) (Fin.castSucc_ne_last l).symm (by simpa using hkl) p q
    _ = _ := (x_stabilize F n k l hkl (p * q)).symm

private lemma w_mem_stage (a : Fˣ) : w a ∈ stage F 2 :=
  (stage F 2).mul_mem
    ((stage F 2).mul_mem (x_mem_stage F 2 0 1 (by decide) a)
      (x_mem_stage F 2 1 0 (by decide) (-((a⁻¹ : Fˣ) : F))))
    (x_mem_stage F 2 0 1 (by decide) a)

private lemma h_mem_stage (a : Fˣ) : h a ∈ stage F 2 :=
  (stage F 2).mul_mem (w_mem_stage a) (w_mem_stage (-1 : Fˣ))

private lemma wMatrix_inv_val (a : Fˣ) :
    ((wMatrix a)⁻¹).val = !![0, -(a : F); ((a⁻¹ : Fˣ) : F), 0] := by
  have he : wMatrix (-a) = (wMatrix a)⁻¹ :=
    StableGeneralLinear.of_injective F 2 (by
      rw [← toStableGeneralLinear_w, w_neg, map_inv, toStableGeneralLinear_w, map_inv])
  rw [← he, wMatrix_val]
  simp

local notation "U" => (x F 2 (0 : Fin 2) 1 (by decide))
local notation "V" => (x F 2 (1 : Fin 2) 0 (by decide))

private lemma w_lower_one_conj (a : Fˣ) :
    w a * V (1 : F) * (w a)⁻¹ = U (-((a : F) ^ 2)) := by
  have hc : (wMatrix a).val *ᵥ Pi.single (1 : Fin 2) (1 : F) =
      Pi.single (0 : Fin 2) (a : F) := by
    rw [wMatrix_val]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hr : Pi.single (0 : Fin 2) (1 : F) ᵥ* ((wMatrix a)⁻¹).val =
      Pi.single (1 : Fin 2) (-(a : F)) := by
    rw [wMatrix_inv_val]
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  have hh := stage_conj_root_of_vectors 2 (w a) (w_mem_stage a) (wMatrix a)
    (toStableGeneralLinear_w a) 1 0 0 1 (by decide) (by decide) 1 (a : F) (-(a : F)) hc hr
  simpa only [mul_neg, pow_two] using hh

private lemma w_lower_one (a : Fˣ) : w a * V (1 : F) = U (-((a : F) ^ 2)) * w a :=
  mul_inv_eq_iff_eq_mul.mp (w_lower_one_conj a)

private lemma lower_one_w (a : Fˣ) : V (1 : F) * w a = w a * U (-((a : F) ^ 2)) := by
  have hh := w_lower_one (-a)
  rw [w_neg] at hh
  simp only [Units.val_neg, neg_sq] at hh
  simpa [mul_assoc] using congrArg (fun z => w a * z * w a) hh

private lemma w_minus_one_alt : w (-1 : Fˣ) = V (1 : F) * U (-1 : F) * V (1 : F) := by
  have hh : w (-1 : Fˣ) * V (1 : F) = U (-1 : F) * w (-1 : Fˣ) := by
    simpa using w_lower_one (-1 : Fˣ)
  calc
    _ = U (1 : F) * (U (-1 : F) * w (-1 : Fˣ)) := by
      rw [← mul_assoc, x_add, add_neg_cancel, x_zero, one_mul]
    _ = U (1 : F) * (w (-1 : Fˣ) * V (1 : F)) := by rw [hh]
    _ = _ := by simp [w, ← mul_assoc, x_add, x_zero]

private lemma upper_add_mul (r s : F) (g : Group F) :
    U r * (U s * g) = U (r + s) * g := by rw [← mul_assoc, x_add]

private lemma lower_add_mul (r s : F) (g : Group F) :
    V r * (V s * g) = V (r + s) * g := by rw [← mul_assoc, x_add]

private lemma w_product_of_add_one (a b : Fˣ) (hab : (a : F) + (b : F) = 1) :
    w a * w (-1 : Fˣ) * w b = w (a * b) := by
  have ha : -((a : F) ^ 2) + (a : F) = (a : F) * (b : F) := by
    calc
      _ = (a : F) * (1 - (a : F)) := by ring
      _ = (a : F) * (((a : F) + (b : F)) - (a : F)) := by rw [hab]
      _ = _ := by ring
  have hb : (b : F) + -((b : F) ^ 2) = (a : F) * (b : F) := by
    calc
      _ = (b : F) * (1 - (b : F)) := by ring
      _ = (b : F) * (((a : F) + (b : F)) - (b : F)) := by rw [hab]
      _ = _ := by ring
  have hm : (a : F) + (-1) + (b : F) = 0 := by
    calc
      _ = (a : F) + (b : F) - 1 := by ring
      _ = 0 := by rw [hab, sub_self]
  have hi : -((a⁻¹ : Fˣ) : F) + -((b⁻¹ : Fˣ) : F) = -(((a * b)⁻¹ : Fˣ) : F) := by
    simp only [Units.val_inv_eq_inv_val, Units.val_mul]
    field_simp
    simpa only [← neg_add, add_comm] using congrArg (fun t : F => -t) hab
  calc
    _ = (w a * V (1 : F)) * U (-1 : F) * (V (1 : F) * w b) := by
      rw [w_minus_one_alt]
      simp only [mul_assoc]
    _ = (U (-((a : F) ^ 2)) * w a) * U (-1 : F) *
        (w b * U (-((b : F) ^ 2))) := by rw [w_lower_one, lower_one_w]
    _ = U ((a : F) * (b : F)) * V (-((a⁻¹ : Fˣ) : F)) *
        V (-((b⁻¹ : Fˣ) : F)) * U ((a : F) * (b : F)) := by
      simp only [w, mul_assoc]
      rw [upper_add_mul, upper_add_mul, upper_add_mul, ha, hm, x_zero, one_mul, x_add, hb]
    _ = _ := by
      simp only [w, Units.val_mul, mul_assoc]
      rw [lower_add_mul, hi]

/-- The literal ordered defect satisfies the Steinberg relation in the actual presentation. -/
lemma torusDefect_steinberg (a b : Fˣ) (hab : (a : F) + (b : F) = 1) :
    torusDefect a b = 1 := by
  have hh : h a * h b = h (a * b) := by
    calc
      _ = (w a * w (-1 : Fˣ) * w b) * w (-1 : Fˣ) := by simp only [h, mul_assoc]
      _ = _ := by rw [w_product_of_add_one a b hab, h]
  rw [torusDefect, hh, mul_inv_cancel]

/-- The literal rank-three Weyl word on the original roots `02` and `20`. -/
def w02 (a : Fˣ) : Group F :=
  x F 3 0 2 (by decide) (a : F) *
    x F 3 2 0 (by decide) (-((a⁻¹ : Fˣ) : F)) * x F 3 0 2 (by decide) (a : F)

/-- The literal rank-three torus word `w02(a) w02(-1)`. -/
def h02 (a : Fˣ) : Group F := w02 a * w02 (-1 : Fˣ)

private def defect02 (a b : Fˣ) : Group F := h02 a * h02 b * (h02 (a * b))⁻¹

private def shift (F : Type u) [Field F] : Group F :=
  x F 3 1 2 (by decide) (-1) * x F 3 2 1 (by decide) 1 * x F 3 1 2 (by decide) (-1)

private def shiftMatrix (F : Type u) [Field F] : Matrix.GeneralLinearGroup (Fin 3) F :=
  Matrix.GeneralLinearGroup.elementary (1 : Fin 3) 2 (by decide) (-1 : F) *
    Matrix.GeneralLinearGroup.elementary (2 : Fin 3) 1 (by decide) (1 : F) *
      Matrix.GeneralLinearGroup.elementary (1 : Fin 3) 2 (by decide) (-1 : F)

private lemma shift_mem_stage : shift F ∈ stage F 3 :=
  (stage F 3).mul_mem
    ((stage F 3).mul_mem (x_mem_stage F 3 1 2 (by decide) (-1))
      (x_mem_stage F 3 2 1 (by decide) 1))
    (x_mem_stage F 3 1 2 (by decide) (-1))

private lemma shift_image :
    toStableGeneralLinear F (shift F) = StableGeneralLinear.of F 3 (shiftMatrix F) := by
  simp only [shift, shiftMatrix, map_mul, toStableGeneralLinear_x]

private lemma shiftMatrix_val :
    (shiftMatrix F).val = !![(1 : F), 0, 0; 0, 0, -1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shiftMatrix, Units.val_mul, Matrix.GeneralLinearGroup.elementary_val,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single, Matrix.one_apply]

private lemma shiftMatrix_inv_val :
    ((shiftMatrix F)⁻¹).val = !![(1 : F), 0, 0; 0, 0, 1; 0, -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shiftMatrix, mul_inv_rev, Matrix.GeneralLinearGroup.elementary_inv, Units.val_mul,
      Matrix.GeneralLinearGroup.elementary_val, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.single, Matrix.one_apply]

private lemma shift_upper (t : F) :
    shift F * U t * (shift F)⁻¹ = x F 3 0 2 (by decide) t := by
  have hc : (shiftMatrix F).val *ᵥ Pi.single (0 : Fin 3) t = Pi.single (0 : Fin 3) t := by
    rw [shiftMatrix_val]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hr : Pi.single (1 : Fin 3) (1 : F) ᵥ* ((shiftMatrix F)⁻¹).val =
      Pi.single (2 : Fin 3) (1 : F) := by
    rw [shiftMatrix_inv_val]
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  rw [x_stabilize F 2 (0 : Fin 2) 1 (by decide) t]
  simpa only [mul_one, show (0 : Fin 2).castSucc = (0 : Fin 3) from by decide,
    show (1 : Fin 2).castSucc = (1 : Fin 3) from by decide] using
    stage_conj_root_of_vectors 3 (shift F) shift_mem_stage
    (shiftMatrix F) shift_image 0 1 0 2 (by decide) (by decide) t t 1 hc hr

private lemma shift_lower (t : F) :
    shift F * V t * (shift F)⁻¹ = x F 3 2 0 (by decide) t := by
  have hc : (shiftMatrix F).val *ᵥ Pi.single (1 : Fin 3) t = Pi.single (2 : Fin 3) t := by
    rw [shiftMatrix_val]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hr : Pi.single (0 : Fin 3) (1 : F) ᵥ* ((shiftMatrix F)⁻¹).val =
      Pi.single (0 : Fin 3) (1 : F) := by
    rw [shiftMatrix_inv_val]
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  rw [x_stabilize F 2 (1 : Fin 2) 0 (by decide) t]
  simpa only [mul_one, show (0 : Fin 2).castSucc = (0 : Fin 3) from by decide,
    show (1 : Fin 2).castSucc = (1 : Fin 3) from by decide] using
    stage_conj_root_of_vectors 3 (shift F) shift_mem_stage
    (shiftMatrix F) shift_image 1 0 2 0 (by decide) (by decide) t t 1 hc hr

private lemma shift_conj_w (a : Fˣ) : shift F * w a * (shift F)⁻¹ = w02 a := by
  calc
    _ = (shift F * U (a : F) * (shift F)⁻¹) *
        (shift F * V (-((a⁻¹ : Fˣ) : F)) * (shift F)⁻¹) *
          (shift F * U (a : F) * (shift F)⁻¹) := by rw [w]; simp [mul_assoc]
    _ = _ := by rw [shift_upper, shift_lower, w02]

private lemma shift_conj_h (a : Fˣ) : shift F * h a * (shift F)⁻¹ = h02 a := by
  calc
    _ = (shift F * w a * (shift F)⁻¹) *
        (shift F * w (-1 : Fˣ) * (shift F)⁻¹) := by rw [h]; simp [mul_assoc]
    _ = _ := by rw [shift_conj_w, shift_conj_w, h02]

private lemma shift_conj_defect (a b : Fˣ) :
    shift F * torusDefect a b * (shift F)⁻¹ = defect02 a b := by
  change (MulAut.conj (shift F)) (torusDefect a b) = _
  simp only [torusDefect, map_mul, map_inv]
  change (shift F * h a * (shift F)⁻¹) * (shift F * h b * (shift F)⁻¹) *
    (shift F * h (a * b) * (shift F)⁻¹)⁻¹ = _
  rw [shift_conj_h, shift_conj_h, shift_conj_h]
  rfl

private lemma torusDefect_commute (a b : Fˣ) (g : Group F) :
    Commute g (torusDefect a b) := by
  have hc : torusDefect a b ∈ Subgroup.center (Group F) :=
    ker_toElementary_le_center F (torusDefectKernel a b).property
  exact Subgroup.mem_center_iff.mp hc g

private lemma defect02_eq (a b : Fˣ) : defect02 a b = torusDefect a b := by
  rw [← shift_conj_defect, (torusDefect_commute a b (shift F)).eq, mul_inv_cancel_right]

private lemma hMatrix_inv_val (a : Fˣ) :
    ((hMatrix a)⁻¹).val = Matrix.diagonal ![((a⁻¹ : Fˣ) : F), (a : F)] := by
  have hone : hMatrix (1 : Fˣ) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hMatrix_val]
  have hh : hMatrix a * hMatrix (a⁻¹) = 1 := by
    rw [hMatrix_mul, mul_inv_cancel, hone]
  have he : hMatrix (a⁻¹) = (hMatrix a)⁻¹ := eq_inv_of_mul_eq_one_right hh
  rw [← he, hMatrix_val]
  simp

private lemma h_conj_upper02 (a : Fˣ) (t : F) :
    h a * x F 3 0 2 (by decide) t * (h a)⁻¹ = x F 3 0 2 (by decide) ((a : F) * t) := by
  obtain ⟨hc, _⟩ := stage_actions_of_image 2 (h a) (h_mem_stage a) (hMatrix a)
    (toStableGeneralLinear_h a)
  have hv : (hMatrix a).val *ᵥ Pi.single (0 : Fin 2) t =
      Pi.single (0 : Fin 2) ((a : F) * t) := by
    rw [hMatrix_val]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hh := hc (Pi.single (0 : Fin 2) t)
  rw [columnWord_single, hv, columnWord_single] at hh
  exact hh

private lemma h_conj_lower02 (a : Fˣ) (t : F) :
    h a * x F 3 2 0 (by decide) t * (h a)⁻¹ =
      x F 3 2 0 (by decide) (t * ((a⁻¹ : Fˣ) : F)) := by
  obtain ⟨_, hr⟩ := stage_actions_of_image 2 (h a) (h_mem_stage a) (hMatrix a)
    (toStableGeneralLinear_h a)
  have hv : Pi.single (0 : Fin 2) t ᵥ* ((hMatrix a)⁻¹).val =
      Pi.single (0 : Fin 2) (t * ((a⁻¹ : Fˣ) : F)) := by
    rw [hMatrix_inv_val]
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  have hh := hr (Pi.single (0 : Fin 2) t)
  rw [rowWord_single, hv, rowWord_single] at hh
  exact hh

private lemma h_conj_w02 (a b : Fˣ) : h a * w02 b * (h a)⁻¹ = w02 (a * b) := by
  calc
    _ = (h a * x F 3 0 2 (by decide) (b : F) * (h a)⁻¹) *
        (h a * x F 3 2 0 (by decide) (-((b⁻¹ : Fˣ) : F)) * (h a)⁻¹) *
          (h a * x F 3 0 2 (by decide) (b : F) * (h a)⁻¹) := by rw [w02]; simp [mul_assoc]
    _ = _ := by
      rw [h_conj_upper02, h_conj_lower02]
      simp only [w02, Units.val_mul, mul_inv_rev, neg_mul]

private lemma w02_neg (a : Fˣ) : w02 (-a) = (w02 a)⁻¹ := by
  simp [w02, x_neg, mul_inv_rev, mul_assoc]

private lemma h_conj_h02 (a b : Fˣ) :
    h a * h02 b * (h a)⁻¹ = h02 (a * b) * (h02 a)⁻¹ := by
  have he : a * (-1 : Fˣ) = -a := by apply Units.ext; simp
  calc
    _ = (h a * w02 b * (h a)⁻¹) *
        (h a * w02 (-1 : Fˣ) * (h a)⁻¹) := by rw [h02]; simp [mul_assoc]
    _ = w02 (a * b) * w02 (-a) := by rw [h_conj_w02, h_conj_w02, he]
    _ = _ := by rw [w02_neg]; simp [h02, mul_inv_rev, mul_assoc]

/-- The rank-three torus commutator is the inverse of the reversed ordered defect. -/
lemma commutator_torus (a b : Fˣ) :
    ⁅h a, h02 b⁆ = (torusDefect b a)⁻¹ := by
  change (h a * h02 b * (h a)⁻¹) * (h02 b)⁻¹ = _
  rw [h_conj_h02, ← defect02_eq]
  simp only [defect02, mul_inv_rev, inv_inv, show b * a = a * b from mul_comm b a]
  simp only [mul_assoc]

private lemma torusDefect_inv_commute (a b : Fˣ) (g : Group F) :
    Commute (torusDefect a b)⁻¹ g :=
  (torusDefect_commute a b g).inv_right.symm

private lemma commutator_central_mul_left (z a b : Group F)
    (hz : ∀ g, Commute z g) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, (hz b).commutator_eq, mul_one,
    (hz ⁅a, b⁆).eq, mul_inv_cancel_right]

private lemma commutator_central_mul_right (z a b : Group F)
    (hz : ∀ g, Commute z g) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, (hz a).symm.commutator_eq, one_mul,
    (hz ⁅a, b⁆).eq, mul_inv_cancel_right]

private lemma h_product_lift (a b : Fˣ) :
    h (a * b) = (torusDefect a b)⁻¹ * (h a * h b) := by
  simp [torusDefect, mul_inv_rev, mul_assoc]

private lemma h02_product_lift (a b : Fˣ) :
    h02 (a * b) = (torusDefect a b)⁻¹ * (h02 a * h02 b) := by
  rw [← defect02_eq]
  simp [defect02, mul_inv_rev, mul_assoc]

/-- The literal ordered defect is multiplicative in its second unit parameter. -/
lemma torusDefect_mul_right (a b c : Fˣ) :
    torusDefect a (b * c) = torusDefect a b * torusDefect a c := by
  apply inv_injective
  calc
    _ = ⁅h (b * c), h02 a⁆ := (commutator_torus (b * c) a).symm
    _ = ⁅h b * h c, h02 a⁆ := by
      rw [h_product_lift]
      exact commutator_central_mul_left _ _ _ (torusDefect_inv_commute b c)
    _ = h b * ⁅h c, h02 a⁆ * (h b)⁻¹ * ⁅h b, h02 a⁆ :=
      commutatorElement_mul_left_eq_conj_mul (h b) (h c) (h02 a)
    _ = (torusDefect a c)⁻¹ * (torusDefect a b)⁻¹ := by
      rw [commutator_torus, commutator_torus,
        (torusDefect_commute a c (h b)).inv_right.eq, mul_inv_cancel_right]
    _ = _ := (mul_inv_rev (torusDefect a b) (torusDefect a c)).symm

/-- The literal ordered defect is multiplicative in its first unit parameter. -/
lemma torusDefect_mul_left (a b c : Fˣ) :
    torusDefect (a * b) c = torusDefect a c * torusDefect b c := by
  apply inv_injective
  calc
    _ = ⁅h c, h02 (a * b)⁆ := (commutator_torus c (a * b)).symm
    _ = ⁅h c, h02 (b * a)⁆ := by rw [mul_comm a b]
    _ = ⁅h c, h02 b * h02 a⁆ := by
      rw [h02_product_lift]
      exact commutator_central_mul_right _ _ _ (torusDefect_inv_commute b a)
    _ = ⁅h c, h02 b⁆ * h02 b * ⁅h c, h02 a⁆ * (h02 b)⁻¹ :=
      commutatorElement_mul_right_eq_mul_conj (h c) (h02 b) (h02 a)
    _ = (torusDefect b c)⁻¹ *
        (h02 b * (torusDefect a c)⁻¹ * (h02 b)⁻¹) := by
      rw [commutator_torus, commutator_torus]
      simp only [mul_assoc]
    _ = (torusDefect b c)⁻¹ * (torusDefect a c)⁻¹ := by
      rw [(torusDefect_commute a c (h02 b)).inv_right.eq, mul_inv_cancel_right]
    _ = _ := (mul_inv_rev (torusDefect a c) (torusDefect b c)).symm

/-- A canonical commutative structure copying every original kernel group operation. -/
@[instance_reducible]
def kernelCommGroup (K : Type u) [Field K] :
    CommGroup ((toElementary K).ker) := {
  (inferInstance : _root_.Group ((toElementary K).ker)) with
  mul_comm a b := by
    apply Subtype.ext
    have hc : (b : Group K) ∈ Subgroup.center (Group K) :=
      ker_toElementary_le_center K b.property
    exact Subgroup.mem_center_iff.mp hc (a : Group K)
}

attribute [local instance] kernelCommGroup

end StableSteinberg
