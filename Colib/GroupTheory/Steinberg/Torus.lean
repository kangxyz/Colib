/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Map
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Literal rank-two torus words in the stable Steinberg presentation

For `a : Fˣ`, the actual presented group contains the ordered words
`w(a) = x01(a) x10(-a⁻¹) x01(a)` and `h(a) = w(a) w(-1)`.
Their canonical images are represented at the original finite rank two by
`!![0, a; -a⁻¹, 0]` and `diagonal ![a, a⁻¹]`, respectively.

The finite diagonal representatives multiply as expected. Consequently the
ordered source word `h(a) h(b) h(ab)⁻¹` belongs to the kernel of the original
`toElementary`. It is retained as a literal kernel word, with its induced
field-change naturality. The short word identities `w(-a) = w(a)⁻¹` and `h(1) = 1`
also prove normalization when either defect parameter is one.

Only the finite matrix representatives are proved multiplicative. No symbol
bilinearity, Steinberg-symbol relation, kernel centrality, universal central
extension, or Milnor/Quillen K2 identification is asserted. There is no
characteristic or cardinality restriction on the field.

## Implementation provenance

Adapted from `Quillen/Algebra/Group/StableSteinbergTorus.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the ordered word and its sign.
-/
@[expose] public section

noncomputable section

universe u v

namespace StableSteinberg

variable {F : Type u} [Field F] {L : Type v} [Field L]

/-- Negation of a root coefficient is inversion of the actual presented generator. -/
lemma x_neg (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    x F n i j hij (-a) = (x F n i j hij a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [x_add, add_neg_cancel, x_zero]

/-- The literal ordered Weyl word on the original two root indices. -/
def w (a : Fˣ) : Group F :=
  x F 2 0 1 (by decide) (a : F) *
    x F 2 1 0 (by decide) (-((a⁻¹ : Fˣ) : F)) * x F 2 0 1 (by decide) (a : F)

/-- The literal normalization `w(a) w(-1)` in the actual presented group. -/
def h (a : Fˣ) : Group F := w a * w (-1 : Fˣ)

/-- The original rank-two elementary-matrix product representing the Weyl word. -/
def wMatrix (a : Fˣ) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.elementary (0 : Fin 2) 1 (by decide) (a : F) *
    Matrix.GeneralLinearGroup.elementary (1 : Fin 2) 0 (by decide) (-((a⁻¹ : Fˣ) : F)) *
      Matrix.GeneralLinearGroup.elementary (0 : Fin 2) 1 (by decide) (a : F)

/-- The finite representative has the stated ordered off-diagonal matrix values. -/
lemma wMatrix_val (a : Fˣ) :
    (wMatrix a).val = !![0, (a : F); -((a⁻¹ : Fˣ) : F), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMatrix, Units.val_mul, Matrix.GeneralLinearGroup.elementary_val,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Matrix.one_apply]

/-- The original stable matrix map retains the actual rank-two Weyl representative. -/
lemma toStableGeneralLinear_w (a : Fˣ) :
    toStableGeneralLinear F (w a) = StableGeneralLinear.of F 2 (wMatrix a) := by
  simp only [w, wMatrix, map_mul, toStableGeneralLinear_x]

/-- The original rank-two product representing the normalized torus word. -/
def hMatrix (a : Fˣ) : Matrix.GeneralLinearGroup (Fin 2) F := wMatrix a * wMatrix (-1 : Fˣ)

/-- The actual finite torus representative is the diagonal matrix `(a, a⁻¹)`. -/
lemma hMatrix_val (a : Fˣ) :
    (hMatrix a).val = Matrix.diagonal ![(a : F), ((a⁻¹ : Fˣ) : F)] := by
  rw [hMatrix, Units.val_mul, wMatrix_val, wMatrix_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The original stable matrix map retains the actual rank-two torus representative. -/
lemma toStableGeneralLinear_h (a : Fˣ) :
    toStableGeneralLinear F (h a) = StableGeneralLinear.of F 2 (hMatrix a) := by
  simp only [h, hMatrix, map_mul, toStableGeneralLinear_w]

/-- Multiplicativity holds for the finite diagonal matrix representatives. -/
lemma hMatrix_mul (a b : Fˣ) : hMatrix a * hMatrix b = hMatrix (a * b) := by
  apply Units.ext
  simp only [Units.val_mul, hMatrix_val, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_inv_rev, mul_comm]

/-- Negating the unit parameter inverts the literal Weyl word. -/
lemma w_neg (a : Fˣ) : w (-a) = (w a)⁻¹ := by
  simp [w, x_neg, mul_inv_rev, mul_assoc]

/-- The chosen literal torus normalization sends the unit parameter one to the identity. -/
lemma h_one : h (1 : Fˣ) = 1 := by
  rw [h, w_neg, mul_inv_cancel]

/-- The ordered source defect `h(a) h(b) h(ab)⁻¹`, without any symbol-law assertion. -/
def torusDefect (a b : Fˣ) : Group F := h a * h b * (h (a * b))⁻¹

/-- The literal defect is normalized when its second parameter is one. -/
lemma torusDefect_one_right (a : Fˣ) : torusDefect a 1 = 1 := by
  simp [torusDefect, h_one]

/-- The literal defect is normalized when its first parameter is one. -/
lemma torusDefect_one_left (b : Fˣ) : torusDefect 1 b = 1 := by
  simp [torusDefect, h_one]

/-- The ordered torus defect has trivial original stable matrix image. -/
lemma toStableGeneralLinear_torusDefect (a b : Fˣ) :
    toStableGeneralLinear F (torusDefect a b) = 1 := by
  simp only [torusDefect, map_mul, map_inv, toStableGeneralLinear_h]
  rw [← map_mul, hMatrix_mul, mul_inv_cancel]

/-- The ordered torus defect has trivial image in the actual elementary subgroup. -/
lemma toElementary_torusDefect (a b : Fˣ) : toElementary F (torusDefect a b) = 1 := by
  apply Subtype.ext
  exact toStableGeneralLinear_torusDefect a b

/-- The literal defect as an element of the kernel of the original `toElementary`. -/
def torusDefectKernel (a b : Fˣ) : (toElementary F).ker :=
  ⟨torusDefect a b, toElementary_torusDefect a b⟩

/-- The kernel element retains the same literal source word. -/
@[simp] lemma torusDefectKernel_coe (a b : Fˣ) :
    (torusDefectKernel a b : Group F) = torusDefect a b := rfl

/-- The actual field-change map acts on the literal Weyl word through its unit coefficient. -/
lemma map_w (f : F →+* L) (a : Fˣ) :
    map f (w a) = w (Units.map f.toMonoidHom a) := by
  simp [w, map_x, map_mul]

/-- The actual field-change map retains the chosen torus-word normalization. -/
lemma map_h (f : F →+* L) (a : Fˣ) :
    map f (h a) = h (Units.map f.toMonoidHom a) := by
  simp only [h, map_mul, map_w]
  congr 1
  apply congrArg w
  apply Units.ext
  simp

/-- The actual field-change map retains the ordered torus defect word. -/
lemma map_torusDefect (f : F →+* L) (a b : Fˣ) :
    map f (torusDefect a b) =
      torusDefect (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) := by
  simp [torusDefect, map_mul, map_inv, map_h]

/-- Field change on the actual kernels, induced by the original elementary naturality square. -/
def toElementaryKernelMap (f : F →+* L) :
    (toElementary F).ker →* (toElementary L).ker where
  toFun a := ⟨map f a, by
    have hn := DFunLike.congr_fun (toElementary_naturality f) (a : Group F)
    change toElementary L (map f a) = 1
    change toElementary L (map f a) = elementaryMap f (toElementary F a) at hn
    rw [a.property, map_one] at hn
    exact hn⟩
  map_one' := Subtype.ext (map_one (map f))
  map_mul' a b := Subtype.ext (map_mul (map f) (a : Group F) (b : Group F))

/-- The kernel field map retains the original presented-group field map. -/
@[simp] lemma toElementaryKernelMap_coe (f : F →+* L) (a : (toElementary F).ker) :
    (toElementaryKernelMap f a : Group L) = map f a := rfl

/-- The literal kernel-valued torus defects are natural under actual field change. -/
lemma toElementaryKernelMap_torusDefectKernel (f : F →+* L) (a b : Fˣ) :
    toElementaryKernelMap f (torusDefectKernel a b) =
      torusDefectKernel (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) := by
  apply Subtype.ext
  exact map_torusDefect f a b

end StableSteinberg
