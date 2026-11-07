/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.Bruhat.Decomposition
public import Colib.LinearAlgebra.Matrix.Bruhat.Coordinates
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# RootUpdate

Finite matrix Bruhat rootupdate over fields, using the native general linear
group, with the original rank hypotheses and signed matrix formulas.

## Implementation provenance

Adapted from `Quillen/Aglib/LinearAlgebra/Matrix/Bruhat/RootUpdate.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native elementary matrix units and
finite matrix stabilization are used directly.
-/

@[expose] public section

/-! ## BruhatRootTransport -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- Conjugation of a literal elementary matrix by a literal finite monomial matrix. -/
lemma monomial_conjugate_elementary {n : ℕ} (m : MonomialGroup F n)
    (i j : Fin n) (hij : i ≠ j) (a : F) :
    monomialToGL F n m * Matrix.GeneralLinearGroup.elementary i j hij a * (monomialToGL F n m)⁻¹ =
      Matrix.GeneralLinearGroup.elementary (m.right i) (m.right j) (m.right.injective.ne hij)
        ((m.left (m.right i) : F) * a * ((m.left (m.right j))⁻¹ : Fˣ)) := by
  apply Units.ext
  ext r s
  rw [monomial_conjugate_val]
  simp only [Matrix.GeneralLinearGroup.elementary_val,
    Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply, Equiv.eq_symm_apply, Equiv.apply_symm_apply]
  by_cases hrs : r = s
  · subst s
    have hn : ¬(m.right i = r ∧ m.right j = r) := by
      rintro ⟨hi, hj⟩
      exact hij (m.right.injective (hi.trans hj.symm))
    simp only [↓reduceIte, hn, add_zero, mul_one]
    exact Units.mul_inv (m.left r)
  · by_cases hir : m.right i = r <;> by_cases hjs : m.right j = s
    · subst r
      subst s
      simp [hrs]
    all_goals simp [hrs, hir, hjs]

/-- Moving a root through an actual monomial produces an actual upper root when the
inverse permutation puts its two indices in increasing order. -/
lemma elementary_mul_monomial_upper {n : ℕ} (m : MonomialGroup F n)
    (i j : Fin n) (hij : i ≠ j) (a : F)
    (horder : m.right.symm i < m.right.symm j) :
    ∃ V : upperUnipotent F n,
      Matrix.GeneralLinearGroup.elementary i j hij a * monomialToGL F n m = monomialToGL F n m * V
        := by
  let b : F := ((m⁻¹).left ((m⁻¹).right i) : F) * a *
    (((m⁻¹).left ((m⁻¹).right j))⁻¹ : Fˣ)
  let V : upperUnipotent F n :=
    ⟨Matrix.GeneralLinearGroup.elementary ((m⁻¹).right i) ((m⁻¹).right j)
      ((m⁻¹).right.injective.ne hij) b, elementary_mem_upper F _ _ horder b⟩
  refine ⟨V, ?_⟩
  have he := monomial_conjugate_elementary F m⁻¹ i j hij a
  rw [map_inv, inv_inv] at he
  have hh := congrArg (fun z : Matrix.GeneralLinearGroup (Fin n) F => monomialToGL F n m * z)
    he
  simpa only [V, b, mul_assoc, mul_inv_cancel_left] using hh

end Matrix.Bruhat

end

end

/-! ## BruhatGauss -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

lemma elementary_mul_val {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) F)
    (i j : Fin n) (hij : i ≠ j) (a : F) (r s : Fin n) :
    (Matrix.GeneralLinearGroup.elementary i j hij a * g).val r s =
      g.val r s + if r = i then a * g.val j s else 0 := by
  change ((1 + Matrix.single i j a) * g.val) r s = _
  rw [add_mul, one_mul, Matrix.add_apply]
  by_cases hr : r = i
  · subst r
    simp
  · rw [Matrix.single_mul_apply_of_ne a i j r s hr, ite_eq_right hr, add_zero]

lemma mul_elementary_val {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) F)
    (i j : Fin n) (hij : i ≠ j) (a : F) (r s : Fin n) :
    (g * Matrix.GeneralLinearGroup.elementary i j hij a).val r s =
      g.val r s + if s = j then g.val r i * a else 0 := by
  change (g.val * (1 + Matrix.single i j a)) r s = _
  rw [mul_add, mul_one, Matrix.add_apply]
  by_cases hs : s = j
  · subst s
    simp
  · rw [Matrix.mul_single_apply_of_ne a i j r s hs, ite_eq_right hs, add_zero]

/-- Literal signed swap coordinates for a finite elementary Weyl matrix. -/
def rootWMonomial {n : ℕ} (i j : Fin n) (a : Fˣ) : MonomialGroup F n :=
  ⟨Pi.mulSingle i a * Pi.mulSingle j (-a⁻¹), Equiv.swap i j⟩

/-- Literal two-coordinate diagonal data for a finite coroot matrix. -/
def rootHMonomial {n : ℕ} (i j : Fin n) (a : Fˣ) : MonomialGroup F n :=
  ⟨Pi.mulSingle i a * Pi.mulSingle j a⁻¹, 1⟩

lemma diagonalGL_val {n : ℕ} (d : Fin n → Fˣ) (r s : Fin n) :
    (diagonalGL F n d).val r s = if r = s then (d r : F) else 0 := rfl

/-- The literal finite-rank Gauss crossing used in the decreasing-permutation Bruhat case. -/
lemma rootWMonomial_gauss {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    monomialToGL F n (rootWMonomial F i j 1) *
        Matrix.GeneralLinearGroup.elementary i j hij (-(a : F)) =
      Matrix.GeneralLinearGroup.elementary i j hij ((a⁻¹ : Fˣ) : F) *
        (monomialToGL F n (rootHMonomial F i j a))⁻¹ *
          Matrix.GeneralLinearGroup.elementary j i hij.symm (-((a⁻¹ : Fˣ) : F)) := by
  have hi : (monomialToGL F n (rootHMonomial F i j a))⁻¹ =
      diagonalGL F n ((Pi.mulSingle i a : Fin n → Fˣ) * Pi.mulSingle j a⁻¹)⁻¹ := by
    change (diagonalGL F n ((Pi.mulSingle i a : Fin n → Fˣ) * Pi.mulSingle j a⁻¹))⁻¹ = _
    exact (map_inv _ _).symm
  apply Units.ext
  ext r s
  rw [hi, mul_elementary_val, mul_elementary_val, elementary_mul_val, elementary_mul_val]
  simp only [diagonalGL_val]
  change (if r = Equiv.swap i j s then
      ((Pi.mulSingle i 1 * Pi.mulSingle j (-1) : Fin n → Fˣ) r : F) else 0) +
      (if s = j then (if r = Equiv.swap i j i then
        ((Pi.mulSingle i 1 * Pi.mulSingle j (-1) : Fin n → Fˣ) r : F) else 0) * -(a : F)
      else 0) = _
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsi : s = i <;> by_cases hsj : s = j <;>
      simp_all [Equiv.swap_apply_def, Pi.mulSingle_apply, eq_comm]

end Matrix.Bruhat

end

end

/-! ## BruhatLeftUpdate -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- The actual two-case update for left multiplication by a simple Weyl matrix. -/
theorem bruhatMonomial_left_simple (n : ℕ) (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    bruhatMonomial F (n + 1)
        (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) * g) =
      rootWMonomial F i.castSucc i.succ 1 * bruhatMonomial F (n + 1) g ∨
    ∃ a : Fˣ, bruhatMonomial F (n + 1)
        (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) * g) =
      (rootHMonomial F i.castSucc i.succ a)⁻¹ * bruhatMonomial F (n + 1) g := by
  let m := bruhatMonomial F (n + 1) g
  let w := rootWMonomial F i.castSucc i.succ (1 : Fˣ)
  let G := monomialToGL F (n + 1) w
  let M := monomialToGL F (n + 1) m
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  obtain ⟨U, V, hg⟩ := bruhatMonomial_factorization F (n + 1) g
  change g = (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * M * V at hg
  let t := (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ
  obtain ⟨U₀, hzero, hU⟩ := split_simple_upper F n i U
  change U = U₀ * simpleUpper F n i t at hU
  let U₁ : upperUnipotent F (n + 1) :=
    ⟨G * U₀ * G⁻¹, upper_simple_reflection_conjugate F n i w.left U₀ hzero⟩
  have hbase : G * g = (U₁ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * G *
      Matrix.GeneralLinearGroup.elementary i.castSucc i.succ hij t * M * V := by
    change G * g = (G * U₀ * G⁻¹) * G *
      Matrix.GeneralLinearGroup.elementary i.castSucc i.succ hij t * M * V
    rw [hg, hU]
    simp [simpleUpper, mul_assoc]
  have hfirst (R : upperUnipotent F (n + 1))
      (hR : Matrix.GeneralLinearGroup.elementary i.castSucc i.succ hij t * M = M * R) :
      bruhatMonomial F (n + 1) (G * g) = w * m := by
    apply bruhatMonomial_eq_of_factorization F (n + 1) _ (w * m) U₁ (R * V)
    rw [map_mul, hbase]
    change (U₁ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * G *
        Matrix.GeneralLinearGroup.elementary i.castSucc i.succ hij t * M * V = U₁ * (G * M) * (R *
          V)
    have he : Matrix.GeneralLinearGroup.elementary i.castSucc i.succ hij t * (M * V) = M * (R * V)
      := by
      rw [← mul_assoc, hR, mul_assoc]
    simp only [mul_assoc]
    rw [he]
  by_cases ht : t = 0
  · left
    apply hfirst 1
    rw [ht, Matrix.GeneralLinearGroup.elementary_zero, one_mul]
    exact (mul_one M).symm
  by_cases hord : m.right.symm i.castSucc < m.right.symm i.succ
  · left
    obtain ⟨R, hR⟩ := elementary_mul_monomial_upper F m i.castSucc i.succ hij t hord
    exact hfirst R hR
  · right
    have hne := m.right.symm.injective.ne hij
    have hrev : m.right.symm i.succ < m.right.symm i.castSucc :=
      lt_of_le_of_ne (le_of_not_gt hord) (Ne.symm hne)
    let a : Fˣ := Units.mk0 (-t) (neg_ne_zero.mpr ht)
    have ha : -(a : F) = t := by simp [a]
    let X := Matrix.GeneralLinearGroup.elementary i.castSucc i.succ hij ((a⁻¹ : Fˣ) : F)
    let Y := Matrix.GeneralLinearGroup.elementary i.succ i.castSucc hij.symm (-((a⁻¹ : Fˣ) : F))
    let H₀ := monomialToGL F (n + 1) (rootHMonomial F i.castSucc i.succ a)
    have hgauss : G * Matrix.GeneralLinearGroup.elementary i.castSucc i.succ hij t = X * H₀⁻¹ * Y :=
      by
      simpa only [ha] using rootWMonomial_gauss F i.castSucc i.succ hij a
    obtain ⟨R, hR⟩ := elementary_mul_monomial_upper F m i.succ i.castSucc hij.symm
      (-((a⁻¹ : Fˣ) : F)) hrev
    change Y * M = M * R at hR
    let U₂ := U₁ * simpleUpper F n i ((a⁻¹ : Fˣ) : F)
    refine ⟨a, ?_⟩
    apply bruhatMonomial_eq_of_factorization F (n + 1) _
      ((rootHMonomial F i.castSucc i.succ a)⁻¹ * m) U₂ (R * V)
    rw [map_mul, map_inv, hbase]
    change (U₁ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * G *
        Matrix.GeneralLinearGroup.elementary i.castSucc i.succ hij t * M * V =
      (U₁ * X) * (H₀⁻¹ * M) * (R * V)
    have he : Y * (M * V) = M * (R * V) := by rw [← mul_assoc, hR, mul_assoc]
    calc
      _ = (U₁ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) *
          (G * Matrix.GeneralLinearGroup.elementary i.castSucc i.succ hij t) * (M * V) := by simp
            [mul_assoc]
      _ = U₁ * (X * H₀⁻¹ * Y) * (M * V) := by rw [hgauss]
      _ = _ := by simp only [mul_assoc]; rw [he]

end Matrix.Bruhat

end

end

/-! ## BruhatRightUpdate -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- Inversion reverses the actual two upper-unipotent factors. -/
lemma bruhatMonomial_inv (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) F) :
    bruhatMonomial F n g⁻¹ = (bruhatMonomial F n g)⁻¹ := by
  obtain ⟨U, V, hg⟩ := bruhatMonomial_factorization F n g
  apply bruhatMonomial_eq_of_factorization F n _ _ V⁻¹ U⁻¹
  nth_rw 1 [hg]
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, map_inv]
  simp [mul_assoc]

lemma rootWMonomial_neg_one {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    rootWMonomial F i j (-1) = (rootWMonomial F i j 1)⁻¹ := by
  have he : rootWMonomial F i j 1 * rootWMonomial F i j (-1) = 1 := by
    apply SemidirectProduct.ext
    · change (Pi.mulSingle i 1 * Pi.mulSingle j (-(1 : Fˣ)⁻¹) : Fin n → Fˣ) *
        permDiagonal F (Equiv.swap i j)
          (Pi.mulSingle i (-1) * Pi.mulSingle j (-(-1 : Fˣ)⁻¹)) = 1
      funext k
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp_all [permDiagonal, Pi.mulSingle_apply, Equiv.swap_apply_def, eq_comm]
    · exact Equiv.swap_mul_self i j
  have hh := congrArg (fun z => (rootWMonomial F i j 1)⁻¹ * z) he
  simpa [mul_assoc] using hh

end Matrix.Bruhat

end

end
