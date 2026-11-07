/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matsumoto.Torus
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Weyl

Adapted from Quillen Matsumoto/Weyl.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native Stacks
homogeneous Milnor group throughout.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## RootCoordinateWeylAlgebra -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The correction for conjugation by W_i(1), namely Matsumoto's theta_i inverse. -/
def reflectionCorrection (l x r : Fˣ) : MilnorKTheory F 2 :=
  -pair F r (-1) - pair F l x + pair F l r - pair F x r

lemma reflectionCorrection_cocycle (l x r L X R : Fˣ) :
    pair F x (L * X⁻¹ * R * X⁻¹) - pair F r (L * X⁻¹ * R * X⁻¹) +
      pair F (l * x⁻¹ * r * x⁻¹) X - pair F (l * x⁻¹ * r * x⁻¹) L +
        pair F (l * x⁻¹ * r * x⁻¹) (L * X⁻¹ * R * X⁻¹) =
          reflectionCorrection F (l * L) (x * X) (r * R) -
            reflectionCorrection F l x r - reflectionCorrection F L X R := by
  simp only [reflectionCorrection, pair_mul_left, pair_mul_right, pair_inv_left,
    pair_inv_right]
  rw [pair_skew F L x, pair_skew F L r, pair_skew F X r]
  abel

lemma pair_sign_neg (a : Fˣ) : -pair F a (-1) = pair F a (-1) := by
  exact neg_eq_iff_add_eq_zero.mpr (pair_sign_two F a)

lemma reflectionCorrection_square (l x r : Fˣ) :
    reflectionCorrection F l x r + reflectionCorrection F l (l * x⁻¹ * r) r =
      pair F l (-1) + pair F r (-1) := by
  simp only [reflectionCorrection, pair_mul_left, pair_mul_right, pair_inv_left,
    pair_inv_right, pair_self]
  calc
    _ = -pair F l (-1) - pair F r (-1) -
      (pair F r (-1) + pair F r (-1)) := by abel
    _ = _ := by rw [pair_sign_two, sub_zero, sub_eq_add_neg, pair_sign_neg, pair_sign_neg]

@[simp] lemma reflectionCorrection_one : reflectionCorrection F 1 1 1 = 0 := by
  simp [reflectionCorrection]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateWeyl -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
open scoped commutatorElement
variable (F : Type u) [Field F]

/-- The multiplicative change in the reflected simple-coroot coordinate. -/
def reflectionDelta {n : ℕ} (i : Fin n) (s : Fin n → Fˣ) : Fˣ :=
  previous F s i * (s i)⁻¹ * following F s i * (s i)⁻¹

/-- The literal simple reflection on simple-coroot coordinates. -/
def reflectionCoordinates {n : ℕ} (i : Fin n) (s : Fin n → Fˣ) : Fin n → Fˣ :=
  s * Pi.mulSingle i (reflectionDelta F i s)

@[simp] lemma reflectionCoordinates_self {n : ℕ} (i : Fin n) (s : Fin n → Fˣ) :
    reflectionCoordinates F i s i = previous F s i * (s i)⁻¹ * following F s i := by
  simp [reflectionCoordinates, reflectionDelta, mul_comm, mul_left_comm]

lemma reflectionCoordinates_other {n : ℕ} (i j : Fin n) (s : Fin n → Fˣ) (hji : j ≠ i) :
    reflectionCoordinates F i s j = s j := by
  simp [reflectionCoordinates, hji]

@[simp] lemma previous_reflection {n : ℕ} (i : Fin n) (s : Fin n → Fˣ) :
    previous F (reflectionCoordinates F i s) i = previous F s i := by
  simp [reflectionCoordinates]

@[simp] lemma following_reflection {n : ℕ} (i : Fin n) (s : Fin n → Fˣ) :
    following F (reflectionCoordinates F i s) i = following F s i := by
  simp [reflectionCoordinates]

lemma reflectionCoordinates_mul {n : ℕ} (i : Fin n) (s t : Fin n → Fˣ) :
    reflectionCoordinates F i (s * t) =
      reflectionCoordinates F i s * reflectionCoordinates F i t := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [mul_comm, mul_left_comm, mul_assoc]
  · simp [reflectionCoordinates_other, hji]

@[simp] lemma reflectionCoordinates_one {n : ℕ} (i : Fin n) :
    reflectionCoordinates F i 1 = 1 := by
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [reflectionCoordinates_other, hji]

@[simp] lemma reflectionCoordinates_involutive {n : ℕ} (i : Fin n) (s : Fin n → Fˣ) :
    reflectionCoordinates F i (reflectionCoordinates F i s) = s := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [mul_comm, mul_left_comm]
  · simp [reflectionCoordinates_other, hji]

lemma cocycle_reflection {n : ℕ} (i : Fin n) (s t : Fin n → Fˣ) :
    cocycle F n (reflectionCoordinates F i s) (reflectionCoordinates F i t) =
      cocycle F n s t +
        reflectionCorrection F (previous F (s * t) i) ((s * t) i)
          (following F (s * t) i) -
        reflectionCorrection F (previous F s i) (s i) (following F s i) -
        reflectionCorrection F (previous F t i) (t i) (following F t i) := by
  unfold reflectionCoordinates
  rw [cocycle_mul_left, cocycle_mul_right, cocycle_mul_right,
    cocycle_single_right, cocycle_single_left, cocycle_single_single]
  have he := reflectionCorrection_cocycle F (previous F s i) (s i) (following F s i)
    (previous F t i) (t i) (following F t i)
  simp only [previous_mul, following_mul, Pi.mul_apply]
  unfold reflectionDelta
  convert congrArg (fun z => cocycle F n s t + z) he using 1 <;> abel

/-- The actual signed Weyl homomorphism, with its central correction retained. -/
def reflectionHom {n : ℕ} (i : Fin n) : Torus F n →* Torus F n where
  toFun x := ⟨reflectionCoordinates F i x.diagonal,
    x.central + reflectionCorrection F (previous F x.diagonal i) (x.diagonal i)
      (following F x.diagonal i)⟩
  map_one' := by
    apply Torus.ext
    · exact reflectionCoordinates_one F i
    · change 0 + reflectionCorrection F (previous F 1 i) ((1 : Fin n → Fˣ) i)
        (following F 1 i) = 0
      simp
  map_mul' x y := by
    apply Torus.ext
    · exact reflectionCoordinates_mul F i x.diagonal y.diagonal
    · change (x.central + y.central + cocycle F n x.diagonal y.diagonal) +
          reflectionCorrection F (previous F (x.diagonal * y.diagonal) i)
            ((x.diagonal * y.diagonal) i) (following F (x.diagonal * y.diagonal) i) =
        (x.central + reflectionCorrection F (previous F x.diagonal i) (x.diagonal i)
          (following F x.diagonal i)) +
        (y.central + reflectionCorrection F (previous F y.diagonal i) (y.diagonal i)
          (following F y.diagonal i)) +
        cocycle F n (reflectionCoordinates F i x.diagonal)
          (reflectionCoordinates F i y.diagonal)
      rw [cocycle_reflection]
      abel

/-- Matsumoto's theta_i inverse, corresponding to the signed matrix W_i(1). -/
def reflection {n : ℕ} (i : Fin n) : MulAut (Torus F n) where
  __ := reflectionHom F i
  invFun x := ⟨reflectionCoordinates F i x.diagonal,
    x.central - reflectionCorrection F (previous F x.diagonal i)
      (reflectionCoordinates F i x.diagonal i) (following F x.diagonal i)⟩
  left_inv x := by
    apply Torus.ext
    · exact reflectionCoordinates_involutive F i x.diagonal
    · change x.central + reflectionCorrection F (previous F x.diagonal i)
          (x.diagonal i) (following F x.diagonal i) -
        reflectionCorrection F (previous F (reflectionCoordinates F i x.diagonal) i)
          (reflectionCoordinates F i (reflectionCoordinates F i x.diagonal) i)
          (following F (reflectionCoordinates F i x.diagonal) i) = x.central
      simp only [previous_reflection, reflectionCoordinates_involutive,
        following_reflection, add_sub_cancel_right]
  right_inv x := by
    apply Torus.ext
    · exact reflectionCoordinates_involutive F i x.diagonal
    · change x.central - reflectionCorrection F (previous F x.diagonal i)
          (reflectionCoordinates F i x.diagonal i) (following F x.diagonal i) +
        reflectionCorrection F (previous F (reflectionCoordinates F i x.diagonal) i)
          (reflectionCoordinates F i x.diagonal i)
          (following F (reflectionCoordinates F i x.diagonal) i) = x.central
      simp

@[simp] lemma reflection_coefficient {n : ℕ} (i : Fin n)
    (a : Multiplicative (MilnorKTheory F 2)) : reflection F i (coefficient F n a) =
      coefficient F n a := by
  apply Torus.ext
  · exact reflectionCoordinates_one F i
  · change a.toAdd + reflectionCorrection F (previous F 1 i) ((1 : Fin n → Fˣ) i)
      (following F 1 i) = a.toAdd
    simp

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateGenerators -/

section

noncomputable section
universe u v
namespace StableSteinberg.RootCoordinate
open scoped commutatorElement
variable (F : Type u) [Field F]

/-- The simple-coroot section with zero central coordinate. -/
def simple {n : ℕ} (i : Fin n) (a : Fˣ) : Torus F n := torusLift F n (Pi.mulSingle i a)

@[simp] lemma simple_one {n : ℕ} (i : Fin n) : simple F i 1 = 1 := by
  apply Torus.ext
  · change (Pi.mulSingle i (1 : Fˣ) : Fin n → Fˣ) = 1
    simp
  · rfl

lemma simple_mul {n : ℕ} (i : Fin n) (a b : Fˣ) :
    simple F i a * simple F i b =
      coefficient F n (Multiplicative.ofAdd (pair F a b)) * simple F i (a * b) := by
  rw [simple, simple, torusLift_mul, cocycle_single_single]
  congr 2
  ext j
  by_cases hji : j = i <;> simp [hji]

lemma simple_defect {n : ℕ} (i : Fin n) (a b : Fˣ) :
    simple F i a * simple F i b * (simple F i (a * b))⁻¹ =
      coefficient F n (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])) := by
  rw [simple_mul, mul_inv_cancel_right]
  rfl

lemma simple_neg_one_square {n : ℕ} (i : Fin n) :
    simple F i (-1) * simple F i (-1) =
      coefficient F n (Multiplicative.ofAdd (milnorKTupleSymbol ![-1, -1])) := by
  rw [simple_mul]
  simp [pair]

lemma previous_single {n : ℕ} (i j : Fin n) (a : Fˣ) :
    previous F (Pi.mulSingle j a) i = if i.val = j.val + 1 then a else 1 := by
  unfold previous
  split_ifs with h hij
  · have he : (⟨i.val - 1, by omega⟩ : Fin n) = j := by
      apply Fin.ext
      simp only
      omega
    simp [he]
  · have hne : (⟨i.val - 1, by omega⟩ : Fin n) ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      simp only at hv
      omega
    simp [hne]
  · omega
  · rfl

lemma following_single {n : ℕ} (i j : Fin n) (a : Fˣ) :
    following F (Pi.mulSingle j a) i = if j.val = i.val + 1 then a else 1 := by
  unfold following
  split_ifs with h hij
  · have he : (⟨i.val + 1, h⟩ : Fin n) = j := Fin.ext hij.symm
    simp [he]
  · have hne : (⟨i.val + 1, h⟩ : Fin n) ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      simp only at hv
      omega
    simp [hne]
  · omega
  · rfl

/-- The coefficient subgroup and the actual simple-coroot sections generate the torus. -/
theorem generated {n : ℕ} (S : Subgroup (Torus F n))
    (hc : ∀ a, coefficient F n a ∈ S) (hh : ∀ i a, simple F i a ∈ S) : S = ⊤ := by
  apply top_unique
  intro x _
  have hproj : ∀ s : Fin n → Fˣ, s ∈ S.map (projection F n) := by
    intro s
    rw [← Finset.univ_prod_mulSingle s]
    apply Subgroup.prod_mem
    intro i _
    exact ⟨simple F i (s i), hh i (s i), rfl⟩
  obtain ⟨y, hy, hxy⟩ := hproj x.diagonal
  have hk : y⁻¹ * x ∈ (projection F n).ker := by
    change projection F n (y⁻¹ * x) = 1
    rw [map_mul, map_inv, hxy]
    change x.diagonal⁻¹ * x.diagonal = 1
    exact inv_mul_cancel _
  rw [projection_ker] at hk
  obtain ⟨a, ha⟩ := hk
  have hx : x = y * coefficient F n a := by rw [ha, mul_inv_cancel_left]
  rw [hx]
  exact S.mul_mem hy (hc a)

/-- Homomorphisms out of the concrete torus are fixed by coefficients and simple coroots. -/
theorem hom_ext {n : ℕ} {G : Type v} [_root_.Group G] (f g : Torus F n →* G)
    (hc : ∀ a, f (coefficient F n a) = g (coefficient F n a))
    (hh : ∀ i a, f (simple F i a) = g (simple F i a)) : f = g := by
  have he := generated F (f.eqLocus g) hc hh
  ext x
  have hx : x ∈ f.eqLocus g := by rw [he]; trivial
  exact hx

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateWeylSquare -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
open scoped commutatorElement
variable (F : Type u) [Field F]

lemma conjugate_formula {n : ℕ} (x y : Torus F n) :
    x * y * x⁻¹ = coefficient F n (Multiplicative.ofAdd
      (cocycle F n x.diagonal y.diagonal - cocycle F n y.diagonal x.diagonal)) * y := by
  have he : x * y = coefficient F n (Multiplicative.ofAdd
      (cocycle F n x.diagonal y.diagonal - cocycle F n y.diagonal x.diagonal)) * (y * x) := by
    apply Torus.ext
    · change x.diagonal * y.diagonal = 1 * (y.diagonal * x.diagonal)
      simp [mul_comm]
    · change x.central + y.central + cocycle F n x.diagonal y.diagonal =
        (cocycle F n x.diagonal y.diagonal - cocycle F n y.diagonal x.diagonal) +
          (y.central + x.central + cocycle F n y.diagonal x.diagonal) +
          cocycle F n 1 (y.diagonal * x.diagonal)
      rw [cocycle_one_left]
      abel
  rw [he]
  simp [mul_assoc]

lemma conjugate_neg_one {n : ℕ} (i : Fin n) (x : Torus F n) :
    simple F i (-1) * x * (simple F i (-1))⁻¹ =
      coefficient F n (Multiplicative.ofAdd
        (pair F (previous F x.diagonal i) (-1) +
          pair F (following F x.diagonal i) (-1))) * x := by
  rw [conjugate_formula]
  change coefficient F n (Multiplicative.ofAdd
      (cocycle F n (Pi.mulSingle i (-1)) x.diagonal -
        cocycle F n x.diagonal (Pi.mulSingle i (-1)))) * x = _
  rw [cocycle_single_left, cocycle_single_right,
    pair_skew F (-1) (x.diagonal i), pair_skew F (-1) (previous F x.diagonal i)]
  apply congrArg (fun z : MilnorKTheory F 2 =>
    coefficient F n (Multiplicative.ofAdd z) * x)
  rw [pair_sign_neg F (x.diagonal i)]
  abel

/-- The signed automorphism has the actual inner square, without killing the sign symbol. -/
theorem reflection_square {n : ℕ} (i : Fin n) (x : Torus F n) :
    reflection F i (reflection F i x) = simple F i (-1) * x * (simple F i (-1))⁻¹ := by
  rw [conjugate_neg_one]
  apply Torus.ext
  · change reflectionCoordinates F i (reflectionCoordinates F i x.diagonal) = 1 * x.diagonal
    simp
  · change (x.central + reflectionCorrection F (previous F x.diagonal i)
          (x.diagonal i) (following F x.diagonal i)) +
        reflectionCorrection F (previous F (reflectionCoordinates F i x.diagonal) i)
          (reflectionCoordinates F i x.diagonal i)
          (following F (reflectionCoordinates F i x.diagonal) i) =
      (pair F (previous F x.diagonal i) (-1) + pair F (following F x.diagonal i) (-1)) +
        x.central + cocycle F n 1 x.diagonal
    rw [previous_reflection, following_reflection, reflectionCoordinates_self,
      cocycle_one_left, add_zero, add_assoc, reflectionCorrection_square]
    exact add_comm _ _

/-- The nonsimple 02 lift with the central shift dictated by the signed Weyl action. -/
def signedH02 (a : Fˣ) : Torus F 2 :=
  coefficient F 2 (Multiplicative.ofAdd (-pair F a (-1))) * torusLift F 2 (coroot02 F a)

lemma commutator_formula {n : ℕ} (x y : Torus F n) :
    ⁅x, y⁆ = coefficient F n (Multiplicative.ofAdd
      (cocycle F n x.diagonal y.diagonal - cocycle F n y.diagonal x.diagonal)) := by
  rw [commutatorElement_def, conjugate_formula]
  simp [mul_assoc]

lemma signedH02_commutator (a b : Fˣ) :
    ⁅simple F (0 : Fin 2) a, signedH02 F b⁆ =
      coefficient F 2 (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])) := by
  rw [commutator_formula]
  have he : (Pi.mulSingle (0 : Fin 2) a : Fin 2 → Fˣ) = coroot01 F a := by
    ext i
    fin_cases i <;> simp [coroot01]
  change coefficient F 2 (Multiplicative.ofAdd
    (cocycle F 2 (Pi.mulSingle 0 a) (1 * coroot02 F b) -
      cocycle F 2 (1 * coroot02 F b) (Pi.mulSingle 0 a))) = _
  rw [one_mul, he, cocycle_01_02, cocycle_02_01, sub_zero]
  rfl

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateLocalActions -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma previous_adjacent {n : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val)
    (s : Fin n → Fˣ) : previous F s j = s i := by
  unfold previous
  split_ifs with h
  · congr 1
    apply Fin.ext
    simp only
    omega
  · omega

lemma following_adjacent {n : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val)
    (s : Fin n → Fˣ) : following F s i = s j := by
  unfold following
  split_ifs with h
  · congr 1
    exact Fin.ext hij
  · omega

lemma previous_reflection_other {n : ℕ} (i j : Fin n) (hij : i.val + 1 ≠ j.val)
    (s : Fin n → Fˣ) : previous F (reflectionCoordinates F i s) j = previous F s j := by
  unfold previous
  split_ifs with h
  · apply reflectionCoordinates_other
    intro he
    have hv := congrArg Fin.val he
    simp only at hv
    omega
  · rfl

lemma following_reflection_other {n : ℕ} (i j : Fin n) (hij : j.val + 1 ≠ i.val)
    (s : Fin n → Fˣ) : following F (reflectionCoordinates F i s) j = following F s j := by
  unfold following
  split_ifs with h
  · apply reflectionCoordinates_other
    intro he
    have hv := congrArg Fin.val he
    simp only at hv
    omega
  · rfl

lemma reflectionCoordinates_commute {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) (s : Fin n → Fˣ) :
    reflectionCoordinates F i (reflectionCoordinates F j s) =
      reflectionCoordinates F j (reflectionCoordinates F i s) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [reflectionCoordinates_other, hne, previous_reflection_other F j i hji,
      following_reflection_other F j i hij]
  · by_cases hkj : k = j
    · subst k
      simp [reflectionCoordinates_other, hne.symm, previous_reflection_other F i j hij,
        following_reflection_other F i j hji]
    · simp [reflectionCoordinates_other, hki, hkj]

lemma reflectionCoordinates_braid {n : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val)
    (s : Fin n → Fˣ) :
    reflectionCoordinates F i (reflectionCoordinates F j (reflectionCoordinates F i s)) =
      reflectionCoordinates F j (reflectionCoordinates F i (reflectionCoordinates F j s)) := by
  have hne : i ≠ j := by intro he; have := congrArg Fin.val he; omega
  have hji : j.val + 1 ≠ i.val := by omega
  ext k
  by_cases hki : k = i
  · subst k
    simp [reflectionCoordinates_other, hne, hne.symm, previous_adjacent F i j hij,
      following_adjacent F i j hij, previous_reflection_other F j i hji,
      following_reflection_other F i j hji, mul_comm, mul_left_comm, mul_assoc]
  · by_cases hkj : k = j
    · subst k
      simp [reflectionCoordinates_other, hne, hne.symm, previous_adjacent F i j hij,
        following_adjacent F i j hij, previous_reflection_other F j i hji,
        following_reflection_other F i j hji, mul_comm, mul_left_comm, mul_assoc]
    · simp [reflectionCoordinates_other, hki, hkj]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateCoherenceAlgebra -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma reflectionCorrection_braid (l x y r : Fˣ) :
    reflectionCorrection F l x y + reflectionCorrection F (l * x⁻¹ * y) y r +
      reflectionCorrection F l (l * x⁻¹ * y) (l * x⁻¹ * r) =
    reflectionCorrection F x y r + reflectionCorrection F l x (x * y⁻¹ * r) +
      reflectionCorrection F (l * y⁻¹ * r) (x * y⁻¹ * r) r := by
  simp only [reflectionCorrection, pair_mul_left, pair_mul_right,
    pair_inv_left, pair_inv_right, pair_self]
  simp only [pair_skew F x l, pair_skew F y l,
    pair_skew F y x, pair_skew F r x, pair_skew F r y]
  have htwo (a : Fˣ) : (-2 : ℤ) • pair F a (-1) = 0 := by
    rw [neg_smul, two_zsmul, pair_sign_two, neg_zero]
  have hfour (a : Fˣ) : (-4 : ℤ) • pair F a (-1) = 0 := by
    rw [show (-4 : ℤ) = -2 + -2 from rfl, add_smul, htwo, add_zero]
  abel_nf
  simp only [htwo, hfour, zero_add, add_zero]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateWeylRelations -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- Distant signed Weyl automorphisms commute on the whole concrete torus. -/
theorem reflection_commute {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) (x : Torus F n) :
    reflection F i (reflection F j x) = reflection F j (reflection F i x) := by
  apply Torus.ext
  · exact reflectionCoordinates_commute F i j hne hij hji x.diagonal
  · change (x.central + reflectionCorrection F (previous F x.diagonal j)
          (x.diagonal j) (following F x.diagonal j)) +
        reflectionCorrection F (previous F (reflectionCoordinates F j x.diagonal) i)
          (reflectionCoordinates F j x.diagonal i)
          (following F (reflectionCoordinates F j x.diagonal) i) =
      (x.central + reflectionCorrection F (previous F x.diagonal i)
          (x.diagonal i) (following F x.diagonal i)) +
        reflectionCorrection F (previous F (reflectionCoordinates F i x.diagonal) j)
          (reflectionCoordinates F i x.diagonal j)
          (following F (reflectionCoordinates F i x.diagonal) j)
    rw [previous_reflection_other F j i hji, following_reflection_other F j i hij,
      previous_reflection_other F i j hij, following_reflection_other F i j hji,
      reflectionCoordinates_other F j i x.diagonal hne,
      reflectionCoordinates_other F i j x.diagonal hne.symm]
    abel

/-- The adjacent type-A braid relation holds with the central sign terms retained. -/
theorem reflection_braid {n : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val)
    (x : Torus F n) :
    reflection F i (reflection F j (reflection F i x)) =
      reflection F j (reflection F i (reflection F j x)) := by
  have hne : i ≠ j := by intro he; have := congrArg Fin.val he; omega
  have hji : j.val + 1 ≠ i.val := by omega
  apply Torus.ext
  · exact reflectionCoordinates_braid F i j hij x.diagonal
  · change ((x.central + reflectionCorrection F (previous F x.diagonal i)
            (x.diagonal i) (following F x.diagonal i)) +
          reflectionCorrection F (previous F (reflectionCoordinates F i x.diagonal) j)
            (reflectionCoordinates F i x.diagonal j)
            (following F (reflectionCoordinates F i x.diagonal) j)) +
        reflectionCorrection F
          (previous F (reflectionCoordinates F j (reflectionCoordinates F i x.diagonal)) i)
          (reflectionCoordinates F j (reflectionCoordinates F i x.diagonal) i)
          (following F (reflectionCoordinates F j (reflectionCoordinates F i x.diagonal)) i) =
      ((x.central + reflectionCorrection F (previous F x.diagonal j)
            (x.diagonal j) (following F x.diagonal j)) +
          reflectionCorrection F (previous F (reflectionCoordinates F j x.diagonal) i)
            (reflectionCoordinates F j x.diagonal i)
            (following F (reflectionCoordinates F j x.diagonal) i)) +
        reflectionCorrection F
          (previous F (reflectionCoordinates F i (reflectionCoordinates F j x.diagonal)) j)
          (reflectionCoordinates F i (reflectionCoordinates F j x.diagonal) j)
          (following F (reflectionCoordinates F i (reflectionCoordinates F j x.diagonal)) j)
    simp only [previous_adjacent F i j hij, following_adjacent F i j hij,
      previous_reflection_other F j i hji, following_reflection_other F i j hji,
      reflectionCoordinates_self, previous_reflection, following_reflection,
      reflectionCoordinates_other F i j _ hne.symm, reflectionCoordinates_other F j i _ hne]
    have hnorm : previous F x.diagonal i * (x.diagonal i)⁻¹ *
        (x.diagonal i * (x.diagonal j)⁻¹ * following F x.diagonal j) =
          previous F x.diagonal i * (x.diagonal j)⁻¹ * following F x.diagonal j := by
      group
    rw [mul_inv_cancel_right, hnorm]
    convert congrArg (fun z => x.central + z)
      (reflectionCorrection_braid F (previous F x.diagonal i) (x.diagonal i)
        (x.diagonal j) (following F x.diagonal j)) using 1 <;>
      abel

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateWeylGenerators -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma reflection_simple_self {n : ℕ} (i : Fin n) (a : Fˣ) :
    reflection F i (simple F i a) = simple F i a⁻¹ := by
  apply Torus.ext
  · funext k
    by_cases hki : k = i
    · subst k
      change reflectionCoordinates F i (Pi.mulSingle i a) i = (Pi.mulSingle i a⁻¹ : Fin n → Fˣ) i
      simp
    · change reflectionCoordinates F i (Pi.mulSingle i a) k = (Pi.mulSingle i a⁻¹ : Fin n → Fˣ) k
      simp [reflectionCoordinates_other, hki]
  · change 0 + reflectionCorrection F (previous F (Pi.mulSingle i a) i)
      ((Pi.mulSingle i a : Fin n → Fˣ) i) (following F (Pi.mulSingle i a) i) = 0
    simp [reflectionCorrection]

@[simp] lemma reflection_simple_neg_one {n : ℕ} (i : Fin n) :
    reflection F i (simple F i (-1)) = simple F i (-1) := by
  rw [reflection_simple_self]
  simp

lemma reflection_simple_distant {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) (a : Fˣ) :
    reflection F i (simple F j a) = simple F j a := by
  have hp : previous F (Pi.mulSingle j a) i = 1 := by
    rw [previous_single]
    simp [Ne.symm hji]
  have hq : following F (Pi.mulSingle j a) i = 1 := by
    rw [following_single]
    simp [Ne.symm hij]
  apply Torus.ext
  · change reflectionCoordinates F i (Pi.mulSingle j a) = Pi.mulSingle j a
    simp [reflectionCoordinates, reflectionDelta, hp, hq, hne]
  · change 0 + reflectionCorrection F (previous F (Pi.mulSingle j a) i)
      ((Pi.mulSingle j a : Fin n → Fˣ) i) (following F (Pi.mulSingle j a) i) = 0
    simp [reflectionCorrection, hp, hq, hne]

/-- On either neighboring coroot, theta_i inverse appends H_i(a) on the right. -/
lemma reflection_simple_adjacent {n : ℕ} (i j : Fin n)
    (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) (a : Fˣ) :
    reflection F i (simple F j a) = simple F j a * simple F i a := by
  have hne : i ≠ j := by intro he; have := congrArg Fin.val he; omega
  have hp := previous_single F i j a
  have hq := following_single F i j a
  apply Torus.ext
  · change reflectionCoordinates F i (Pi.mulSingle j a) = Pi.mulSingle j a * Pi.mulSingle i a
    unfold reflectionCoordinates reflectionDelta
    rw [hp, hq]
    rcases hij with hij | hij
    · have hji : i.val ≠ j.val + 1 := by omega
      simp [hij, hji, hne]
    · have hji : j.val ≠ i.val + 1 := by omega
      simp [hij, hji, hne]
  · change 0 + reflectionCorrection F (previous F (Pi.mulSingle j a) i)
        ((Pi.mulSingle j a : Fin n → Fˣ) i) (following F (Pi.mulSingle j a) i) =
      0 + 0 + cocycle F n (Pi.mulSingle j a) (Pi.mulSingle i a)
    rw [cocycle_single_right, hp, hq]
    rcases hij with hij | hij
    · have hji : i.val ≠ j.val + 1 := by omega
      simp [reflectionCorrection, hij, hji, hne, pair_self]
    · have hji : j.val ≠ i.val + 1 := by omega
      simp [reflectionCorrection, hij, hji, hne]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateMatrices -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- A simple coroot as a literal diagonal tuple of size n+1. -/
def simpleDiagonal {n : ℕ} (i : Fin n) (a : Fˣ) : Fin (n + 1) → Fˣ :=
  Pi.mulSingle i.castSucc a * Pi.mulSingle i.succ a⁻¹

lemma simpleDiagonal_mul {n : ℕ} (i : Fin n) (a b : Fˣ) :
    simpleDiagonal F i (a * b) = simpleDiagonal F i a * simpleDiagonal F i b := by
  have hne : i.castSucc ≠ i.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  funext k
  by_cases hk : k = i.castSucc <;> by_cases hl : k = i.succ <;>
    simp [simpleDiagonal, hk, hl, hne, hne.symm, mul_comm]

@[simp] lemma simpleDiagonal_one {n : ℕ} (i : Fin n) : simpleDiagonal F i 1 = 1 := by
  simp [simpleDiagonal]

/-- The product of the literal simple-coroot diagonal matrices. -/
def diagonalCoordinates {n : ℕ} (s : Fin n → Fˣ) : Fin (n + 1) → Fˣ :=
  ∏ i, simpleDiagonal F i (s i)

lemma diagonalCoordinates_mul {n : ℕ} (s t : Fin n → Fˣ) :
    diagonalCoordinates F (s * t) = diagonalCoordinates F s * diagonalCoordinates F t := by
  simp [diagonalCoordinates, simpleDiagonal_mul, Finset.prod_mul_distrib]

@[simp] lemma diagonalCoordinates_one (n : ℕ) :
    diagonalCoordinates F (1 : Fin n → Fˣ) = 1 := by
  simp [diagonalCoordinates]

@[simp] lemma diagonalCoordinates_single {n : ℕ} (i : Fin n) (a : Fˣ) :
    diagonalCoordinates F (Pi.mulSingle i a) = simpleDiagonal F i a := by
  unfold diagonalCoordinates
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- The actual diagonal matrix homomorphism. -/
def torusMatrix (n : ℕ) : Torus F n →* Matrix (Fin (n + 1)) (Fin (n + 1)) F where
  toFun x := Matrix.diagonal (fun i => (diagonalCoordinates F x.diagonal i : F))
  map_one' := by
    change Matrix.diagonal (fun i => (diagonalCoordinates F (1 : Fin n → Fˣ) i : F)) = 1
    simp
  map_mul' x y := by
    change Matrix.diagonal (fun i =>
      (diagonalCoordinates F (x.diagonal * y.diagonal) i : F)) = _
    rw [diagonalCoordinates_mul, Matrix.diagonal_mul_diagonal]
    rfl

/-- The same actual diagonal matrices as units. -/
def torusToGL (n : ℕ) : Torus F n →* Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  (torusMatrix F n).toHomUnits

lemma simpleDiagonal_prod {n : ℕ} (i : Fin n) (a : Fˣ) :
    ∏ k, simpleDiagonal F i a k = 1 := by
  simp [simpleDiagonal, Finset.prod_mul_distrib]

lemma diagonalCoordinates_prod {n : ℕ} (s : Fin n → Fˣ) :
    ∏ k, diagonalCoordinates F s k = 1 := by
  simp only [diagonalCoordinates, Finset.prod_apply]
  rw [Finset.prod_comm]
  simp [simpleDiagonal_prod]

/-- Every projected matrix has determinant one, in every finite rank. -/
theorem torusToGL_det (n : ℕ) (x : Torus F n) :
    Matrix.det ((torusToGL F n x).val) = 1 := by
  change Matrix.det (Matrix.diagonal (fun i => (diagonalCoordinates F x.diagonal i : F))) = 1
  rw [Matrix.det_diagonal]
  simpa only [Units.coe_prod, Units.val_one] using
    congrArg (fun u : Fˣ => (u : F)) (diagonalCoordinates_prod F x.diagonal)

lemma torusMatrix_simple {n : ℕ} (i : Fin n) (a : Fˣ) :
    torusMatrix F n (torusLift F n (Pi.mulSingle i a)) =
      Matrix.diagonal (fun k => (simpleDiagonal F i a k : F)) := by
  change Matrix.diagonal (fun k =>
    (diagonalCoordinates F (Pi.mulSingle i a) k : F)) = _
  rw [diagonalCoordinates_single]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateNormalization -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
open scoped commutatorElement
variable (F : Type u) [Field F]

lemma signedH02_eq_reverse_product (a : Fˣ) :
    signedH02 F a = simple F (1 : Fin 2) a * simple F (0 : Fin 2) a := by
  apply Torus.ext
  · change (1 : Fin 2 → Fˣ) * coroot02 F a =
      Pi.mulSingle (1 : Fin 2) a * Pi.mulSingle (0 : Fin 2) a
    funext i
    fin_cases i <;> simp [coroot02]
  · change -pair F a (-1) + 0 + cocycle F 2 1 (coroot02 F a) =
      0 + 0 + cocycle F 2 (Pi.mulSingle 1 a) (Pi.mulSingle 0 a)
    rw [cocycle_one_left, cocycle_single_right, following_single]
    simp [pair_self]

/-- The shifted 02 section is the signed-Weyl conjugate of the neighboring simple section. -/
theorem reflection_one_H12 (a : Fˣ) :
    reflection F (0 : Fin 2) (simple F (1 : Fin 2) a) = signedH02 F a := by
  rw [reflection_simple_adjacent F 0 1 (Or.inl (by decide)), signedH02_eq_reverse_product]

lemma signedH02_mul (a b : Fˣ) :
    signedH02 F a * signedH02 F b =
      coefficient F 2 (Multiplicative.ofAdd (pair F a b)) * signedH02 F (a * b) := by
  rw [← reflection_one_H12, ← reflection_one_H12, ← map_mul, simple_mul, map_mul,
    reflection_coefficient, reflection_one_H12]

/-- The signed nonsimple section retains the same positive ordered defect. -/
theorem signedH02_defect (a b : Fˣ) :
    signedH02 F a * signedH02 F b * (signedH02 F (a * b))⁻¹ =
      coefficient F 2 (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])) := by
  rw [signedH02_mul, mul_inv_cancel_right]
  rfl

lemma signedH02_matrix (a : Fˣ) :
    torusMatrix F 2 (signedH02 F a) = Matrix.diagonal ![(a : F), 1, (a⁻¹ : Fˣ)] := by
  change Matrix.diagonal (fun i =>
    (diagonalCoordinates F (1 * coroot02 F a) i : F)) = _
  rw [one_mul]
  congr 1
  funext i
  fin_cases i <;>
    simp [diagonalCoordinates, simpleDiagonal, coroot02, Fin.prod_univ_succ]

lemma simple01_matrix (a : Fˣ) :
    torusMatrix F 2 (simple F (0 : Fin 2) a) =
      Matrix.diagonal ![(a : F), (a⁻¹ : Fˣ), 1] := by
  rw [simple, torusMatrix_simple]
  congr 1
  funext i
  fin_cases i <;> simp [simpleDiagonal]

end StableSteinberg.RootCoordinate

end

end
