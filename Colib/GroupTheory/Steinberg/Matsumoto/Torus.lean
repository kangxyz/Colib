/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.Relations
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Torus

The explicit type-A cocycle constructs a central extension of the simple-coroot
torus by the native Stacks homogeneous Milnor group. Its marked defect and
commutator are the literal ordered tuple symbol with positive sign.

Adapted from Quillen Matsumoto/Torus.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; no secondary Milnor model is used.
This is a prerequisite for the Matsumoto extension, not an injectivity theorem.
-/

@[expose] public section

/-! ## RootCoordinateTorus -/

section

/-!
# The determinant-one torus in simple-coroot coordinates

The coefficient group and ordered symbols are the native Stacks Milnor K₂.
The cocycle is explicit; no normalizer or Matsumoto law is an input.
-/

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
open scoped Matrix commutatorElement
variable (F : Type u) [Field F]

/-- The original ordered pair in the existing all-degree Milnor group. -/
def pair (a b : Fˣ) : MilnorKTheory F 2 := milnorKTupleSymbol ![a, b]

private lemma pair_val (a b : Fˣ) :
    (pair F a b : MilnorKRing F) = milnorKSymbol F a * milnorKSymbol F b := by
  simp [pair, milnorKTupleSymbol, List.ofFn_succ, milnorKSymbolProd_cons]

lemma pair_mul_left (a b c : Fˣ) : pair F (a * b) c = pair F a c + pair F b c := by
  apply Subtype.ext
  simp [pair_val, milnorKSymbol_mul, add_mul]

lemma pair_mul_right (a b c : Fˣ) : pair F a (b * c) = pair F a b + pair F a c := by
  apply Subtype.ext
  simp [pair_val, milnorKSymbol_mul, mul_add]

@[simp] lemma pair_one_left (b : Fˣ) : pair F 1 b = 0 := by
  apply Subtype.ext
  simp [pair_val]

@[simp] lemma pair_one_right (a : Fˣ) : pair F a 1 = 0 := by
  apply Subtype.ext
  simp [pair_val]

@[simp] lemma pair_inv_left (a b : Fˣ) : pair F a⁻¹ b = -pair F a b := by
  apply Subtype.ext
  simp [pair_val, milnorKSymbol_inv]

@[simp] lemma pair_inv_right (a b : Fˣ) : pair F a b⁻¹ = -pair F a b := by
  apply Subtype.ext
  simp [pair_val, milnorKSymbol_inv]

lemma pair_skew (a b : Fˣ) : pair F a b = -pair F b a := by
  apply Subtype.ext
  change (pair F a b : MilnorKRing F) = -(pair F b a : MilnorKRing F)
  simpa only [pair_val] using
    eq_neg_of_add_eq_zero_left (milnorKSymbol_mul_add_mul_comm (k := F) a b)

lemma pair_self_neg (a : Fˣ) : pair F a (-a) = 0 := by
  apply Subtype.ext
  change (pair F a (-a) : MilnorKRing F) = 0
  simpa only [pair_val] using milnorKSymbol_mul_neg_self (k := F) a

lemma pair_self (a : Fˣ) : pair F a a = pair F a (-1) := by
  have h := pair_self_neg F a
  rw [show -a = (-1 : Fˣ) * a by simp, pair_mul_right] at h
  have hs : pair F a (-1) + pair F a (-1) = 0 := by
    rw [← pair_mul_right]; simp
  exact add_left_cancel (h.trans hs.symm)

lemma pair_steinberg (a b : Fˣ) (hab : (a : F) + (b : F) = 1) : pair F a b = 0 := by
  exact milnorKTupleSymbol_steinberg ![a, b] 0 1 rfl hab

lemma pair_sign_two (a : Fˣ) : pair F a (-1) + pair F a (-1) = 0 := by
  rw [← pair_mul_right]
  simp

private lemma ite_add_zero_split (p : Prop) [Decidable p] (a b : MilnorKTheory F 2) :
    (if p then a + b else 0) = (if p then a else 0) + (if p then b else 0) := by
  split_ifs <;> simp

/-- The type-A cocycle in ordered simple-coroot coordinates. -/
def cocycle (n : ℕ) (s t : Fin n → Fˣ) : MilnorKTheory F 2 :=
  (∑ i : Fin n, pair F (s i) (t i)) -
    ∑ i : Fin n, ∑ j : Fin n, if i.val = j.val + 1 then pair F (s i) (t j) else 0

lemma cocycle_mul_left (n : ℕ) (d e f : Fin n → Fˣ) :
    cocycle F n (d * e) f = cocycle F n d f + cocycle F n e f := by
  simp only [cocycle, Pi.mul_apply, pair_mul_left, ite_add_zero_split,
    Finset.sum_add_distrib]
  abel

lemma cocycle_mul_right (n : ℕ) (d e f : Fin n → Fˣ) :
    cocycle F n d (e * f) = cocycle F n d e + cocycle F n d f := by
  simp only [cocycle, Pi.mul_apply, pair_mul_right, ite_add_zero_split,
    Finset.sum_add_distrib]
  abel

@[simp] lemma cocycle_one_left (n : ℕ) (d : Fin n → Fˣ) : cocycle F n 1 d = 0 := by
  simp [cocycle]

@[simp] lemma cocycle_one_right (n : ℕ) (d : Fin n → Fˣ) : cocycle F n d 1 = 0 := by
  simp [cocycle]

lemma cocycle_identity (n : ℕ) (d e f : Fin n → Fˣ) :
    cocycle F n d e + cocycle F n (d * e) f =
      cocycle F n e f + cocycle F n d (e * f) := by
  rw [cocycle_mul_left, cocycle_mul_right]
  abel

/-- Concrete pairs of simple-coroot data and existing Milnor K2 coefficients. -/
structure Torus (n : ℕ) where
  /-- The actual simple-coroot parameters. -/
  diagonal : Fin n → Fˣ
  /-- The coefficient in the existing Milnor group. -/
  central : MilnorKTheory F 2

@[ext] lemma Torus.ext {n : ℕ} {x y : Torus F n}
    (hd : x.diagonal = y.diagonal) (hc : x.central = y.central) : x = y := by
  cases x
  cases y
  simp_all

instance (n : ℕ) : One (Torus F n) := ⟨⟨1, 0⟩⟩
instance (n : ℕ) : Mul (Torus F n) :=
  ⟨fun x y => ⟨x.diagonal * y.diagonal,
    x.central + y.central + cocycle F n x.diagonal y.diagonal⟩⟩
instance (n : ℕ) : Inv (Torus F n) :=
  ⟨fun x => ⟨x.diagonal⁻¹, -x.central - cocycle F n x.diagonal⁻¹ x.diagonal⟩⟩

instance (n : ℕ) : _root_.Group (Torus F n) where
  mul_assoc x y z := by
    apply Torus.ext
    · exact mul_assoc _ _ _
    · change (x.central + y.central + cocycle F n x.diagonal y.diagonal) + z.central +
        cocycle F n (x.diagonal * y.diagonal) z.diagonal =
          x.central + (y.central + z.central + cocycle F n y.diagonal z.diagonal) +
            cocycle F n x.diagonal (y.diagonal * z.diagonal)
      rw [cocycle_mul_left, cocycle_mul_right]
      abel
  one_mul x := by
    apply Torus.ext
    · exact one_mul _
    · change 0 + x.central + cocycle F n 1 x.diagonal = x.central
      simp
  mul_one x := by
    apply Torus.ext
    · exact mul_one _
    · change x.central + 0 + cocycle F n x.diagonal 1 = x.central
      simp
  inv_mul_cancel x := by
    apply Torus.ext
    · exact inv_mul_cancel _
    · change (-x.central - cocycle F n x.diagonal⁻¹ x.diagonal) + x.central +
        cocycle F n x.diagonal⁻¹ x.diagonal = 0
      abel

/-- Projection to the literal simple-coroot tuple. -/
def projection (n : ℕ) : Torus F n →* (Fin n → Fˣ) where
  toFun := Torus.diagonal
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Inject the existing Milnor group as the central coordinate. -/
def coefficient (n : ℕ) : Multiplicative (MilnorKTheory F 2) →* Torus F n where
  toFun z := ⟨1, z.toAdd⟩
  map_one' := rfl
  map_mul' a b := by
    apply Torus.ext
    · change 1 = 1 * (1 : Fin n → Fˣ)
      simp
    · change a.toAdd + b.toAdd = a.toAdd + b.toAdd + cocycle F n 1 1
      simp

lemma coefficient_injective (n : ℕ) : Function.Injective (coefficient F n) := by
  intro a b hab
  exact congrArg (fun z : Torus F n => Multiplicative.ofAdd z.central) hab

/-- The coordinate-zero section; its multiplicative defect is computed, not assumed. -/
def torusLift (n : ℕ) (d : Fin n → Fˣ) : Torus F n := ⟨d, 0⟩

lemma projection_surjective (n : ℕ) : Function.Surjective (projection F n) :=
  fun d => ⟨torusLift F n d, rfl⟩

lemma projection_ker (n : ℕ) : (projection F n).ker = (coefficient F n).range := by
  ext x
  constructor
  · intro hx
    refine ⟨Multiplicative.ofAdd x.central, ?_⟩
    apply Torus.ext
    · exact hx.symm
    · rfl
  · rintro ⟨z, rfl⟩
    rfl

lemma coefficient_le_center (n : ℕ) :
    (coefficient F n).range ≤ Subgroup.center (Torus F n) := by
  rintro _ ⟨a, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Torus.ext
  · change x.diagonal * 1 = 1 * x.diagonal
    simp
  · change x.central + a.toAdd + cocycle F n x.diagonal 1 =
      a.toAdd + x.central + cocycle F n 1 x.diagonal
    rw [cocycle_one_left, cocycle_one_right, add_zero, add_zero]
    exact add_comm _ _

lemma torusLift_mul (n : ℕ) (d e : Fin n → Fˣ) :
    torusLift F n d * torusLift F n e =
      coefficient F n (Multiplicative.ofAdd (cocycle F n d e)) *
        torusLift F n (d * e) := by
  apply Torus.ext
  · change d * e = 1 * (d * e)
    simp
  · change 0 + 0 + cocycle F n d e = cocycle F n d e + 0 + cocycle F n 1 (d * e)
    simp

lemma torusLift_defect (n : ℕ) (d e : Fin n → Fˣ) :
    torusLift F n d * torusLift F n e * (torusLift F n (d * e))⁻¹ =
      coefficient F n (Multiplicative.ofAdd (cocycle F n d e)) := by
  rw [torusLift_mul, mul_inv_cancel_right]

lemma torusLift_commutator (n : ℕ) (d e : Fin n → Fˣ) :
    ⁅torusLift F n d, torusLift F n e⁆ =
      coefficient F n (Multiplicative.ofAdd (cocycle F n d e - cocycle F n e d)) := by
  have he : torusLift F n d * torusLift F n e =
      coefficient F n (Multiplicative.ofAdd (cocycle F n d e - cocycle F n e d)) *
        (torusLift F n e * torusLift F n d) := by
    apply Torus.ext
    · change d * e = 1 * (e * d)
      simp [mul_comm]
    · change 0 + 0 + cocycle F n d e =
        (cocycle F n d e - cocycle F n e d) +
          (0 + 0 + cocycle F n e d) + cocycle F n 1 (e * d)
      simp
  rw [commutatorElement_def, he]
  simp [mul_assoc]

/-- The first simple coroot in rank two. -/
def coroot01 (a : Fˣ) : Fin 2 → Fˣ := ![a, 1]

/-- The 02 coroot is the product of the two consecutive simple coroots. -/
def coroot02 (a : Fˣ) : Fin 2 → Fˣ := ![a, a]

lemma coroot01_mul (a b : Fˣ) : coroot01 F (a * b) = coroot01 F a * coroot01 F b := by
  ext i
  fin_cases i <;> simp [coroot01]

lemma cocycle_01_01 (a b : Fˣ) :
    cocycle F 2 (coroot01 F a) (coroot01 F b) = pair F a b := by
  simp [cocycle, coroot01, Fin.sum_univ_succ]

lemma cocycle_01_02 (a b : Fˣ) :
    cocycle F 2 (coroot01 F a) (coroot02 F b) = pair F a b := by
  simp [cocycle, coroot01, coroot02, Fin.sum_univ_succ]

lemma cocycle_02_01 (a b : Fˣ) :
    cocycle F 2 (coroot02 F b) (coroot01 F a) = 0 := by
  simp [cocycle, coroot01, coroot02, Fin.sum_univ_succ]

/-- The ordered defect has the original positive symbol value. -/
theorem marked_defect (a b : Fˣ) :
    torusLift F 2 (coroot01 F a) * torusLift F 2 (coroot01 F b) *
      (torusLift F 2 (coroot01 F (a * b)))⁻¹ =
        coefficient F 2 (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])) := by
  rw [coroot01_mul, torusLift_defect, cocycle_01_01]
  rfl

/-- The 01,02 commutator has the same original positive symbol value. -/
theorem marked_commutator (a b : Fˣ) :
    ⁅torusLift F 2 (coroot01 F a), torusLift F 2 (coroot02 F b)⁆ =
      coefficient F 2 (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])) := by
  rw [torusLift_commutator, cocycle_01_02, cocycle_02_01, sub_zero]
  rfl

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateLocal -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The preceding simple-coroot coordinate, with boundary value one. -/
def previous {n : ℕ} (s : Fin n → Fˣ) (i : Fin n) : Fˣ :=
  if h : 0 < i.val then s ⟨i.val - 1, by omega⟩ else 1

/-- The following simple-coroot coordinate, with boundary value one. -/
def following {n : ℕ} (s : Fin n → Fˣ) (i : Fin n) : Fˣ :=
  if h : i.val + 1 < n then s ⟨i.val + 1, h⟩ else 1

@[simp] lemma previous_mul {n : ℕ} (s t : Fin n → Fˣ) (i : Fin n) :
    previous F (s * t) i = previous F s i * previous F t i := by
  unfold previous
  split_ifs <;> simp

@[simp] lemma following_mul {n : ℕ} (s t : Fin n → Fˣ) (i : Fin n) :
    following F (s * t) i = following F s i * following F t i := by
  unfold following
  split_ifs <;> simp

@[simp] lemma previous_one {n : ℕ} (i : Fin n) : previous F 1 i = 1 := by
  simp [previous]

@[simp] lemma following_one {n : ℕ} (i : Fin n) : following F 1 i = 1 := by
  simp [following]

lemma sum_previous {n : ℕ} (i : Fin n) (a : Fˣ) (t : Fin n → Fˣ) :
    (∑ j : Fin n, if i.val = j.val + 1 then pair F a (t j) else 0) =
      pair F a (previous F t i) := by
  unfold previous
  split_ifs with h
  · let j : Fin n := ⟨i.val - 1, by omega⟩
    rw [Finset.sum_eq_single j]
    · have hij : i.val = j.val + 1 := by dsimp [j]; omega
      exact ite_eq_left hij
    · intro k _ hkj
      have hik : i.val ≠ k.val + 1 := by
        intro he
        apply hkj
        apply Fin.ext
        dsimp [j]
        omega
      simp [hik]
    · simp
  · have hi : i.val = 0 := by omega
    simp [hi]

lemma sum_following {n : ℕ} (i : Fin n) (a : Fˣ) (s : Fin n → Fˣ) :
    (∑ j : Fin n, if j.val = i.val + 1 then pair F (s j) a else 0) =
      pair F (following F s i) a := by
  unfold following
  split_ifs with h
  · let j : Fin n := ⟨i.val + 1, h⟩
    rw [Finset.sum_eq_single j]
    · simp [j]
    · intro k _ hkj
      have hki : k.val ≠ i.val + 1 := by
        intro he
        exact hkj (Fin.ext he)
      simp [hki]
    · simp
  · have hji (j : Fin n) : j.val ≠ i.val + 1 := by omega
    simp [hji]

lemma cocycle_single_left {n : ℕ} (i : Fin n) (a : Fˣ) (t : Fin n → Fˣ) :
    cocycle F n (Pi.mulSingle i a) t = pair F a (t i) - pair F a (previous F t i) := by
  unfold cocycle
  congr 1
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  · rw [Finset.sum_eq_single i]
    · simpa using sum_previous F i a t
    · intro k _ hki
      apply Finset.sum_eq_zero
      intro j _
      simp [hki]
    · simp

lemma cocycle_single_right {n : ℕ} (i : Fin n) (a : Fˣ) (s : Fin n → Fˣ) :
    cocycle F n s (Pi.mulSingle i a) = pair F (s i) a - pair F (following F s i) a := by
  unfold cocycle
  congr 1
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  · have he (k : Fin n) :
        (∑ j : Fin n, if k.val = j.val + 1 then
          pair F (s k) ((Pi.mulSingle i a : Fin n → Fˣ) j) else 0) =
            if k.val = i.val + 1 then pair F (s k) a else 0 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · simp
    simp only [he]
    exact sum_following F i a s

@[simp] lemma previous_single_self {n : ℕ} (i : Fin n) (a : Fˣ) :
    previous F (Pi.mulSingle i a) i = 1 := by
  unfold previous
  split_ifs with h
  · have hne : (⟨i.val - 1, by omega⟩ : Fin n) ≠ i := by
      intro he
      have hv := congrArg Fin.val he
      simp only at hv
      omega
    simp [hne]
  · rfl

@[simp] lemma following_single_self {n : ℕ} (i : Fin n) (a : Fˣ) :
    following F (Pi.mulSingle i a) i = 1 := by
  unfold following
  split_ifs with h
  · have hne : (⟨i.val + 1, h⟩ : Fin n) ≠ i := by
      intro he
      have hv := congrArg Fin.val he
      simp only at hv
      omega
    simp [hne]
  · rfl

@[simp] lemma cocycle_single_single {n : ℕ} (i : Fin n) (a b : Fˣ) :
    cocycle F n (Pi.mulSingle i a) (Pi.mulSingle i b) = pair F a b := by
  simp [cocycle_single_left]

end StableSteinberg.RootCoordinate

end

end
