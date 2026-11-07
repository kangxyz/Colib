/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matsumoto.Weyl
public import Colib.GroupTheory.Steinberg.Matsumoto.Torus

/-!
# LiftedWeyl

Adapted from Quillen Matsumoto/LiftedWeyl.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native Stacks
homogeneous Milnor group throughout.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## RootCoordinateLiftedWeyl -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The simple adjacent transposition on the actual finite matrix indices. -/
def simpleSwap {n : ℕ} (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap i.castSucc i.succ

@[simp] lemma simpleSwap_mul_self {n : ℕ} (i : Fin n) :
    simpleSwap i * simpleSwap i = 1 := Equiv.swap_mul_self _ _

/-- The concrete lifted Weyl state set. -/
abbrev NormalizerState (n : ℕ) := Torus F n × Equiv.Perm (Fin (n + 1))

/-- Ascent for left multiplication, read from the two inverse permutation positions. -/
def isAscent {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin (n + 1))) : Prop :=
  σ.symm i.castSucc < σ.symm i.succ

/-- The right-hand correction in Matsumoto's descending branch. -/
def descentCarry {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin (n + 1))) : Torus F n := by
  classical
  exact if isAscent i σ then 1 else simple F i (-1)

/-- Matsumoto's theta_i, inverse to conjugation by W_i(1). -/
def theta {n : ℕ} (i : Fin n) : MulAut (Torus F n) := (reflection F i).symm

/-- The actual ascent/descent permutation, with the W_i(-1) convention. -/
def liftedWeyl {n : ℕ} (i : Fin n) : Equiv.Perm (NormalizerState F n) where
  toFun s := (theta F i (s.1 * descentCarry F i s.2), simpleSwap i * s.2)
  invFun s := (reflection F i s.1 * (descentCarry F i (simpleSwap i * s.2))⁻¹,
    simpleSwap i * s.2)
  left_inv s := by
    apply Prod.ext
    · change reflection F i (theta F i (s.1 * descentCarry F i s.2)) *
        (descentCarry F i (simpleSwap i * (simpleSwap i * s.2)))⁻¹ = s.1
      simp [theta, ← mul_assoc]
    · simp [← mul_assoc]
  right_inv s := by
    apply Prod.ext
    · change theta F i ((reflection F i s.1 *
        (descentCarry F i (simpleSwap i * s.2))⁻¹) *
          descentCarry F i (simpleSwap i * s.2)) = s.1
      simp [theta]
    · simp [← mul_assoc]

/-- Faithful left multiplication by the actual torus on the state set. -/
def torusLeft (n : ℕ) : Torus F n →* Equiv.Perm (NormalizerState F n) where
  toFun h :=
    { toFun := fun s => (h * s.1, s.2)
      invFun := fun s => (h⁻¹ * s.1, s.2)
      left_inv := by intro s; simp
      right_inv := by intro s; simp }
  map_one' := by ext s <;> simp
  map_mul' h k := by ext s <;> simp [mul_assoc]

lemma torusLeft_injective (n : ℕ) : Function.Injective (torusLeft F n) := by
  intro h k he
  have hv := congrArg (fun e : Equiv.Perm (NormalizerState F n) => (e (1, 1)).1) he
  simpa [torusLeft] using hv

lemma isAscent_toggle {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin (n + 1))) :
    isAscent i (simpleSwap i * σ) ↔ ¬isAscent i σ := by
  have hne : i.castSucc ≠ i.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hpositions := σ.symm.injective.ne hne
  have ha : (simpleSwap i * σ).symm i.castSucc = σ.symm i.succ := by
    apply (simpleSwap i * σ).injective
    simp [simpleSwap]
  have hb : (simpleSwap i * σ).symm i.succ = σ.symm i.castSucc := by
    apply (simpleSwap i * σ).injective
    simp [simpleSwap]
  unfold isAscent
  rw [ha, hb]
  constructor
  · exact not_lt_of_gt
  · intro h
    exact lt_of_le_of_ne (le_of_not_gt h) hpositions.symm

lemma theta_simple_self {n : ℕ} (i : Fin n) (a : Fˣ) :
    theta F i (simple F i a) = simple F i a⁻¹ := by
  apply (reflection F i).injective
  simp [theta, reflection_simple_self]

@[simp] lemma theta_simple_neg_one {n : ℕ} (i : Fin n) :
    theta F i (simple F i (-1)) = simple F i (-1) := by
  rw [theta_simple_self]
  simp

lemma theta_square {n : ℕ} (i : Fin n) (x : Torus F n) :
    theta F i (theta F i x) = simple F i (-1) * x * (simple F i (-1))⁻¹ := by
  rw [conjugate_neg_one]
  apply Torus.ext
  · change reflectionCoordinates F i (reflectionCoordinates F i x.diagonal) = 1 * x.diagonal
    simp
  · change (x.central - reflectionCorrection F (previous F x.diagonal i)
          (reflectionCoordinates F i x.diagonal i) (following F x.diagonal i)) -
        reflectionCorrection F (previous F (reflectionCoordinates F i x.diagonal) i)
          (reflectionCoordinates F i (reflectionCoordinates F i x.diagonal) i)
          (following F (reflectionCoordinates F i x.diagonal) i) =
      (pair F (previous F x.diagonal i) (-1) + pair F (following F x.diagonal i) (-1)) +
        x.central + cocycle F n 1 x.diagonal
    rw [previous_reflection, following_reflection, reflectionCoordinates_involutive,
      reflectionCoordinates_self, cocycle_one_left, add_zero]
    calc
      _ = x.central - (reflectionCorrection F (previous F x.diagonal i) (x.diagonal i)
          (following F x.diagonal i) + reflectionCorrection F (previous F x.diagonal i)
            (previous F x.diagonal i * (x.diagonal i)⁻¹ * following F x.diagonal i)
            (following F x.diagonal i)) := by abel
      _ = _ := by
        rw [reflectionCorrection_square, sub_eq_add_neg, neg_add,
          pair_sign_neg, pair_sign_neg]
        exact add_comm _ _

/-- The concrete Weyl lift squares to left multiplication by the actual H_i(-1). -/
theorem liftedWeyl_square {n : ℕ} (i : Fin n) (s : NormalizerState F n) :
    liftedWeyl F i (liftedWeyl F i s) = torusLeft F n (simple F i (-1)) s := by
  classical
  apply Prod.ext
  · change theta F i (theta F i (s.1 * descentCarry F i s.2) *
        descentCarry F i (simpleSwap i * s.2)) = simple F i (-1) * s.1
    by_cases h : isAscent i s.2
    · have hn : ¬isAscent i (simpleSwap i * s.2) := by
        rw [isAscent_toggle]
        exact not_not_intro h
      simp only [descentCarry, h, hn, ↓reduceIte, mul_one, map_mul,
        theta_square, theta_simple_neg_one]
      group
    · have hy : isAscent i (simpleSwap i * s.2) := (isAscent_toggle i s.2).mpr h
      simp only [descentCarry, h, hy, ↓reduceIte, mul_one, theta_square]
      group
  · change simpleSwap i * (simpleSwap i * s.2) = s.2
    simp [← mul_assoc]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateThetaRelations -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma theta_coefficient {n : ℕ} (i : Fin n) (a : Multiplicative (MilnorKTheory F 2)) :
    theta F i (coefficient F n a) = coefficient F n a := by
  apply (reflection F i).injective
  simp [theta]

lemma theta_simple_distant {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) (a : Fˣ) :
    theta F i (simple F j a) = simple F j a := by
  apply (reflection F i).injective
  simp [theta, reflection_simple_distant F i j hne hij hji]

lemma theta_adjacent_neg_one {n : ℕ} (i j : Fin n)
    (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    theta F i (simple F j (-1)) = simple F j (-1) * (simple F i (-1))⁻¹ := by
  apply (reflection F i).injective
  simp [theta, map_mul, map_inv, reflection_simple_adjacent F i j hij, mul_assoc]

lemma theta_commute {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) (x : Torus F n) :
    theta F i (theta F j x) = theta F j (theta F i x) := by
  have he : reflection F i * reflection F j = reflection F j * reflection F i := by
    apply DFunLike.ext
    intro y
    exact reflection_commute F i j hne hij hji y
  have hinv := congrArg (fun f : MulAut (Torus F n) => f⁻¹) he
  have hpoint := congrArg (fun f : MulAut (Torus F n) => f x) hinv.symm
  simpa [theta, _root_.mul_inv_rev] using hpoint

lemma theta_braid {n : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val) (x : Torus F n) :
    theta F i (theta F j (theta F i x)) = theta F j (theta F i (theta F j x)) := by
  have he : reflection F i * reflection F j * reflection F i =
      reflection F j * reflection F i * reflection F j := by
    apply DFunLike.ext
    intro y
    exact reflection_braid F i j hij y
  have hinv := congrArg (fun f : MulAut (Torus F n) => f⁻¹) he
  have hpoint := congrArg (fun f : MulAut (Torus F n) => f x) hinv
  simpa [theta, _root_.mul_inv_rev] using hpoint

lemma theta_descentCarry {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin (n + 1))) :
    theta F i (descentCarry F i σ) = descentCarry F i σ := by
  classical
  unfold descentCarry
  split_ifs <;> simp

lemma theta_descentCarry_distant {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val)
    (σ : Equiv.Perm (Fin (n + 1))) :
    theta F i (descentCarry F j σ) = descentCarry F j σ := by
  classical
  unfold descentCarry
  split_ifs <;> simp [theta_simple_distant F i j hne hij hji]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinatePermutationFacts -/

section

namespace StableSteinberg.RootCoordinate

lemma simpleSwap_fixed_of_distant {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) :
    simpleSwap j i.castSucc = i.castSucc ∧ simpleSwap j i.succ = i.succ := by
  have h00 : i.castSucc ≠ j.castSucc := by
    intro he
    have hv : i.val = j.val := congrArg (fun k : Fin (n + 1) => k.val) he
    exact hne (Fin.ext hv)
  have h01 : i.castSucc ≠ j.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have h10 : i.succ ≠ j.castSucc := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have h11 : i.succ ≠ j.succ := by
    intro he
    apply hne
    apply Fin.ext
    have hv := congrArg Fin.val he
    simp only [Fin.val_succ] at hv
    omega
  simp [simpleSwap, Equiv.swap_apply_def, h00, h01, h10, h11]

lemma isAscent_swap_distant {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val)
    (σ : Equiv.Perm (Fin (n + 1))) :
    isAscent i (simpleSwap j * σ) ↔ isAscent i σ := by
  have hf := simpleSwap_fixed_of_distant i j hne hij hji
  have ha : (simpleSwap j * σ).symm i.castSucc = σ.symm i.castSucc := by
    apply (simpleSwap j * σ).injective
    simpa using hf.1.symm
  have hb : (simpleSwap j * σ).symm i.succ = σ.symm i.succ := by
    apply (simpleSwap j * σ).injective
    simpa using hf.2.symm
  simp [isAscent, ha, hb]

@[simp] lemma simpleSwap_castSucc {n : ℕ} (i : Fin n) :
    simpleSwap i i.castSucc = i.succ := by simp [simpleSwap]

@[simp] lemma simpleSwap_succ {n : ℕ} (i : Fin n) :
    simpleSwap i i.succ = i.castSucc := by simp [simpleSwap]

lemma simpleSwap_commute {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) :
    simpleSwap i * simpleSwap j = simpleSwap j * simpleSwap i := by
  have hf := simpleSwap_fixed_of_distant i j hne hij hji
  have hg := simpleSwap_fixed_of_distant j i hne.symm hji hij
  apply Equiv.ext
  intro k
  by_cases hki : k = i.castSucc
  · subst k
    simp only [Equiv.Perm.mul_apply, hf.1, hf.2, simpleSwap_castSucc]
  · by_cases hki' : k = i.succ
    · subst k
      simp only [Equiv.Perm.mul_apply, hf.1, hf.2, simpleSwap_succ]
    · by_cases hkj : k = j.castSucc
      · subst k
        simp only [Equiv.Perm.mul_apply, hg.1, hg.2, simpleSwap_castSucc]
      · by_cases hkj' : k = j.succ
        · subst k
          simp only [Equiv.Perm.mul_apply, hg.1, hg.2, simpleSwap_succ]
        · simp [simpleSwap, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hki, hki', hkj, hkj']

end StableSteinberg.RootCoordinate

end

/-! ## RootCoordinateSignRelations -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma simple_sign_square_eq {n : ℕ} (i j : Fin n) :
    simple F i (-1) * simple F i (-1) = simple F j (-1) * simple F j (-1) := by
  rw [simple_neg_one_square, simple_neg_one_square]

lemma simple_sign_sq_eq {n : ℕ} (i j : Fin n) :
    simple F i (-1) ^ 2 = simple F j (-1) ^ 2 := by
  simpa only [pow_two] using simple_sign_square_eq F i j

lemma theta_triple_sign {n : ℕ} (i j : Fin n)
    (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    theta F i (theta F j (theta F i (simple F i (-1)))) = simple F j (-1) := by
  rw [theta_simple_neg_one, theta_adjacent_neg_one F j i hij.symm, map_mul,
    map_inv, theta_simple_neg_one, theta_adjacent_neg_one F i j hij]
  calc
    _ = (simple F i (-1) * simple F i (-1)) * (simple F j (-1))⁻¹ := by group
    _ = _ := by rw [simple_sign_square_eq F i j]; simp [mul_assoc]

lemma simple_commute_distant {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) (a b : Fˣ) :
    Commute (simple F i a) (simple F j b) := by
  change simple F i a * simple F j b = simple F j b * simple F i a
  apply Torus.ext
  · change (Pi.mulSingle i a : Fin n → Fˣ) * Pi.mulSingle j b =
      Pi.mulSingle j b * Pi.mulSingle i a
    exact mul_comm _ _
  · change 0 + 0 + cocycle F n (Pi.mulSingle i a) (Pi.mulSingle j b) =
      0 + 0 + cocycle F n (Pi.mulSingle j b) (Pi.mulSingle i a)
    rw [cocycle_single_right, cocycle_single_right, following_single, following_single]
    simp [hne, hne.symm, Ne.symm hij, Ne.symm hji]

lemma descentCarry_commute_distant {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val)
    (σ : Equiv.Perm (Fin (n + 1))) : Commute (descentCarry F i σ) (descentCarry F j σ) := by
  classical
  unfold descentCarry
  split_ifs <;> simp [simple_commute_distant F i j hne hij hji]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBraidBranches -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- All relative-order carry branches of the adjacent braid, including both descending extremes. -/
theorem theta_braid_order_branches {n : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val)
    (t : Torus F n) (p q r : ℕ) :
    theta F i (theta F j (theta F i
        (t * (if p < q then 1 else simple F i (-1))) *
          (if p < r then 1 else simple F j (-1))) *
            (if q < r then 1 else simple F i (-1))) =
    theta F j (theta F i (theta F j
        (t * (if q < r then 1 else simple F j (-1))) *
          (if p < r then 1 else simple F i (-1))) *
            (if p < q then 1 else simple F j (-1))) := by
  have hsq : theta F j (theta F i (theta F j t)) * simple F i (-1) * simple F i (-1) =
      theta F j (theta F i (theta F j t)) * simple F j (-1) * simple F j (-1) := by
    simpa only [mul_assoc] using congrArg
      (fun z => theta F j (theta F i (theta F j t)) * z) (simple_sign_square_eq F i j)
  by_cases hpq : p < q <;> by_cases hpr : p < r <;> by_cases hqr : q < r <;>
    try omega
  all_goals simp only [hpq, hpr, hqr, ↓reduceIte, map_mul]
  all_goals rw [theta_braid F i j hij t]
  all_goals simp only [theta_triple_sign F i j (Or.inl hij),
    theta_triple_sign F j i (Or.inr hij), map_one, mul_one]
  all_goals simp only [theta_simple_neg_one,
    theta_adjacent_neg_one F i j (Or.inl hij), theta_adjacent_neg_one F j i (Or.inr hij)]
  all_goals group
  all_goals
    solve
    | rw [hsq] <;> group
    | rw [← hsq]; group

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateAdjacentPositions -/

section

namespace StableSteinberg.RootCoordinate

lemma simpleSwap_inverse_apply {n : ℕ} (i : Fin n)
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    (simpleSwap i * σ).symm k = σ.symm (simpleSwap i k) := by
  apply (simpleSwap i * σ).injective
  simp [simpleSwap]

lemma adjacent_position_facts {n : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (isAscent j (simpleSwap i * σ) ↔ σ.symm i.castSucc < σ.symm j.succ) ∧
    (isAscent i (simpleSwap j * σ) ↔ σ.symm i.castSucc < σ.symm j.succ) ∧
    (isAscent i (simpleSwap j * (simpleSwap i * σ)) ↔ isAscent j σ) ∧
    (isAscent j (simpleSwap i * (simpleSwap j * σ)) ↔ isAscent i σ) := by
  have hmid : i.succ = j.castSucc := Fin.ext hij
  have hab : i.castSucc ≠ i.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hbc : i.succ ≠ j.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_succ] at hv
    omega
  have hac : i.castSucc ≠ j.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  simp only [isAscent, simpleSwap_inverse_apply]
  simp only [simpleSwap, ← hmid]
  simp [Equiv.swap_apply_def, hab, hbc.symm, hac, hac.symm]

lemma simpleSwap_braid {n : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val) :
    simpleSwap i * simpleSwap j * simpleSwap i =
      simpleSwap j * simpleSwap i * simpleSwap j := by
  have hmid : i.succ = j.castSucc := Fin.ext hij
  have hab : i.castSucc ≠ i.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hbc : i.succ ≠ j.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_succ] at hv
    omega
  have hac : i.castSucc ≠ j.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  unfold simpleSwap
  rw [← hmid]
  rw [Equiv.swap_mul_swap_mul_swap hab hac]
  rw [Equiv.swap_comm i.castSucc i.succ, Equiv.swap_comm i.succ j.succ,
    Equiv.swap_mul_swap_mul_swap hbc.symm hac.symm, Equiv.swap_comm]

end StableSteinberg.RootCoordinate

end

/-! ## RootCoordinateLiftedRelations -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- Distant concrete ascent/descent transformations commute on every state. -/
theorem liftedWeyl_commute {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) (s : NormalizerState F n) :
    liftedWeyl F i (liftedWeyl F j s) = liftedWeyl F j (liftedWeyl F i s) := by
  classical
  have hi : descentCarry F i (simpleSwap j * s.2) = descentCarry F i s.2 := by
    unfold descentCarry
    rw [isAscent_swap_distant i j hne hij hji]
  have hj : descentCarry F j (simpleSwap i * s.2) = descentCarry F j s.2 := by
    unfold descentCarry
    rw [isAscent_swap_distant j i hne.symm hji hij]
  apply Prod.ext
  · change theta F i (theta F j (s.1 * descentCarry F j s.2) *
        descentCarry F i (simpleSwap j * s.2)) =
      theta F j (theta F i (s.1 * descentCarry F i s.2) *
        descentCarry F j (simpleSwap i * s.2))
    rw [hi, hj]
    simp only [map_mul, theta_descentCarry,
      theta_descentCarry_distant F i j hne hij hji,
      theta_descentCarry_distant F j i hne.symm hji hij]
    rw [theta_commute F i j hne hij hji,
      mul_assoc, mul_assoc, (descentCarry_commute_distant F i j hne hij hji s.2).eq]
  · change simpleSwap i * (simpleSwap j * s.2) = simpleSwap j * (simpleSwap i * s.2)
    simpa only [mul_assoc] using
      congrArg (fun σ => σ * s.2) (simpleSwap_commute i j hne hij hji)

/-- All six relative inverse-position orders give the actual adjacent braid on every state. -/
theorem liftedWeyl_braid {n : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val)
    (s : NormalizerState F n) :
    liftedWeyl F i (liftedWeyl F j (liftedWeyl F i s)) =
      liftedWeyl F j (liftedWeyl F i (liftedWeyl F j s)) := by
  classical
  have hf := adjacent_position_facts i j hij s.2
  have hmid : i.succ = j.castSucc := Fin.ext hij
  apply Prod.ext
  · change theta F i (theta F j (theta F i (s.1 * descentCarry F i s.2) *
          descentCarry F j (simpleSwap i * s.2)) *
            descentCarry F i (simpleSwap j * (simpleSwap i * s.2))) =
      theta F j (theta F i (theta F j (s.1 * descentCarry F j s.2) *
          descentCarry F i (simpleSwap j * s.2)) *
            descentCarry F j (simpleSwap i * (simpleSwap j * s.2)))
    unfold descentCarry
    simp only [hf.1, hf.2.1, hf.2.2.1, hf.2.2.2]
    simp only [isAscent, ← hmid]
    simpa only [Fin.lt_def] using theta_braid_order_branches F i j hij s.1
      (s.2.symm i.castSucc).val (s.2.symm i.succ).val (s.2.symm j.succ).val
  · change simpleSwap i * (simpleSwap j * (simpleSwap i * s.2)) =
      simpleSwap j * (simpleSwap i * (simpleSwap j * s.2))
    simpa only [mul_assoc] using
      congrArg (fun σ => σ * s.2) (simpleSwap_braid i j hij)

end StableSteinberg.RootCoordinate

end

end
