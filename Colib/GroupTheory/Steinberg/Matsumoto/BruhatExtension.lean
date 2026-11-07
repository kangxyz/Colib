/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matsumoto.BruhatActions
public import Colib.GroupTheory.Steinberg.Matsumoto.Weyl
public import Colib.GroupTheory.Steinberg.Matsumoto.Torus
public import Colib.GroupTheory.Steinberg.Matsumoto.LiftedWeyl
public import Colib.GroupTheory.Steinberg.Matsumoto.Normalizer
public import Colib.GroupTheory.Steinberg.Matsumoto.NormalizerMatrix
public import Colib.GroupTheory.Steinberg.Matsumoto.MatrixBasics
public import Colib.GroupTheory.Steinberg.Matsumoto.TorusTransporter
public import Colib.LinearAlgebra.Matrix.Bruhat.Coordinates
public import Colib.LinearAlgebra.Matrix.Bruhat.Opposite
public import Colib.LinearAlgebra.Matrix.Bruhat.Decomposition
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Colib.LinearAlgebra.Matrix.Bruhat.RootUpdate
public import Colib.GroupTheory.Steinberg.Matsumoto.WeylTransporter
public import Colib.GroupTheory.Steinberg.Matsumoto.BruhatCoherence
public import Colib.GroupTheory.Steinberg.Matsumoto.BruhatLeftGroup

/-!
# BruhatExtension

Adapted from Quillen Matsumoto/BruhatExtension.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native Stacks
homogeneous Milnor group and native matrix units throughout.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## RootCoordinateBruhatSymmetry -/

section

noncomputable section
universe u v
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The right W(-1) operator has exactly the retained positive H(-1) square. -/
theorem bruhatWeylRight_square {n : ℕ} (i : Fin n) :
    bruhatWeylRight F i * bruhatWeylRight F i =
      bruhatTorusRight F n (simple F i (-1)) := by
  have hi : (bruhatInversion F n)⁻¹ = bruhatInversion F n :=
    (eq_inv_of_mul_eq_one_left (bruhatInversion_square F n)).symm
  have he := congrArg (MulAut.conj (bruhatInversion F n)) (bruhatWeylLeft_square F i)
  rw [map_mul] at he
  change (bruhatInversion F n * bruhatWeylLeft F i * (bruhatInversion F n)⁻¹) *
      (bruhatInversion F n * bruhatWeylLeft F i * (bruhatInversion F n)⁻¹) =
    bruhatInversion F n * bruhatTorusLeft F n ((simple F i (-1))⁻¹) *
      (bruhatInversion F n)⁻¹ at he
  rw [hi, bruhatInversion_torus, inv_inv] at he
  exact he

lemma commute_at_left_iff {S : Type v} (e f : Equiv.Perm S) (s : S)
    (hsq : Commute (e * e) f) :
    e (f (e s)) = f (e (e s)) ↔ e (f s) = f (e s) := by
  have hh : e (e (f s)) = f (e (e s)) := congrArg (fun p : Equiv.Perm S => p s) hsq.eq
  constructor
  · intro h
    exact (e.injective (h.trans hh.symm)).symm
  · intro h
    exact (congrArg e h.symm).trans hh

lemma commute_at_right_iff {S : Type v} (e f : Equiv.Perm S) (s : S)
    (hsq : Commute (f * f) e) :
    e (f (f s)) = f (e (f s)) ↔ e (f s) = f (e s) := by
  simpa only [eq_comm] using commute_at_left_iff f e s hsq

/-- The remaining lifted square is invariant under a left Weyl update. -/
theorem bruhatWeyl_commutes_at_left_iff {n : ℕ} (i k : Fin n) (s : BruhatState F n) :
    bruhatWeylLeft F i (bruhatWeylRight F k (bruhatWeylLeft F i s)) =
        bruhatWeylRight F k (bruhatWeylLeft F i (bruhatWeylLeft F i s)) ↔
      bruhatWeylLeft F i (bruhatWeylRight F k s) =
        bruhatWeylRight F k (bruhatWeylLeft F i s) := by
  apply commute_at_left_iff
  rw [bruhatWeylLeft_square]
  exact bruhatTorusLeft_weylRight F k _

/-- The remaining lifted square is invariant under a right Weyl update. -/
theorem bruhatWeyl_commutes_at_right_iff {n : ℕ} (i k : Fin n) (s : BruhatState F n) :
    bruhatWeylLeft F i (bruhatWeylRight F k (bruhatWeylRight F k s)) =
        bruhatWeylRight F k (bruhatWeylLeft F i (bruhatWeylRight F k s)) ↔
      bruhatWeylLeft F i (bruhatWeylRight F k s) =
        bruhatWeylRight F k (bruhatWeylLeft F i s) := by
  apply commute_at_right_iff
  rw [bruhatWeylRight_square]
  exact (bruhatWeylLeft_torusRight F i _).symm

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatParameters -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma torusToGL_coefficient (n : ℕ) (a : Multiplicative (MilnorKTheory F 2)) :
    torusToGL F n (coefficient F n a) = 1 := by
  simpa only [normalizerCoefficient, MonoidHom.comp_apply, normalizerToGL_torus] using
    normalizerToGL_coefficient F n a

lemma simple_torus_matrix_mul {n : ℕ} (i : Fin n) (a b : Fˣ) :
    torusToGL F n (simple F i a) * torusToGL F n (simple F i b) =
      torusToGL F n (simple F i (a * b)) := by
  rw [← map_mul, simple_mul, map_mul, torusToGL_coefficient, one_mul]

lemma simple_torus_matrix_inv {n : ℕ} (i : Fin n) (a : Fˣ) :
    (torusToGL F n (simple F i a))⁻¹ = torusToGL F n (simple F i a⁻¹) := by
  have he : torusToGL F n (simple F i a) * torusToGL F n (simple F i a⁻¹) = 1 := by
    rw [simple_torus_matrix_mul, mul_inv_cancel, simple_one, map_one]
  have hh := congrArg (fun z => (torusToGL F n (simple F i a))⁻¹ * z) he
  simpa only [mul_assoc, inv_mul_cancel_left, mul_one] using hh.symm

lemma rightWeylCarry_eq_of {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (z : LiftedNormalizer F n)
    (hz : z⁻¹ ∈ leftWeylCell F i)
    (hp : bruhatGL F n g * normalizerToGL F n z =
      bruhatGL F n (g * simpleWMatrix F i (-1))) : rightWeylCarry F i g = z := by
  have hl : leftWeylCarry F i g⁻¹ = z⁻¹ := by
    apply leftWeylCarry_eq_of F i _ _ hz
    have he := congrArg Inv.inv hp
    rw [_root_.mul_inv_rev, ← bruhatGL_inv, ← bruhatGL_inv, _root_.mul_inv_rev,
      simpleWMatrix_neg, inv_inv, ← map_inv] at he
    exact he
  simpa only [rightWeylCarry, inv_inv] using congrArg Inv.inv hl

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateOppositeDiamond -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The opposite nonzero crossing holds in the actual normalizer for every genuine matrix lift. -/
theorem normalizer_opposite_diamond {n : ℕ} (i k : Fin n) (ν : LiftedNormalizer F n)
    (m : _root_.Matrix.Bruhat.MonomialGroup F (n + 1))
    (hm : normalizerToGL F n ν = _root_.Matrix.Bruhat.monomialToGL F (n + 1) m)
    (hk : m.right k.castSucc = i.succ) (hl : m.right k.succ = i.castSucc)
    (u v d : Fˣ)
    (hd : (d : F) = (u : F) * (v : F) -
      ((-m.left i.castSucc * (m.left i.succ)⁻¹ : Fˣ) : F)) :
    (normalizerTorus F n (simple F i (-(d * v⁻¹))))⁻¹ * ν *
        normalizerTorus F n (simple F k v) =
      (normalizerTorus F n (simple F i (-u)))⁻¹ * ν *
        normalizerTorus F n (simple F k (d * u⁻¹)) := by
  let f := -m.left i.castSucc * (m.left i.succ)⁻¹
  have hT (t : Fˣ) : ν * normalizerTorus F n (simple F k t) * ν⁻¹ =
      normalizerCoefficient F n (Multiplicative.ofAdd (pair F f⁻¹ t)) *
        normalizerTorus F n (simple F i t⁻¹) :=
    normalizer_conjugate_simple_opposite F i k ν m hm hk hl t
  have he := congrArg (normalizerTorus F n) (bruhat_torus_diamond F i u v f d hd)
  simp only [map_mul, map_inv] at he
  change (normalizerTorus F n (simple F i (-(d * v⁻¹))))⁻¹ *
      normalizerCoefficient F n (Multiplicative.ofAdd (pair F f⁻¹ v)) *
        normalizerTorus F n (simple F i v⁻¹) =
    (normalizerTorus F n (simple F i (-u)))⁻¹ *
      normalizerCoefficient F n (Multiplicative.ofAdd (pair F f⁻¹ (d * u⁻¹))) *
        normalizerTorus F n (simple F i (d * u⁻¹)⁻¹) at he
  apply mul_right_cancel (b := ν⁻¹)
  calc
    _ = (normalizerTorus F n (simple F i (-(d * v⁻¹))))⁻¹ *
        (ν * normalizerTorus F n (simple F k v) * ν⁻¹) := by group
    _ = (normalizerTorus F n (simple F i (-u)))⁻¹ *
        (ν * normalizerTorus F n (simple F k (d * u⁻¹)) * ν⁻¹) := by
      rw [hT, hT]
      simpa only [mul_assoc] using he
    _ = _ := by group

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatOppositeNonzero -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The opposite nonzero canonical square closes in the actual lifted state. -/
theorem bruhatWeyl_canonical_opposite_nonzero {n : ℕ} (i k : Fin n)
    (s : BruhatState F n) (m : _root_.Matrix.Bruhat.MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.succ) (hl : m.right k.succ = i.castSucc)
    (u v d : Fˣ)
    (hs : s.matrix = _root_.Matrix.Bruhat.simpleBruhatRepresentative F n i k m (u : F) (v : F))
    (hd : (d : F) = (u : F) * (v : F) -
      ((-m.left i.castSucc * (m.left i.succ)⁻¹ : Fˣ) : F)) :
    bruhatWeylLeft F i (bruhatWeylRight F k s) =
      bruhatWeylRight F k (bruhatWeylLeft F i s) := by
  let M := _root_.Matrix.Bruhat.monomialToGL F (n + 1) m
  have h0 : bruhatGL F n s.matrix = M := by
    rw [hs]
    exact congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1))
      (_root_.Matrix.Bruhat.simpleBruhatRepresentative_projection F n i k m (u : F) (v : F))
  have hm : normalizerToGL F n s.normalizer = M := s.compatible.trans h0
  have hL : bruhatGL F n (simpleWMatrix F i 1 * s.matrix) =
      torusToGL F n (simple F i (-u⁻¹)) * M := by
    rw [hs]
    have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1))
      (_root_.Matrix.Bruhat.opposite_left_bruhat_nonzero F n i k m hk hl u (v : F))
    simpa only [bruhatGL, rootWMonomial_toGL, map_mul, rootHMonomial_toGL] using he
  have hR : bruhatGL F n (s.matrix * simpleWMatrix F k (-1)) =
      M * torusToGL F n (simple F k v) := by
    rw [hs]
    have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1))
      (_root_.Matrix.Bruhat.opposite_right_bruhat_nonzero F n i k m hk hl (u : F) v)
    simpa only [bruhatGL, rootWMonomial_toGL, map_mul, rootHMonomial_toGL] using he
  have hD : bruhatGL F n (simpleWMatrix F i 1 * s.matrix * simpleWMatrix F k (-1)) =
      torusToGL F n (simple F i (-d⁻¹)) * M := by
    rw [hs]
    have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1))
      (_root_.Matrix.Bruhat.opposite_crossing_bruhat_nonzero F n i k m hk hl (u : F) (v : F) d hd)
    simpa only [_root_.Matrix.Bruhat.oppositeCrossingMatrix_eq, bruhatGL, rootWMonomial_toGL,
      map_mul, rootHMonomial_toGL] using he
  have hLc : leftWeylCarry F i s.matrix =
      (normalizerTorus F n (simple F i (-u)))⁻¹ := by
    apply leftWeylCarry_eq_of F i _ _ (Or.inr ⟨-u, rfl⟩)
    rw [map_inv, normalizerToGL_torus, h0, hL, simple_torus_matrix_inv]
    simp
  have hRc : rightWeylCarry F k s.matrix = normalizerTorus F n (simple F k v) := by
    apply rightWeylCarry_eq_of F k _ _ (Or.inr ⟨v, rfl⟩)
    rw [h0, hR, normalizerToGL_torus]
  have htransport (t : Fˣ) : M * torusToGL F n (simple F k t) =
      torusToGL F n (simple F i t⁻¹) * M := by
    have he := congrArg (normalizerToGL F n)
      (normalizer_conjugate_simple_opposite F i k s.normalizer m hm hk hl t)
    simp only [map_mul, map_inv, normalizerToGL_torus, normalizerToGL_coefficient,
      one_mul, hm] at he
    have he' := congrArg (fun z => z * M) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he'
  have hRp : bruhatGL F n (simpleWMatrix F i 1 * s.matrix) *
      normalizerToGL F n (normalizerTorus F n (simple F k (d * u⁻¹))) =
        bruhatGL F n (simpleWMatrix F i 1 * s.matrix * simpleWMatrix F k (-1)) := by
    rw [hL, hD, normalizerToGL_torus, mul_assoc, htransport, ← mul_assoc,
      simple_torus_matrix_mul]
    have hu : -u⁻¹ * (d * u⁻¹)⁻¹ = -d⁻¹ := by simp
    rw [hu]
  have hRc' : rightWeylCarry F k (simpleWMatrix F i 1 * s.matrix) =
      normalizerTorus F n (simple F k (d * u⁻¹)) :=
    rightWeylCarry_eq_of F k _ _ (Or.inr ⟨d * u⁻¹, rfl⟩) hRp
  have hdiamond := normalizer_opposite_diamond F i k s.normalizer m hm hk hl u v d hd
  have hLc' : leftWeylCarry F i (s.matrix * simpleWMatrix F k (-1)) =
      (normalizerTorus F n (simple F i (-(d * v⁻¹))))⁻¹ := by
    apply leftWeylCarry_eq_of F i _ _ (Or.inr ⟨-(d * v⁻¹), rfl⟩)
    calc
      _ = normalizerToGL F n
          ((normalizerTorus F n (simple F i (-(d * v⁻¹))))⁻¹ * s.normalizer *
            normalizerTorus F n (simple F k v)) := by
        rw [map_mul, map_mul, normalizerToGL_torus, hm, hR, mul_assoc]
      _ = normalizerToGL F n
          ((normalizerTorus F n (simple F i (-u)))⁻¹ * s.normalizer *
            normalizerTorus F n (simple F k (d * u⁻¹))) := congrArg _ hdiamond
      _ = bruhatGL F n (simpleWMatrix F i 1 * s.matrix) *
          normalizerToGL F n (normalizerTorus F n (simple F k (d * u⁻¹))) := by
        rw [map_mul, map_mul, ← hLc, hm, ← h0, leftWeylCarry_projection]
      _ = _ := by simpa only [mul_assoc] using hRp
  rw [bruhatWeyl_commutes_at_iff, hLc, hRc, hLc', hRc']
  exact hdiamond

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateEqualAlgebra -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma pair_equal_crossing_cancel (c t : Fˣ) :
    pair F c (t * c⁻¹) + pair F (-t) (c * t⁻¹) = 0 := by
  rw [show -t = (-1 : Fˣ) * t by simp]
  simp only [pair_mul_left, pair_mul_right, pair_inv_right, pair_self]
  rw [pair_skew F (-1) c, pair_skew F (-1) t, pair_skew F t c]
  have hc := pair_sign_two F c
  abel_nf at hc ⊢
  simpa only [neg_smul, neg_zero] using congrArg Neg.neg hc

/-- The equal-root crossing identity in the actual torus, including sign symbols. -/
lemma simple_equal_crossing {n : ℕ} (i : Fin n) (c t : Fˣ) :
    (simple F i (-t))⁻¹ * simple F i (-c) =
      coefficient F n (Multiplicative.ofAdd (pair F c (t * c⁻¹))) *
        simple F i (c * t⁻¹) := by
  apply mul_left_cancel (a := simple F i (-t))
  rw [mul_inv_cancel_left]
  have hc := Subgroup.mem_center_iff.mp
    (coefficient_le_center F n ⟨Multiplicative.ofAdd (pair F c (t * c⁻¹)), rfl⟩)
    (simple F i (-t))
  rw [← mul_assoc, hc, mul_assoc, simple_mul, ← mul_assoc, ← map_mul]
  change simple F i (-c) =
    coefficient F n (Multiplicative.ofAdd
      (pair F c (t * c⁻¹) + pair F (-t) (c * t⁻¹))) *
        simple F i (-t * (c * t⁻¹))
  rw [pair_equal_crossing_cancel]
  have he : -t * (c * t⁻¹) = -c := by simp [mul_comm t, mul_assoc]
  rw [he]
  change simple F i (-c) = coefficient F n 1 * simple F i (-c)
  rw [map_one, one_mul]

/-- The equal nonzero rank-one crossing in the actual normalizer. -/
theorem normalizer_equal_crossing {n : ℕ} (i : Fin n) (c t : Fˣ) :
    (normalizerTorus F n (simple F i (-t)))⁻¹ * normalizerW F i (-c) =
      normalizerW F i 1 * normalizerCoefficient F n
        (Multiplicative.ofAdd (pair F c (t * c⁻¹))) *
          normalizerTorus F n (simple F i (t * c⁻¹)) := by
  have ht := normalizerLambda_inv_conjugate_torus F i (simple F i (t * c⁻¹))
  rw [reflection_simple_self] at ht
  have ht' := congrArg (fun z => z * (normalizerLambda F i)⁻¹) ht
  simp only [mul_assoc, mul_inv_cancel, mul_one] at ht'
  have hc := Subgroup.mem_center_iff.mp
    (normalizerCoefficient_le_center F n
      ⟨Multiplicative.ofAdd (pair F c (t * c⁻¹)), rfl⟩) ((normalizerLambda F i)⁻¹)
  rw [normalizerW, normalizerW_one, ← map_inv, ← mul_assoc, ← map_mul,
    simple_equal_crossing, map_mul]
  change (normalizerCoefficient F n (Multiplicative.ofAdd (pair F c (t * c⁻¹))) *
      normalizerTorus F n (simple F i (c * t⁻¹))) * (normalizerLambda F i)⁻¹ = _
  rw [hc]
  simp only [mul_assoc]
  rw [ht']
  congr 2

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateWeylParameters -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma simpleWMatrix_eq_torus_mul_one {n : ℕ} (i : Fin n) (a : Fˣ) :
    simpleWMatrix F i a = torusToGL F n (simple F i a) * simpleWMatrix F i 1 := by
  have he := congrArg (fun z => z * simpleWMatrix F i 1) (simpleWMatrix_h F i a)
  rw [simpleWMatrix_neg F i 1] at he
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using he

lemma simple_torus_matrix_mul_weyl {n : ℕ} (i : Fin n) (a b : Fˣ) :
    torusToGL F n (simple F i a) * simpleWMatrix F i b = simpleWMatrix F i (a * b) := by
  rw [simpleWMatrix_eq_torus_mul_one F i b, ← mul_assoc, simple_torus_matrix_mul,
    ← simpleWMatrix_eq_torus_mul_one]

lemma simpleWMatrix_one_mul_neg {n : ℕ} (i : Fin n) (c : Fˣ) :
    simpleWMatrix F i 1 * simpleWMatrix F i (-c) = torusToGL F n (simple F i c⁻¹) := by
  rw [simpleWMatrix_eq_torus_mul_one F i (-c)]
  have he := torusToGL_reflection_covariance F i 1 (simple F i (-c))
  rw [reflection_simple_self] at he
  have he' := congrArg (fun z => z * simpleWMatrix F i 1) he
  simp only [mul_assoc, inv_mul_cancel, mul_one] at he'
  rw [← mul_assoc, ← he', mul_assoc, simpleWMatrix_one_square,
    simple_torus_matrix_inv, simple_torus_matrix_mul]
  simp

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateEqualDiamond -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The equal nonzero crossing holds for every lift in the actual normalizer. -/
theorem normalizer_equal_diamond {n : ℕ} (i k : Fin n) (ν : LiftedNormalizer F n)
    (m : _root_.Matrix.Bruhat.MonomialGroup F (n + 1))
    (hm : normalizerToGL F n ν = _root_.Matrix.Bruhat.monomialToGL F (n + 1) m)
    (hk : m.right k.castSucc = i.castSucc) (hl : m.right k.succ = i.succ) (t : Fˣ) :
    (normalizerTorus F n (simple F i (-t)))⁻¹ * ν * normalizerW F k (-1) =
      normalizerW F i 1 * ν * normalizerTorus F n
        (simple F k (t * (m.left i.castSucc * (m.left i.succ)⁻¹)⁻¹)) := by
  let c := m.left i.castSucc * (m.left i.succ)⁻¹
  have hW : ν * normalizerW F k (-1) * ν⁻¹ = normalizerW F i (-c) :=
    normalizer_conjugate_W_neg_one F ν m hm i k hk hl
  have hT := normalizer_conjugate_simple_equal F i k ν m hm hk hl (t * c⁻¹)
  apply mul_right_cancel (b := ν⁻¹)
  calc
    _ = (normalizerTorus F n (simple F i (-t)))⁻¹ *
        (ν * normalizerW F k (-1) * ν⁻¹) := by group
    _ = normalizerW F i 1 *
        (ν * normalizerTorus F n (simple F k (t * c⁻¹)) * ν⁻¹) := by
      rw [hW, hT]
      simpa only [mul_assoc] using normalizer_equal_crossing F i c t
    _ = _ := by dsimp [c]; group

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatEqual -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- All equal-orientation canonical lifted squares, including a zero combined pivot. -/
theorem bruhatWeyl_canonical_equal {n : ℕ} (i k : Fin n) (s : BruhatState F n)
    (m : _root_.Matrix.Bruhat.MonomialGroup F (n + 1)) (u v : F)
    (hs : s.matrix = _root_.Matrix.Bruhat.simpleBruhatRepresentative F n i k m u v)
    (hk : m.right k.castSucc = i.castSucc) (hl : m.right k.succ = i.succ) :
    bruhatWeylLeft F i (bruhatWeylRight F k s) =
      bruhatWeylRight F k (bruhatWeylLeft F i s) := by
  let M := _root_.Matrix.Bruhat.monomialToGL F (n + 1) m
  let c := m.left i.castSucc * (m.left i.succ)⁻¹
  have h0 : bruhatGL F n s.matrix = M := by
    rw [hs]
    exact congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1))
      (_root_.Matrix.Bruhat.simpleBruhatRepresentative_projection F n i k m u v)
  have hm : normalizerToGL F n s.normalizer = M := s.compatible.trans h0
  have hL : bruhatGL F n (simpleWMatrix F i 1 * s.matrix) = simpleWMatrix F i 1 * M := by
    rw [hs]
    have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1))
      (_root_.Matrix.Bruhat.equal_left_bruhat F n i k m hk hl u v)
    simpa only [bruhatGL, rootWMonomial_toGL, map_mul] using he
  have hR : bruhatGL F n (s.matrix * simpleWMatrix F k (-1)) =
      M * simpleWMatrix F k (-1) := by
    rw [hs]
    have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1))
      (_root_.Matrix.Bruhat.equal_right_bruhat F n i k m hk hl u v)
    simpa only [bruhatGL, rootWMonomial_toGL, map_mul] using he
  have htransport : M * simpleWMatrix F k (-1) = simpleWMatrix F i (-c) * M := by
    have he := congrArg (normalizerToGL F n)
      (normalizer_conjugate_W_neg_one F s.normalizer m hm i k hk hl)
    simp only [map_mul, map_inv, normalizerToGL_W, hm] at he
    have he' := congrArg (fun z => z * M) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he'
  rcases _root_.Matrix.Bruhat.equal_crossing_bruhat_cases F n i k m hk hl u v with
    ⟨_, hcross⟩ | ⟨t, _, hcross⟩
  · have hD : bruhatGL F n (simpleWMatrix F i 1 * s.matrix * simpleWMatrix F k (-1)) =
        torusToGL F n (simple F i c⁻¹) * M := by
      rw [hs]
      have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1)) hcross
      simpa only [_root_.Matrix.Bruhat.equalCrossingMatrix,
        _root_.Matrix.Bruhat.equalRootCoefficient,
        c, M, bruhatGL, rootWMonomial_toGL,
        map_mul, rootHMonomial_toGL] using he
    apply bruhatWeyl_commutes_of_ratio_square
    rw [hD, hL, h0, hR, mul_inv_cancel_right, htransport, ← mul_assoc,
      simpleWMatrix_one_mul_neg]
  · have hD : bruhatGL F n (simpleWMatrix F i 1 * s.matrix * simpleWMatrix F k (-1)) =
        simpleWMatrix F i (c * t⁻¹) * M := by
      rw [hs]
      have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1)) hcross
      simpa only [_root_.Matrix.Bruhat.equalCrossingMatrix,
        _root_.Matrix.Bruhat.equalRootCoefficient,
        c, M, bruhatGL, rootWMonomial_toGL,
        map_mul] using he
    have hLc : leftWeylCarry F i s.matrix = normalizerW F i 1 := by
      apply leftWeylCarry_eq_of F i _ _ (Or.inl rfl)
      rw [h0, hL, normalizerToGL_W]
    have hRc : rightWeylCarry F k s.matrix = normalizerW F k (-1) := by
      apply rightWeylCarry_eq_of F k _ _
      · left
        rw [normalizerW_neg, inv_inv]
      · rw [h0, hR, normalizerToGL_W]
    have hLp : normalizerToGL F n ((normalizerTorus F n (simple F i (-t)))⁻¹) *
        bruhatGL F n (s.matrix * simpleWMatrix F k (-1)) =
          bruhatGL F n (simpleWMatrix F i 1 * s.matrix * simpleWMatrix F k (-1)) := by
      rw [map_inv, normalizerToGL_torus, hR, hD, htransport, simple_torus_matrix_inv,
        ← mul_assoc, simple_torus_matrix_mul_weyl]
      have he : (-t)⁻¹ * -c = c * t⁻¹ := by simp [mul_comm]
      rw [he]
    have hLc' : leftWeylCarry F i (s.matrix * simpleWMatrix F k (-1)) =
        (normalizerTorus F n (simple F i (-t)))⁻¹ := by
      apply leftWeylCarry_eq_of F i _ _ (Or.inr ⟨-t, rfl⟩)
      simpa only [mul_assoc] using hLp
    have hdiamond := normalizer_equal_diamond F i k s.normalizer m hm hk hl t
    have hRc' : rightWeylCarry F k (simpleWMatrix F i 1 * s.matrix) =
        normalizerTorus F n (simple F k (t * c⁻¹)) := by
      apply rightWeylCarry_eq_of F k _ _ (Or.inr ⟨t * c⁻¹, rfl⟩)
      calc
        _ = normalizerToGL F n (normalizerW F i 1 * s.normalizer *
            normalizerTorus F n (simple F k (t * c⁻¹))) := by
          rw [map_mul, map_mul, normalizerToGL_W, hm, hL]
        _ = normalizerToGL F n ((normalizerTorus F n (simple F i (-t)))⁻¹ *
            s.normalizer * normalizerW F k (-1)) := congrArg _ hdiamond.symm
        _ = normalizerToGL F n ((normalizerTorus F n (simple F i (-t)))⁻¹) *
            bruhatGL F n (s.matrix * simpleWMatrix F k (-1)) := by
          rw [map_mul, map_mul, normalizerToGL_W, hm, hR, mul_assoc]
        _ = _ := hLp
    rw [bruhatWeyl_commutes_at_iff, hLc, hRc, hLc', hRc']
    exact hdiamond

/-- Equal-orientation coherence on every original lifted state. -/
theorem bruhatWeyl_equal {n : ℕ} (i k : Fin n) (s : BruhatState F n)
    (hk : (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.castSucc = i.castSucc)
    (hl : (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.succ = i.succ) :
    bruhatWeylLeft F i (bruhatWeylRight F k s) =
      bruhatWeylRight F k (bruhatWeylLeft F i s) := by
  obtain ⟨u, v, t, ht, _, he⟩ := bruhatWeyl_canonical_reduction F i k s
  exact he.mpr (bruhatWeyl_canonical_equal F i k t _ u v ht hk hl)

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatOpposite -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The opposite canonical square, including zero branches transferred to equal orientation. -/
theorem bruhatWeyl_canonical_opposite {n : ℕ} (i k : Fin n) (s : BruhatState F n)
    (m : _root_.Matrix.Bruhat.MonomialGroup F (n + 1)) (u v : F)
    (hs : s.matrix = _root_.Matrix.Bruhat.simpleBruhatRepresentative F n i k m u v)
    (hk : m.right k.castSucc = i.succ) (hl : m.right k.succ = i.castSucc) :
    bruhatWeylLeft F i (bruhatWeylRight F k s) =
      bruhatWeylRight F k (bruhatWeylLeft F i s) := by
  by_cases hu : u = 0
  · subst u
    have hleft : _root_.Matrix.Bruhat.bruhatMonomial F (n + 1) (bruhatWeylLeft F i s).matrix =
        _root_.Matrix.Bruhat.rootWMonomial F i.castSucc i.succ 1 * m := by
      change _root_.Matrix.Bruhat.bruhatMonomial F (n + 1) (simpleWMatrix F i 1 * s.matrix) = _
      rw [hs, ← rootWMonomial_toGL]
      exact _root_.Matrix.Bruhat.simple_left_bruhat_zero F n i k m v
    apply (bruhatWeyl_commutes_at_left_iff F i k s).mp
    apply bruhatWeyl_equal
    · rw [hleft]
      change Equiv.swap i.castSucc i.succ (m.right k.castSucc) = i.castSucc
      rw [hk, Equiv.swap_apply_right]
    · rw [hleft]
      change Equiv.swap i.castSucc i.succ (m.right k.succ) = i.succ
      rw [hl, Equiv.swap_apply_left]
  by_cases hv : v = 0
  · subst v
    have hright : _root_.Matrix.Bruhat.bruhatMonomial F (n + 1) (bruhatWeylRight F k s).matrix =
        m * _root_.Matrix.Bruhat.rootWMonomial F k.castSucc k.succ (-1) := by
      rw [bruhatWeylRight_matrix, hs, ← rootWMonomial_toGL]
      exact _root_.Matrix.Bruhat.simple_right_bruhat_zero F n i k m u
    apply (bruhatWeyl_commutes_at_right_iff F i k s).mp
    apply bruhatWeyl_equal
    · rw [hright]
      change m.right (Equiv.swap k.castSucc k.succ k.castSucc) = i.castSucc
      rw [Equiv.swap_apply_left, hl]
    · rw [hright]
      change m.right (Equiv.swap k.castSucc k.succ k.succ) = i.succ
      rw [Equiv.swap_apply_right, hk]
  let U := Units.mk0 u hu
  let V := Units.mk0 v hv
  let f := -m.left i.castSucc * (m.left i.succ)⁻¹
  by_cases hd : u * v - (f : F) = 0
  · have hcross : _root_.Matrix.Bruhat.bruhatMonomial F (n + 1)
        (bruhatWeylLeft F i (bruhatWeylRight F k s)).matrix =
          _root_.Matrix.Bruhat.rootWMonomial F i.castSucc i.succ V * m := by
      have he := _root_.Matrix.Bruhat.opposite_crossing_bruhat_zero F n i k m hk hl U V
        (sub_eq_zero.mp hd)
      change _root_.Matrix.Bruhat.bruhatMonomial F (n + 1)
        (simpleWMatrix F i 1 * (bruhatWeylRight F k s).matrix) = _
      rw [bruhatWeylRight_matrix, hs]
      simpa only [_root_.Matrix.Bruhat.oppositeCrossingMatrix_eq, rootWMonomial_toGL,
        mul_assoc, U, V, Units.val_mk0] using he
    apply (bruhatWeyl_commutes_at_right_iff F i k s).mp
    apply (bruhatWeyl_commutes_at_left_iff F i k (bruhatWeylRight F k s)).mp
    apply bruhatWeyl_equal
    · rw [hcross]
      change Equiv.swap i.castSucc i.succ (m.right k.castSucc) = i.castSucc
      rw [hk, Equiv.swap_apply_right]
    · rw [hcross]
      change Equiv.swap i.castSucc i.succ (m.right k.succ) = i.succ
      rw [hl, Equiv.swap_apply_left]
  · exact bruhatWeyl_canonical_opposite_nonzero F i k s m hk hl U V
      (Units.mk0 (u * v - (f : F)) hd) hs rfl

/-- Opposite-orientation coherence on every original lifted state. -/
theorem bruhatWeyl_opposite {n : ℕ} (i k : Fin n) (s : BruhatState F n)
    (hk : (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.castSucc = i.succ)
    (hl : (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.succ = i.castSucc) :
    bruhatWeylLeft F i (bruhatWeylRight F k s) =
      bruhatWeylRight F k (bruhatWeylLeft F i s) := by
  obtain ⟨u, v, t, ht, _, he⟩ := bruhatWeyl_canonical_reduction F i k s
  exact he.mpr (bruhatWeyl_canonical_opposite F i k t _ u v ht hk hl)

/-- Actual all-state Weyl/Weyl coherence, over every field and in every finite rank. -/
theorem bruhatWeylLeft_weylRight {n : ℕ} (i k : Fin n) :
    Commute (bruhatWeylLeft F i) (bruhatWeylRight F k) := by
  apply Equiv.ext
  intro s
  by_cases he : (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.castSucc =
    i.castSucc ∧
      (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.succ = i.succ
  · exact bruhatWeyl_equal F i k s he.1 he.2
  by_cases ho : (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.castSucc = i.succ ∧
      (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.succ = i.castSucc
  · exact bruhatWeyl_opposite F i k s ho.1 ho.2
  exact bruhatWeyl_distinct F i k s he ho

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatExtension -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- Every actual left operator commutes with the entire concrete right group. -/
theorem bruhatLeftGroup_le_rightCentralizer (n : ℕ) :
    BruhatLeftGroup F n ≤ Subgroup.centralizer (BruhatRightGroup F n : Set _) := by
  have hgen (e : Equiv.Perm (BruhatState F n))
      (hU : ∀ U, Commute e (bruhatUpperRight F n U))
      (hT : ∀ h, Commute e (bruhatTorusRight F n h))
      (hW : ∀ i, Commute e (bruhatWeylRight F i)) :
      e ∈ Subgroup.centralizer (BruhatRightGroup F n : Set _) := by
    have hle : BruhatRightGroup F n ≤ Subgroup.centralizer ({e} : Set _) := by
      apply (Subgroup.closure_le _).mpr
      rintro r ((⟨U, rfl⟩ | ⟨h, rfl⟩) | ⟨i, rfl⟩)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hU U).eq.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hT h).eq.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hW i).eq.symm
    apply Subgroup.mem_centralizer_iff.mpr
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hr)
  apply (Subgroup.closure_le _).mpr
  rintro e ((⟨U, rfl⟩ | ⟨h, rfl⟩) | ⟨i, rfl⟩)
  · exact hgen _ (bruhatUpperLeft_upperRight F n U) (bruhatUpperLeft_torusRight F n U)
      (fun i => bruhatUpperLeft_weylRight F i U)
  · exact hgen _ (bruhatTorusLeft_upperRight F n h) (bruhatTorusLeft_torusRight F n h)
      (fun i => bruhatTorusLeft_weylRight F i h)
  · exact hgen _ (bruhatWeylLeft_upperRight F i) (bruhatWeylLeft_torusRight F i)
      (bruhatWeylLeft_weylRight F i)

/-- Transitivity of the actual right group makes basepoint evaluation faithful on the left group. -/
theorem bruhatLeft_base_injective (n : ℕ) :
    Function.Injective (fun e : BruhatLeftGroup F n => e.val (bruhatBase F n)) := by
  intro e f hbase
  change e.val (bruhatBase F n) = f.val (bruhatBase F n) at hbase
  apply Subtype.ext
  apply Equiv.ext
  intro s
  obtain ⟨r, hr, hs⟩ := bruhatRightGroup_transitive F n s
  have he := Subgroup.mem_centralizer_iff.mp
    (bruhatLeftGroup_le_rightCentralizer F n e.property) r hr
  have hf := Subgroup.mem_centralizer_iff.mp
    (bruhatLeftGroup_le_rightCentralizer F n f.property) r hr
  have he' := congrArg (fun p : Equiv.Perm (BruhatState F n) => p (bruhatBase F n)) he
  have hf' := congrArg (fun p : Equiv.Perm (BruhatState F n) => p (bruhatBase F n)) hf
  change r (e.val (bruhatBase F n)) = e.val (r (bruhatBase F n)) at he'
  change r (f.val (bruhatBase F n)) = f.val (r (bruhatBase F n)) at hf'
  rw [hbase] at he'
  rw [← hs]
  exact he'.symm.trans hf'

/-- The entire actual finite matrix kernel is precisely the original faithful Milnor coefficient. -/
theorem bruhatLeftToGL_ker (n : ℕ) :
    (bruhatLeftToGL F n).ker = (bruhatLeftCoefficient F n).range := by
  apply le_antisymm
  · intro e he
    let t := e.val (bruhatBase F n)
    have hm : t.matrix = 1 := he
    have hk : t.normalizer ∈ (normalizerToGL F n).ker := by
      change normalizerToGL F n t.normalizer = 1
      rw [t.compatible, hm, bruhatGL_one]
    rw [normalizerToGL_ker] at hk
    obtain ⟨a, ha⟩ := hk
    refine ⟨a, ?_⟩
    apply bruhatLeft_base_injective F n
    apply BruhatState.ext
    · change (bruhatLeftToGL F n (bruhatLeftCoefficient F n a)) = t.matrix
      rw [bruhatLeftToGL_coefficient, hm]
    · change normalizerCoefficient F n a * 1 = t.normalizer
      rw [mul_one, ha]
  · rintro e ⟨a, rfl⟩
    exact bruhatLeftToGL_coefficient F n a

/-- Centrality is discharged for the constructed finite extension over every field. -/
theorem bruhatLeftToGL_ker_central (n : ℕ) :
    (bruhatLeftToGL F n).ker ≤ Subgroup.center (BruhatLeftGroup F n) := by
  rw [bruhatLeftToGL_ker]
  exact bruhatLeftCoefficient_le_center F n

end StableSteinberg.RootCoordinate

end

end
