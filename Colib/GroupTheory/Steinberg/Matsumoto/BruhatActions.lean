/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matsumoto.NormalizerMatrix
public import Colib.LinearAlgebra.Matrix.Bruhat.RootUpdate
public import Colib.LinearAlgebra.Matrix.Bruhat.Coordinates
public import Colib.LinearAlgebra.Matrix.Bruhat.Decomposition
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Colib.GroupTheory.Steinberg.Matsumoto.MatrixBasics
public import Colib.GroupTheory.Steinberg.Matsumoto.Torus
public import Colib.GroupTheory.Steinberg.Matsumoto.Weyl
public import Colib.GroupTheory.Steinberg.Matsumoto.LiftedWeyl
public import Colib.GroupTheory.Steinberg.Matsumoto.Normalizer
public import Colib.LinearAlgebra.Matrix.Bruhat.Reduction
public import Colib.LinearAlgebra.Matrix.Bruhat.Opposite

/-!
# BruhatActions

Adapted from Quillen Matsumoto/BruhatActions.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native Stacks
homogeneous Milnor group and native matrix units throughout.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## RootCoordinateBruhatMatrix -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The actual GL value of the unique finite Bruhat monomial. -/
def bruhatGL (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  _root_.Matrix.Bruhat.monomialToGL F (n + 1) (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) g)

@[simp] lemma bruhatGL_one (n : ℕ) : bruhatGL F n 1 = 1 := by
  simp [bruhatGL]

@[simp] lemma bruhatGL_inv (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    bruhatGL F n g⁻¹ = (bruhatGL F n g)⁻¹ := by
  simp [bruhatGL, _root_.Matrix.Bruhat.bruhatMonomial_inv]

lemma torusToGL_eq_diagonalGL (n : ℕ) (h : Torus F n) :
    torusToGL F n h = _root_.Matrix.Bruhat.diagonalGL F (n + 1) (diagonalCoordinates F h.diagonal)
      := by
  apply Units.ext
  rfl

lemma rootHMonomial_toGL {n : ℕ} (i : Fin n) (a : Fˣ) :
    _root_.Matrix.Bruhat.monomialToGL F (n + 1) (_root_.Matrix.Bruhat.rootHMonomial F i.castSucc
      i.succ a) =
      torusToGL F n (simple F i a) := by
  apply Units.ext
  ext r s
  rw [torusToGL_simple_entry]
  rfl

lemma rootWMonomial_toGL {n : ℕ} (i : Fin n) (a : Fˣ) :
    _root_.Matrix.Bruhat.monomialToGL F (n + 1) (_root_.Matrix.Bruhat.rootWMonomial F i.castSucc
      i.succ a) =
      simpleWMatrix F i a := by
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  apply Units.ext
  ext r s
  rw [simpleWMatrix_entry]
  change (if r = Equiv.swap i.castSucc i.succ s then
      ((Pi.mulSingle i.castSucc a * Pi.mulSingle i.succ (-a⁻¹) : Fin (n + 1) → Fˣ) r : F)
      else 0) = _
  by_cases hri : r = i.castSucc <;> by_cases hrj : r = i.succ <;>
    by_cases hsi : s = i.castSucc <;> by_cases hsj : s = i.succ <;>
      simp_all [Equiv.swap_apply_def, eq_comm]

lemma bruhatGL_upper (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (U V : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    bruhatGL F n ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * g * V) =
      bruhatGL F n g := by
  simp only [bruhatGL, _root_.Matrix.Bruhat.bruhatMonomial_unipotent_invariant]

lemma bruhatGL_torus_left (n : ℕ) (h : Torus F n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    bruhatGL F n (torusToGL F n h * g) = torusToGL F n h * bruhatGL F n g := by
  rw [torusToGL_eq_diagonalGL]
  simp only [bruhatGL, _root_.Matrix.Bruhat.bruhatMonomial_diagonal_left, map_mul]
  rfl

lemma bruhatGL_torus_right (n : ℕ) (h : Torus F n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    bruhatGL F n (g * torusToGL F n h) = bruhatGL F n g * torusToGL F n h := by
  rw [torusToGL_eq_diagonalGL]
  simp only [bruhatGL, _root_.Matrix.Bruhat.bruhatMonomial_diagonal_right, map_mul]
  rfl

lemma upperUnipotent_det (n : ℕ) (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    Matrix.GeneralLinearGroup.det (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) = 1 := by
  apply Units.ext
  change Matrix.det (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val = 1
  rw [Matrix.det_of_isUpperTriangular U.property.1]
  simp [U.property.2]

lemma bruhatGL_det (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    Matrix.GeneralLinearGroup.det (bruhatGL F n g) = Matrix.GeneralLinearGroup.det g := by
  obtain ⟨U, V, hg⟩ := _root_.Matrix.Bruhat.bruhatMonomial_factorization F (n + 1) g
  change g = (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * bruhatGL F n g * V at hg
  conv_rhs => rw [hg, map_mul, map_mul, upperUnipotent_det, upperUnipotent_det, one_mul, mul_one]

lemma bruhatGL_left_simple {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    bruhatGL F n (simpleWMatrix F i 1 * g) = simpleWMatrix F i 1 * bruhatGL F n g ∨
      ∃ a : Fˣ, bruhatGL F n (simpleWMatrix F i 1 * g) =
        (torusToGL F n (simple F i a))⁻¹ * bruhatGL F n g := by
  rcases _root_.Matrix.Bruhat.bruhatMonomial_left_simple F n i g with h | ⟨a, h⟩
  · left
    have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1)) h
    simpa only [bruhatGL, rootWMonomial_toGL, map_mul] using he
  · right
    refine ⟨a, ?_⟩
    have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1)) h
    simpa only [bruhatGL, rootWMonomial_toGL, map_mul, map_inv, rootHMonomial_toGL] using he

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatState -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- Actual matrices equipped with a lift of their unique Bruhat monomial. -/
@[ext] structure BruhatState (n : ℕ) where
  /-- The original finite matrix. -/
  matrix : Matrix.GeneralLinearGroup (Fin (n + 1)) F
  /-- An actual normalizer lift of its Bruhat monomial. -/
  normalizer : LiftedNormalizer F n
  compatible : normalizerToGL F n normalizer = bruhatGL F n matrix

/-- The specified identity state. -/
def bruhatBase (n : ℕ) : BruhatState F n := ⟨1, 1, by simp⟩

lemma bruhatState_det (n : ℕ) (s : BruhatState F n) :
    Matrix.GeneralLinearGroup.det s.matrix = 1 := by
  rw [← bruhatGL_det, ← s.compatible]
  exact normalizerToGL_det F n s.normalizer

/-- Every actual determinant-one matrix has a lifted Bruhat state. -/
theorem bruhatState_exists (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hg : Matrix.GeneralLinearGroup.det g = 1) : ∃ s : BruhatState F n, s.matrix = g := by
  let m := _root_.Matrix.Bruhat.bruhatMonomial F (n + 1) g
  have hd : Matrix.GeneralLinearGroup.det (bruhatGL F n g) = 1 := by rw [bruhatGL_det, hg]
  obtain ⟨ν, hν⟩ := normalizerToGL_row_preimage F (bruhatGL F n g) m.right m.left
    (fun _ _ => rfl) hd
  exact ⟨⟨g, ν, hν⟩, rfl⟩

/-- Matrix and normalizer inversion together preserve the actual compatibility equation. -/
def bruhatInversion (n : ℕ) : Equiv.Perm (BruhatState F n) where
  toFun s := ⟨s.matrix⁻¹, s.normalizer⁻¹, by rw [map_inv, s.compatible, bruhatGL_inv]⟩
  invFun s := ⟨s.matrix⁻¹, s.normalizer⁻¹, by rw [map_inv, s.compatible, bruhatGL_inv]⟩
  left_inv s := by ext <;> simp
  right_inv s := by ext <;> simp

/-- Literal left upper-unitriangular multiplication on the lifted Bruhat set. -/
def bruhatUpperLeft (n : ℕ) (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    Equiv.Perm (BruhatState F n) where
  toFun s := ⟨U * s.matrix, s.normalizer, by
    simpa only [Subgroup.coe_one, mul_one] using
      s.compatible.trans (bruhatGL_upper F n s.matrix U 1).symm⟩
  invFun s := ⟨U⁻¹ * s.matrix, s.normalizer, by
    simpa only [Subgroup.coe_one, mul_one] using
      s.compatible.trans (bruhatGL_upper F n s.matrix U⁻¹ 1).symm⟩
  left_inv s := by ext <;> simp
  right_inv s := by ext <;> simp

/-- Literal left multiplication by the existing torus and its projected diagonal. -/
def bruhatTorusLeft (n : ℕ) (h : Torus F n) : Equiv.Perm (BruhatState F n) where
  toFun s := ⟨torusToGL F n h * s.matrix, normalizerTorus F n h * s.normalizer, by
    rw [map_mul, normalizerToGL_torus, s.compatible, bruhatGL_torus_left]⟩
  invFun s := ⟨torusToGL F n h⁻¹ * s.matrix, normalizerTorus F n h⁻¹ * s.normalizer, by
    rw [map_mul, normalizerToGL_torus, s.compatible, bruhatGL_torus_left]⟩
  left_inv s := by ext <;> simp
  right_inv s := by ext <;> simp

@[simp] lemma bruhatUpperLeft_matrix {n : ℕ} (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1))
    (s : BruhatState F n) : (bruhatUpperLeft F n U s).matrix = U * s.matrix := rfl

@[simp] lemma bruhatUpperLeft_normalizer {n : ℕ} (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1))
    (s : BruhatState F n) : (bruhatUpperLeft F n U s).normalizer = s.normalizer := rfl

@[simp] lemma bruhatTorusLeft_matrix {n : ℕ} (h : Torus F n) (s : BruhatState F n) :
    (bruhatTorusLeft F n h s).matrix = torusToGL F n h * s.matrix := rfl

@[simp] lemma bruhatTorusLeft_normalizer {n : ℕ} (h : Torus F n) (s : BruhatState F n) :
    (bruhatTorusLeft F n h s).normalizer = normalizerTorus F n h * s.normalizer := rfl

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatCarry -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma simpleTorus_matrix_injective {n : ℕ} (i : Fin n) :
    Function.Injective (fun a : Fˣ => torusToGL F n (simple F i a)) := by
  intro a b he
  apply Units.ext
  have h := congrArg (fun g : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
    g.val i.castSucc i.castSucc) he
  simpa [torusToGL_simple_entry, simpleDiagonal, i.castSucc_lt_succ.ne] using h

lemma simpleWMatrix_ne_torus {n : ℕ} (i : Fin n) (a : Fˣ) (h : Torus F n) :
    simpleWMatrix F i a ≠ torusToGL F n h := by
  intro he
  have he' := congrArg (fun g : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
    g.val i.castSucc i.succ) he
  rw [simpleWMatrix_entry] at he'
  change (if i.castSucc = i.castSucc then (if i.succ = i.succ then (a : F) else 0)
    else _) = (Matrix.diagonal (fun k => (diagonalCoordinates F h.diagonal k : F)))
      i.castSucc i.succ at he'
  simp [i.castSucc_lt_succ.ne] at he'

/-- The two actual normalized lifts allowed by a left simple Bruhat update. -/
def leftWeylCell {n : ℕ} (i : Fin n) : Set (LiftedNormalizer F n) :=
  {z | z = normalizerW F i 1 ∨ ∃ a : Fˣ, z = (normalizerTorus F n (simple F i a))⁻¹}

/-- Matrix projection is injective on this explicit two-cell family. -/
lemma leftWeylCell_injective {n : ℕ} (i : Fin n) :
    Set.InjOn (normalizerToGL F n) (leftWeylCell F i) := by
  intro x hx y hy hxy
  rcases hx with rfl | ⟨a, rfl⟩ <;> rcases hy with rfl | ⟨b, rfl⟩
  · rfl
  · exfalso
    rw [normalizerToGL_W, map_inv, normalizerToGL_torus, ← map_inv] at hxy
    exact simpleWMatrix_ne_torus F i 1 _ hxy
  · exfalso
    rw [normalizerToGL_W, map_inv, normalizerToGL_torus, ← map_inv] at hxy
    exact simpleWMatrix_ne_torus F i 1 _ hxy.symm
  · rw [map_inv, map_inv, normalizerToGL_torus, normalizerToGL_torus] at hxy
    have hab := simpleTorus_matrix_injective F i (inv_injective hxy)
    rw [hab]

lemma leftWeylCarry_exists {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    ∃ z ∈ leftWeylCell F i,
      normalizerToGL F n z * bruhatGL F n g = bruhatGL F n (simpleWMatrix F i 1 * g) := by
  rcases bruhatGL_left_simple F i g with h | ⟨a, h⟩
  · exact ⟨normalizerW F i 1, Or.inl rfl, by rw [normalizerToGL_W]; exact h.symm⟩
  · refine ⟨(normalizerTorus F n (simple F i a))⁻¹, Or.inr ⟨a, rfl⟩, ?_⟩
    rw [map_inv, normalizerToGL_torus]
    exact h.symm

/-- The unique genuine lift supplied by the actual two-case Bruhat theorem. -/
def leftWeylCarry {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) : LiftedNormalizer F n :=
  Classical.choose (leftWeylCarry_exists F i g)

lemma leftWeylCarry_mem {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    leftWeylCarry F i g ∈ leftWeylCell F i :=
  (Classical.choose_spec (leftWeylCarry_exists F i g)).1

lemma leftWeylCarry_projection {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    normalizerToGL F n (leftWeylCarry F i g) * bruhatGL F n g =
      bruhatGL F n (simpleWMatrix F i 1 * g) :=
  (Classical.choose_spec (leftWeylCarry_exists F i g)).2

lemma leftWeylCarry_eq_of {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (z : LiftedNormalizer F n)
    (hz : z ∈ leftWeylCell F i)
    (hp : normalizerToGL F n z * bruhatGL F n g =
      bruhatGL F n (simpleWMatrix F i 1 * g)) : leftWeylCarry F i g = z := by
  apply leftWeylCell_injective F i (leftWeylCarry_mem F i g) hz
  exact mul_right_cancel ((leftWeylCarry_projection F i g).trans hp.symm)

/-- The carry only depends on the two original Bruhat monomials. -/
lemma leftWeylCarry_congr {n : ℕ} (i : Fin n)
    (g h : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (he : bruhatGL F n g = bruhatGL F n h)
    (hwe : bruhatGL F n (simpleWMatrix F i 1 * g) =
      bruhatGL F n (simpleWMatrix F i 1 * h)) : leftWeylCarry F i g = leftWeylCarry F i h := by
  apply leftWeylCarry_eq_of F i g _ (leftWeylCarry_mem F i h)
  rw [he, hwe]
  exact leftWeylCarry_projection F i h

/-- The second carry retains the inverse H(-1) square before any matrix projection. -/
lemma leftWeylCell_square_partner {n : ℕ} (i : Fin n) (z : LiftedNormalizer F n)
    (hz : z ∈ leftWeylCell F i) :
    (normalizerTorus F n (simple F i (-1)))⁻¹ * z⁻¹ ∈ leftWeylCell F i := by
  rcases hz with rfl | ⟨a, rfl⟩
  · left
    have hs := normalizerW_one_square F i
    rw [map_inv] at hs
    rw [← hs]
    simp [mul_assoc]
  · right
    refine ⟨-a⁻¹, ?_⟩
    rw [inv_inv, simple_inverse_parameter_neg F i a⁻¹, inv_inv, map_mul, map_inv,
      _root_.mul_inv_rev, inv_inv]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatWeyl -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma leftWeylCarry_square {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    leftWeylCarry F i (simpleWMatrix F i 1 * g) * leftWeylCarry F i g =
      (normalizerTorus F n (simple F i (-1)))⁻¹ := by
  have hc : leftWeylCarry F i (simpleWMatrix F i 1 * g) =
      (normalizerTorus F n (simple F i (-1)))⁻¹ * (leftWeylCarry F i g)⁻¹ := by
    apply leftWeylCarry_eq_of F i _ _
      (leftWeylCell_square_partner F i _ (leftWeylCarry_mem F i g))
    rw [map_mul, map_inv, normalizerToGL_torus, map_inv,
      ← leftWeylCarry_projection F i g, mul_assoc, inv_mul_cancel_left,
      ← mul_assoc (simpleWMatrix F i 1), simpleWMatrix_one_square]
    simpa only [map_inv] using (bruhatGL_torus_left F n ((simple F i (-1))⁻¹) g).symm
  rw [hc]
  simp [mul_assoc]

/-- The literal left W_i(1) update, with its uniquely selected normalizer carry. -/
def bruhatWeylLeftFun {n : ℕ} (i : Fin n) (s : BruhatState F n) : BruhatState F n :=
  ⟨simpleWMatrix F i 1 * s.matrix, leftWeylCarry F i s.matrix * s.normalizer, by
    rw [map_mul, s.compatible, leftWeylCarry_projection]⟩

lemma bruhatWeylLeftFun_square {n : ℕ} (i : Fin n) (s : BruhatState F n) :
    bruhatWeylLeftFun F i (bruhatWeylLeftFun F i s) =
      bruhatTorusLeft F n ((simple F i (-1))⁻¹) s := by
  apply BruhatState.ext
  · change simpleWMatrix F i 1 * (simpleWMatrix F i 1 * s.matrix) = _
    rw [← mul_assoc, simpleWMatrix_one_square]
    rfl
  · change leftWeylCarry F i (simpleWMatrix F i 1 * s.matrix) *
      (leftWeylCarry F i s.matrix * s.normalizer) = _
    rw [← mul_assoc, leftWeylCarry_square, ← map_inv]
    rfl

lemma bruhatWeylLeftFun_bijective {n : ℕ} (i : Fin n) :
    Function.Bijective (bruhatWeylLeftFun F i) := by
  constructor
  · intro s t he
    apply (bruhatTorusLeft F n ((simple F i (-1))⁻¹)).injective
    rw [← bruhatWeylLeftFun_square, ← bruhatWeylLeftFun_square, he]
  · intro t
    obtain ⟨s, hs⟩ := (bruhatTorusLeft F n ((simple F i (-1))⁻¹)).surjective t
    exact ⟨bruhatWeylLeftFun F i s, (bruhatWeylLeftFun_square F i s).trans hs⟩

/-- The actual lifted left W_i(1) permutation. -/
def bruhatWeylLeft {n : ℕ} (i : Fin n) : Equiv.Perm (BruhatState F n) :=
  Equiv.ofBijective (bruhatWeylLeftFun F i) (bruhatWeylLeftFun_bijective F i)

@[simp] lemma bruhatWeylLeft_apply {n : ℕ} (i : Fin n) (s : BruhatState F n) :
    bruhatWeylLeft F i s = bruhatWeylLeftFun F i s := rfl

theorem bruhatWeylLeft_square {n : ℕ} (i : Fin n) :
    bruhatWeylLeft F i * bruhatWeylLeft F i =
      bruhatTorusLeft F n ((simple F i (-1))⁻¹) := by
  apply Equiv.ext
  exact bruhatWeylLeftFun_square F i

/-- Right W_i(-1) is obtained by inverting both coordinates of the left action. -/
def bruhatWeylRight {n : ℕ} (i : Fin n) : Equiv.Perm (BruhatState F n) :=
  bruhatInversion F n * bruhatWeylLeft F i * bruhatInversion F n

lemma bruhatWeylRight_matrix {n : ℕ} (i : Fin n) (s : BruhatState F n) :
    (bruhatWeylRight F i s).matrix = s.matrix * simpleWMatrix F i (-1) := by
  change (simpleWMatrix F i 1 * s.matrix⁻¹)⁻¹ = _
  rw [_root_.mul_inv_rev, inv_inv, simpleWMatrix_neg]

lemma bruhatWeylRight_normalizer {n : ℕ} (i : Fin n) (s : BruhatState F n) :
    (bruhatWeylRight F i s).normalizer =
      s.normalizer * (leftWeylCarry F i s.matrix⁻¹)⁻¹ := by
  change (leftWeylCarry F i s.matrix⁻¹ * s.normalizer⁻¹)⁻¹ = _
  rw [_root_.mul_inv_rev, inv_inv]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatTranslations -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The actual upper group acts by its literal matrix products. -/
def bruhatUpperLeftHom (n : ℕ) : _root_.Matrix.Bruhat.upperUnipotent F (n + 1) →*
    Equiv.Perm (BruhatState F n) where
  toFun := bruhatUpperLeft F n
  map_one' := by ext s <;> simp [bruhatUpperLeft]
  map_mul' U V := by ext s <;> simp [bruhatUpperLeft, mul_assoc]

/-- The existing torus acts by its literal products in both state coordinates. -/
def bruhatTorusLeftHom (n : ℕ) : Torus F n →* Equiv.Perm (BruhatState F n) where
  toFun := bruhatTorusLeft F n
  map_one' := by ext s <;> simp [bruhatTorusLeft]
  map_mul' h k := by ext s <;> simp [bruhatTorusLeft, mul_assoc]

lemma bruhatTorusLeft_injective (n : ℕ) : Function.Injective (bruhatTorusLeft F n) := by
  intro h k he
  apply normalizerTorus_injective F n
  have hh := congrArg (fun e : Equiv.Perm (BruhatState F n) =>
    (e (bruhatBase F n)).normalizer) he
  simpa only [bruhatTorusLeft_normalizer, bruhatBase, mul_one] using hh

/-- Literal right upper-unitriangular multiplication. -/
def bruhatUpperRight (n : ℕ) (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    Equiv.Perm (BruhatState F n) where
  toFun s := ⟨s.matrix * U, s.normalizer, by
    simpa only [Subgroup.coe_one, one_mul] using
      s.compatible.trans (bruhatGL_upper F n s.matrix 1 U).symm⟩
  invFun s := ⟨s.matrix * U⁻¹, s.normalizer, by
    simpa only [Subgroup.coe_one, one_mul] using
      s.compatible.trans (bruhatGL_upper F n s.matrix 1 U⁻¹).symm⟩
  left_inv s := by ext <;> simp
  right_inv s := by ext <;> simp

/-- Literal right torus multiplication, retaining the same central fibre. -/
def bruhatTorusRight (n : ℕ) (h : Torus F n) : Equiv.Perm (BruhatState F n) where
  toFun s := ⟨s.matrix * torusToGL F n h, s.normalizer * normalizerTorus F n h, by
    rw [map_mul, normalizerToGL_torus, s.compatible, bruhatGL_torus_right]⟩
  invFun s := ⟨s.matrix * torusToGL F n h⁻¹, s.normalizer * normalizerTorus F n h⁻¹, by
    rw [map_mul, normalizerToGL_torus, s.compatible, bruhatGL_torus_right]⟩
  left_inv s := by ext <;> simp
  right_inv s := by ext <;> simp

lemma bruhatUpperLeft_upperRight (n : ℕ)
    (U V : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    Commute (bruhatUpperLeft F n U) (bruhatUpperRight F n V) := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext <;> dsimp [bruhatUpperLeft, bruhatUpperRight]
  exact (mul_assoc _ _ _).symm

lemma bruhatTorusLeft_torusRight (n : ℕ) (h k : Torus F n) :
    Commute (bruhatTorusLeft F n h) (bruhatTorusRight F n k) := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext <;> dsimp [bruhatTorusLeft, bruhatTorusRight]
  · exact (mul_assoc _ _ _).symm
  · exact (mul_assoc _ _ _).symm

lemma bruhatUpperLeft_torusRight (n : ℕ) (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1))
    (h : Torus F n) : Commute (bruhatUpperLeft F n U) (bruhatTorusRight F n h) := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext <;> dsimp [bruhatUpperLeft, bruhatTorusRight]
  exact (mul_assoc _ _ _).symm

lemma bruhatTorusLeft_upperRight (n : ℕ) (h : Torus F n)
    (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    Commute (bruhatTorusLeft F n h) (bruhatUpperRight F n U) := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext <;> dsimp [bruhatTorusLeft, bruhatUpperRight]
  exact (mul_assoc _ _ _).symm

lemma bruhatInversion_square (n : ℕ) : bruhatInversion F n * bruhatInversion F n = 1 := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext <;> simp [bruhatInversion]

lemma bruhatInversion_torus (n : ℕ) (h : Torus F n) :
    bruhatInversion F n * bruhatTorusLeft F n h * bruhatInversion F n =
      bruhatTorusRight F n h⁻¹ := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext <;> simp [bruhatInversion, bruhatTorusLeft, bruhatTorusRight]

lemma bruhatInversion_upper (n : ℕ) (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    bruhatInversion F n * bruhatUpperLeft F n U * bruhatInversion F n =
      bruhatUpperRight F n U⁻¹ := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext <;> simp [bruhatInversion, bruhatUpperLeft, bruhatUpperRight]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatMixed -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma leftWeylCarry_upper_right {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    leftWeylCarry F i (g * U) = leftWeylCarry F i g := by
  apply leftWeylCarry_congr F i
  · simpa only [Subgroup.coe_one, one_mul] using bruhatGL_upper F n g 1 U
  · simpa only [Subgroup.coe_one, one_mul, mul_assoc] using
      bruhatGL_upper F n (simpleWMatrix F i 1 * g) 1 U

lemma leftWeylCarry_torus_right {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (h : Torus F n) :
    leftWeylCarry F i (g * torusToGL F n h) = leftWeylCarry F i g := by
  apply leftWeylCarry_eq_of F i _ _ (leftWeylCarry_mem F i g)
  rw [bruhatGL_torus_right, ← mul_assoc, leftWeylCarry_projection,
    ← mul_assoc (simpleWMatrix F i 1), bruhatGL_torus_right]

/-- Every lifted left Weyl update commutes with literal right upper multiplication. -/
theorem bruhatWeylLeft_upperRight {n : ℕ} (i : Fin n)
    (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    Commute (bruhatWeylLeft F i) (bruhatUpperRight F n U) := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext
  · change simpleWMatrix F i 1 * (s.matrix * U) = (simpleWMatrix F i 1 * s.matrix) * U
    exact (mul_assoc _ _ _).symm
  · change leftWeylCarry F i (s.matrix * U) * s.normalizer =
      leftWeylCarry F i s.matrix * s.normalizer
    rw [leftWeylCarry_upper_right]

/-- Every lifted left Weyl update commutes with literal right torus multiplication. -/
theorem bruhatWeylLeft_torusRight {n : ℕ} (i : Fin n) (h : Torus F n) :
    Commute (bruhatWeylLeft F i) (bruhatTorusRight F n h) := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext
  · change simpleWMatrix F i 1 * (s.matrix * torusToGL F n h) = _
    exact (mul_assoc _ _ _).symm
  · change leftWeylCarry F i (s.matrix * torusToGL F n h) *
      (s.normalizer * normalizerTorus F n h) = _
    rw [leftWeylCarry_torus_right, ← mul_assoc]
    rfl

/-- Literal left upper multiplication commutes with every lifted right Weyl update. -/
theorem bruhatUpperLeft_weylRight {n : ℕ} (i : Fin n)
    (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    Commute (bruhatUpperLeft F n U) (bruhatWeylRight F i) := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext
  · simp only [Equiv.Perm.mul_apply, bruhatUpperLeft_matrix, bruhatWeylRight_matrix,
      mul_assoc]
  · simp only [Equiv.Perm.mul_apply, bruhatUpperLeft_normalizer,
      bruhatWeylRight_normalizer, bruhatUpperLeft_matrix, _root_.mul_inv_rev]
    have hc := leftWeylCarry_upper_right F i s.matrix⁻¹ U⁻¹
    rw [Subgroup.coe_inv] at hc
    rw [hc]

/-- Literal left torus multiplication commutes with every lifted right Weyl update. -/
theorem bruhatTorusLeft_weylRight {n : ℕ} (i : Fin n) (h : Torus F n) :
    Commute (bruhatTorusLeft F n h) (bruhatWeylRight F i) := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext
  · simp only [Equiv.Perm.mul_apply, bruhatTorusLeft_matrix, bruhatWeylRight_matrix,
      mul_assoc]
  · simp only [Equiv.Perm.mul_apply, bruhatTorusLeft_normalizer,
      bruhatWeylRight_normalizer, bruhatTorusLeft_matrix, _root_.mul_inv_rev]
    have hc := leftWeylCarry_torus_right F i s.matrix⁻¹ h⁻¹
    rw [map_inv] at hc
    rw [hc, mul_assoc]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatRightCarry -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The retained W(-1) right carry, obtained by actual inversion. -/
def rightWeylCarry {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) : LiftedNormalizer F n :=
  (leftWeylCarry F i g⁻¹)⁻¹

lemma rightWeylCarry_projection {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    bruhatGL F n g * normalizerToGL F n (rightWeylCarry F i g) =
      bruhatGL F n (g * simpleWMatrix F i (-1)) := by
  have he := congrArg Inv.inv (leftWeylCarry_projection F i g⁻¹)
  rw [_root_.mul_inv_rev, bruhatGL_inv, inv_inv, ← bruhatGL_inv, _root_.mul_inv_rev, inv_inv,
    ← simpleWMatrix_neg F i 1] at he
  simpa only [rightWeylCarry, map_inv] using he

lemma rightWeylCarry_congr {n : ℕ} (i : Fin n)
    (g h : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (he : bruhatGL F n g = bruhatGL F n h)
    (hwe : bruhatGL F n (g * simpleWMatrix F i (-1)) =
      bruhatGL F n (h * simpleWMatrix F i (-1))) :
    rightWeylCarry F i g = rightWeylCarry F i h := by
  apply congrArg Inv.inv
  apply leftWeylCarry_congr F i
  · rw [bruhatGL_inv, bruhatGL_inv, he]
  · have he' := congrArg Inv.inv hwe
    simpa only [← bruhatGL_inv, _root_.mul_inv_rev, simpleWMatrix_neg, inv_inv] using he'

lemma bruhatWeylRight_normalizer_carry {n : ℕ} (i : Fin n) (s : BruhatState F n) :
    (bruhatWeylRight F i s).normalizer = s.normalizer * rightWeylCarry F i s.matrix :=
  bruhatWeylRight_normalizer F i s

/-- The all-state operator equation is exactly the displayed equality inside the actual N. -/
theorem bruhatWeyl_commutes_at_iff {n : ℕ} (i k : Fin n) (s : BruhatState F n) :
    bruhatWeylLeft F i (bruhatWeylRight F k s) =
        bruhatWeylRight F k (bruhatWeylLeft F i s) ↔
      leftWeylCarry F i (s.matrix * simpleWMatrix F k (-1)) * s.normalizer *
          rightWeylCarry F k s.matrix =
        leftWeylCarry F i s.matrix * s.normalizer *
          rightWeylCarry F k (simpleWMatrix F i 1 * s.matrix) := by
  have hn : (bruhatWeylLeft F i (bruhatWeylRight F k s)).normalizer =
      leftWeylCarry F i (s.matrix * simpleWMatrix F k (-1)) * s.normalizer *
        rightWeylCarry F k s.matrix := by
    change leftWeylCarry F i (bruhatWeylRight F k s).matrix *
      (bruhatWeylRight F k s).normalizer = _
    rw [bruhatWeylRight_matrix, bruhatWeylRight_normalizer_carry, mul_assoc]
  have hn' : (bruhatWeylRight F k (bruhatWeylLeft F i s)).normalizer =
      leftWeylCarry F i s.matrix * s.normalizer *
        rightWeylCarry F k (simpleWMatrix F i 1 * s.matrix) := by
    rw [bruhatWeylRight_normalizer_carry]
    rfl
  constructor
  · intro he
    rw [← hn, ← hn', he]
  · intro he
    apply BruhatState.ext
    · rw [bruhatWeylRight_matrix]
      change simpleWMatrix F i 1 * (bruhatWeylRight F k s).matrix = _
      rw [bruhatWeylRight_matrix]
      exact (mul_assoc _ _ _).symm
    · rw [hn, hn', he]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatReduction -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- Every lifted Weyl/Weyl square reduces to the canonical matrix quartet with the SAME N lift. -/
theorem bruhatWeyl_canonical_reduction {n : ℕ} (i k : Fin n) (s : BruhatState F n) :
    ∃ (u v : F) (t : BruhatState F n),
      t.matrix = _root_.Matrix.Bruhat.simpleBruhatRepresentative F n i k
        (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix) u v ∧
      t.normalizer = s.normalizer ∧
      (bruhatWeylLeft F i (bruhatWeylRight F k s) =
          bruhatWeylRight F k (bruhatWeylLeft F i s) ↔
        bruhatWeylLeft F i (bruhatWeylRight F k t) =
          bruhatWeylRight F k (bruhatWeylLeft F i t)) := by
  obtain ⟨u, v, U, V, _, _, _, h0, hL, hR, hLR⟩ :=
    _root_.Matrix.Bruhat.finite_bruhat_four_monomial_reduction F n i k s.matrix
  let c := _root_.Matrix.Bruhat.simpleBruhatRepresentative F n i k
    (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix) u v
  have h0' : bruhatGL F n s.matrix = bruhatGL F n c :=
    congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1)) h0
  have hL' : bruhatGL F n (simpleWMatrix F i 1 * s.matrix) =
      bruhatGL F n (simpleWMatrix F i 1 * c) := by
    have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1)) hL
    simpa only [bruhatGL, rootWMonomial_toGL] using he
  have hR' : bruhatGL F n (s.matrix * simpleWMatrix F k (-1)) =
      bruhatGL F n (c * simpleWMatrix F k (-1)) := by
    have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1)) hR
    simpa only [bruhatGL, rootWMonomial_toGL] using he
  have hLR' : bruhatGL F n (simpleWMatrix F i 1 * s.matrix * simpleWMatrix F k (-1)) =
      bruhatGL F n (simpleWMatrix F i 1 * c * simpleWMatrix F k (-1)) := by
    have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1)) hLR
    simpa only [bruhatGL, rootWMonomial_toGL] using he
  let t : BruhatState F n := ⟨c, s.normalizer, s.compatible.trans h0'⟩
  refine ⟨u, v, t, rfl, rfl, ?_⟩
  have hcL := leftWeylCarry_congr F i s.matrix c h0' hL'
  have hcR := rightWeylCarry_congr F k s.matrix c h0' hR'
  have hcLR := leftWeylCarry_congr F i (s.matrix * simpleWMatrix F k (-1))
    (c * simpleWMatrix F k (-1)) hR' (by simpa only [mul_assoc] using hLR')
  have hcRL := rightWeylCarry_congr F k (simpleWMatrix F i 1 * s.matrix)
    (simpleWMatrix F i 1 * c) hL' hLR'
  rw [bruhatWeyl_commutes_at_iff, bruhatWeyl_commutes_at_iff]
  change _ ↔ leftWeylCarry F i (c * simpleWMatrix F k (-1)) * s.normalizer *
      rightWeylCarry F k c = leftWeylCarry F i c * s.normalizer *
        rightWeylCarry F k (simpleWMatrix F i 1 * c)
  rw [hcL, hcR, hcLR, hcRL]

end StableSteinberg.RootCoordinate

end

end
