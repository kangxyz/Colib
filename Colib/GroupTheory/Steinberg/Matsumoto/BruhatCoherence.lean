/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matsumoto.BruhatActions
public import Colib.LinearAlgebra.Matrix.Bruhat.Distinct
public import Colib.LinearAlgebra.Matrix.Bruhat.Coordinates
public import Colib.LinearAlgebra.Matrix.Bruhat.Opposite
public import Colib.GroupTheory.Steinberg.Matsumoto.MatrixBasics
public import Colib.LinearAlgebra.Matrix.Bruhat.Decomposition
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Colib.LinearAlgebra.Matrix.Bruhat.RootUpdate
public import Colib.GroupTheory.Steinberg.Matsumoto.LiftedWeyl
public import Colib.GroupTheory.Steinberg.Matsumoto.Normalizer
public import Colib.GroupTheory.Steinberg.Matsumoto.NormalizerMatrix
public import Colib.GroupTheory.Steinberg.Matsumoto.Torus
public import Colib.GroupTheory.Steinberg.Matsumoto.Weyl

/-!
# BruhatCoherence

Adapted from Quillen Matsumoto/BruhatCoherence.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native Stacks
homogeneous Milnor group and native matrix units throughout.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## RootCoordinateBruhatDistinct -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma rightWeylCarry_eq_of_projection {n : ℕ} (i : Fin n)
    (g h : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (he : normalizerToGL F n (rightWeylCarry F i g) =
      normalizerToGL F n (rightWeylCarry F i h)) : rightWeylCarry F i g = rightWeylCarry F i h := by
  apply congrArg Inv.inv
  apply leftWeylCell_injective F i (leftWeylCarry_mem F i g⁻¹) (leftWeylCarry_mem F i h⁻¹)
  simpa only [rightWeylCarry, map_inv, inv_inv] using congrArg Inv.inv he

/-- An actual matrix ratio square identifies each carry separately in its faithful two-cell set. -/
theorem bruhatWeyl_commutes_of_ratio_square {n : ℕ} (i k : Fin n) (s : BruhatState F n)
    (hs : bruhatGL F n (simpleWMatrix F i 1 * s.matrix * simpleWMatrix F k (-1)) =
      bruhatGL F n (simpleWMatrix F i 1 * s.matrix) * (bruhatGL F n s.matrix)⁻¹ *
        bruhatGL F n (s.matrix * simpleWMatrix F k (-1))) :
    bruhatWeylLeft F i (bruhatWeylRight F k s) =
      bruhatWeylRight F k (bruhatWeylLeft F i s) := by
  have hL : leftWeylCarry F i (s.matrix * simpleWMatrix F k (-1)) =
      leftWeylCarry F i s.matrix := by
    apply leftWeylCell_injective F i (leftWeylCarry_mem F i _)
      (leftWeylCarry_mem F i _)
    apply mul_right_cancel (b := bruhatGL F n (s.matrix * simpleWMatrix F k (-1)))
    rw [leftWeylCarry_projection, ← mul_assoc (simpleWMatrix F i 1), hs,
      ← leftWeylCarry_projection F i s.matrix]
    simp only [mul_inv_cancel_right]
  have hR : rightWeylCarry F k (simpleWMatrix F i 1 * s.matrix) =
      rightWeylCarry F k s.matrix := by
    apply rightWeylCarry_eq_of_projection
    apply mul_left_cancel (a := bruhatGL F n (simpleWMatrix F i 1 * s.matrix))
    rw [rightWeylCarry_projection, hs, ← rightWeylCarry_projection F k s.matrix]
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [bruhatWeyl_commutes_at_iff, hL, hR]

/-- Distinct transported roots satisfy the lifted square, including shared endpoints. -/
theorem bruhatWeyl_canonical_distinct {n : ℕ} (i k : Fin n) (s : BruhatState F n)
    (m : _root_.Matrix.Bruhat.MonomialGroup F (n + 1)) (u v : F)
    (hs : s.matrix = _root_.Matrix.Bruhat.simpleBruhatRepresentative F n i k m u v)
    (hpos : ¬(m.right k.castSucc = i.castSucc ∧ m.right k.succ = i.succ))
    (hneg : ¬(m.right k.castSucc = i.succ ∧ m.right k.succ = i.castSucc)) :
    bruhatWeylLeft F i (bruhatWeylRight F k s) =
      bruhatWeylRight F k (bruhatWeylLeft F i s) := by
  apply bruhatWeyl_commutes_of_ratio_square
  rw [hs]
  have he := congrArg (_root_.Matrix.Bruhat.monomialToGL F (n + 1))
    (_root_.Matrix.Bruhat.distinct_bruhat_ratio_square F n i k m hpos hneg u v)
  simpa only [bruhatGL, rootWMonomial_toGL, map_mul, map_inv] using he

/-- The distinct-root lifted coherence holds for every original state, not only canonical ones. -/
theorem bruhatWeyl_distinct {n : ℕ} (i k : Fin n) (s : BruhatState F n)
    (hpos : ¬((_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.castSucc = i.castSucc
      ∧
      (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.succ = i.succ))
    (hneg : ¬((_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.castSucc = i.succ ∧
      (_root_.Matrix.Bruhat.bruhatMonomial F (n + 1) s.matrix).right k.succ = i.castSucc)) :
    bruhatWeylLeft F i (bruhatWeylRight F k s) =
      bruhatWeylRight F k (bruhatWeylLeft F i s) := by
  obtain ⟨u, v, t, ht, _, he⟩ := bruhatWeyl_canonical_reduction F i k s
  exact he.mpr (bruhatWeyl_canonical_distinct F i k t _ u v ht hpos hneg)

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatRightGroup -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The concrete group generated by the three actual right operator families. -/
def BruhatRightGroup (n : ℕ) : Subgroup (Equiv.Perm (BruhatState F n)) :=
  Subgroup.closure (Set.range (bruhatUpperRight F n) ∪ Set.range (bruhatTorusRight F n) ∪
    Set.range (@bruhatWeylRight F _ n))

/-- Actual state permutations inducing right multiplication by their basepoint matrix. -/
def bruhatRightCovariant (n : ℕ) : Subgroup (Equiv.Perm (BruhatState F n)) where
  carrier := {e | ∀ s, (e s).matrix = s.matrix * (e (bruhatBase F n)).matrix}
  one_mem' := by intro s; simp [bruhatBase]
  mul_mem' := by
    intro e f he hf s
    change (e (f s)).matrix = s.matrix * (e (f (bruhatBase F n))).matrix
    rw [he (f s), hf s, he (f (bruhatBase F n))]
    exact mul_assoc _ _ _
  inv_mem' := by
    intro e he
    have hinv (s : BruhatState F n) :
        (e⁻¹ s).matrix = s.matrix * (e (bruhatBase F n)).matrix⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq).mpr
      simpa using (he (e⁻¹ s)).symm
    intro s
    rw [hinv, hinv]
    change _ = s.matrix * (1 * (e (bruhatBase F n)).matrix⁻¹)
    rw [one_mul]

lemma bruhatRightGroup_le_covariant (n : ℕ) :
    BruhatRightGroup F n ≤ bruhatRightCovariant F n := by
  apply (Subgroup.closure_le _).mpr
  rintro e ((⟨U, rfl⟩ | ⟨h, rfl⟩) | ⟨i, rfl⟩) s
  · change s.matrix * U = s.matrix * (1 * U)
    rw [one_mul]
  · change s.matrix * torusToGL F n h = s.matrix * (1 * torusToGL F n h)
    rw [one_mul]
  · simp only [bruhatWeylRight_matrix, bruhatBase, one_mul]

lemma bruhatRightGroup_upper_mem (n : ℕ) (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    bruhatUpperRight F n U ∈ BruhatRightGroup F n :=
  Subgroup.subset_closure (Or.inl (Or.inl ⟨U, rfl⟩))

lemma bruhatRightGroup_torus_mem (n : ℕ) (h : Torus F n) :
    bruhatTorusRight F n h ∈ BruhatRightGroup F n :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨h, rfl⟩))

lemma bruhatRightGroup_weyl_mem {n : ℕ} (i : Fin n) :
    bruhatWeylRight F i ∈ BruhatRightGroup F n :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

/-- Matrices realized by the actual right action, with its reversed multiplication accounted for. -/
def bruhatRightMatrixRange (n : ℕ) : Subgroup (Matrix.GeneralLinearGroup (Fin (n + 1)) F) where
  carrier := {A | ∃ e ∈ BruhatRightGroup F n, (e (bruhatBase F n)).matrix = A}
  one_mem' := ⟨1, Subgroup.one_mem _, rfl⟩
  mul_mem' := by
    rintro A B ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩
    refine ⟨f * e, Subgroup.mul_mem _ hf he, ?_⟩
    exact bruhatRightGroup_le_covariant F n hf (e (bruhatBase F n))
  inv_mem' := by
    rintro A ⟨e, he, rfl⟩
    refine ⟨e⁻¹, Subgroup.inv_mem _ he, ?_⟩
    have hh := bruhatRightGroup_le_covariant F n he (e⁻¹ (bruhatBase F n))
    have hh' : (e⁻¹ (bruhatBase F n)).matrix * (e (bruhatBase F n)).matrix = 1 := by
      simpa [bruhatBase] using hh.symm
    exact eq_inv_of_mul_eq_one_left hh'

lemma bruhatRightMatrixRange_upper (n : ℕ) (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) ∈ bruhatRightMatrixRange F n :=
  ⟨bruhatUpperRight F n U, bruhatRightGroup_upper_mem F n U, one_mul _⟩

lemma bruhatRightMatrixRange_torus (n : ℕ) (h : Torus F n) :
    torusToGL F n h ∈ bruhatRightMatrixRange F n :=
  ⟨bruhatTorusRight F n h, bruhatRightGroup_torus_mem F n h, one_mul _⟩

lemma bruhatRightMatrixRange_weyl {n : ℕ} (i : Fin n) :
    simpleWMatrix F i (-1) ∈ bruhatRightMatrixRange F n := by
  refine ⟨bruhatWeylRight F i, bruhatRightGroup_weyl_mem F i, ?_⟩
  rw [bruhatWeylRight_matrix]
  exact one_mul _

/-- Every original normalizer matrix is realized by the concrete right group. -/
lemma bruhatRightMatrixRange_normalizer (n : ℕ) (ν : LiftedNormalizer F n) :
    normalizerToGL F n ν ∈ bruhatRightMatrixRange F n := by
  let S := (bruhatRightMatrixRange F n).comap (normalizerToGL F n)
  have hS : S = ⊤ := by
    apply normalizer_generated F n
    · intro h
      change normalizerToGL F n (normalizerTorus F n h) ∈ bruhatRightMatrixRange F n
      rw [normalizerToGL_torus]
      exact bruhatRightMatrixRange_torus F n h
    · intro i
      change normalizerToGL F n (normalizerLambda F i) ∈ bruhatRightMatrixRange F n
      rw [normalizerToGL_lambda]
      exact bruhatRightMatrixRange_weyl F i
  have hν : ν ∈ S := by rw [hS]; trivial
  exact hν

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatTransitive -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- Bruhat factorization puts every state matrix in the actual right-action range. -/
lemma bruhatRightMatrixRange_state (n : ℕ) (s : BruhatState F n) :
    s.matrix ∈ bruhatRightMatrixRange F n := by
  obtain ⟨U, V, hg⟩ := _root_.Matrix.Bruhat.bruhatMonomial_factorization F (n + 1) s.matrix
  change s.matrix = (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) *
    bruhatGL F n s.matrix * V at hg
  rw [hg, ← s.compatible]
  exact (bruhatRightMatrixRange F n).mul_mem
    ((bruhatRightMatrixRange F n).mul_mem (bruhatRightMatrixRange_upper F n U)
      (bruhatRightMatrixRange_normalizer F n s.normalizer))
    (bruhatRightMatrixRange_upper F n V)

/-- The concrete right group is transitive on the entire lifted Bruhat set. -/
theorem bruhatRightGroup_transitive (n : ℕ) (s : BruhatState F n) :
    ∃ e ∈ BruhatRightGroup F n, e (bruhatBase F n) = s := by
  obtain ⟨e, he, hm⟩ := bruhatRightMatrixRange_state F n s
  let t := e (bruhatBase F n)
  have hk : t.normalizer⁻¹ * s.normalizer ∈ (normalizerToGL F n).ker := by
    change normalizerToGL F n (t.normalizer⁻¹ * s.normalizer) = 1
    rw [map_mul, map_inv, t.compatible, s.compatible]
    change (bruhatGL F n (e (bruhatBase F n)).matrix)⁻¹ * bruhatGL F n s.matrix = 1
    rw [hm, inv_mul_cancel]
  rw [normalizerToGL_ker] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨bruhatTorusRight F n (coefficient F n a) * e,
    (BruhatRightGroup F n).mul_mem (bruhatRightGroup_torus_mem F n _) he, ?_⟩
  apply BruhatState.ext
  · change t.matrix * torusToGL F n (coefficient F n a) = s.matrix
    have hd : torusToGL F n (coefficient F n a) = 1 := by
      simpa only [normalizerCoefficient, MonoidHom.comp_apply, normalizerToGL_torus] using
        normalizerToGL_coefficient F n a
    rw [hd, mul_one]
    exact hm
  · change t.normalizer * normalizerCoefficient F n a = s.normalizer
    rw [ha, mul_inv_cancel_left]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateBruhatCovariance -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- Literal diagonal conjugation inside the actual upper unitriangular group. -/
def torusConjugateUpper (n : ℕ) (h : Torus F n)
    (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) : _root_.Matrix.Bruhat.upperUnipotent F (n +
      1) :=
  ⟨torusToGL F n h * U * (torusToGL F n h)⁻¹, by
    rw [torusToGL_eq_diagonalGL]
    exact _root_.Matrix.Bruhat.upperUnipotent_diagonal_conjugate F (n + 1) _ U⟩

/-- Actual torus/upper covariance of the lifted operators, with no root-law premise. -/
theorem bruhatTorus_upper_conjugate (n : ℕ) (h : Torus F n)
    (U : _root_.Matrix.Bruhat.upperUnipotent F (n + 1)) :
    bruhatTorusLeft F n h * bruhatUpperLeft F n U * (bruhatTorusLeft F n h)⁻¹ =
      bruhatUpperLeft F n (torusConjugateUpper F n h U) := by
  apply Equiv.ext
  intro s
  apply BruhatState.ext
  · change torusToGL F n h * (U * (torusToGL F n h⁻¹ * s.matrix)) =
      (torusToGL F n h * U * (torusToGL F n h)⁻¹) * s.matrix
    simp only [map_inv, mul_assoc]
  · change normalizerTorus F n h * (normalizerTorus F n h⁻¹ * s.normalizer) = s.normalizer
    simp only [map_inv, mul_inv_cancel_left]

/-- Left and right translation by each unchanged Milnor coefficient coincide on every state. -/
theorem bruhatCoefficient_left_eq_right (n : ℕ) (a : Multiplicative (MilnorKTheory F 2)) :
    bruhatTorusLeft F n (coefficient F n a) =
      bruhatTorusRight F n (coefficient F n a) := by
  have hd : torusToGL F n (coefficient F n a) = 1 := by
    simpa only [normalizerCoefficient, MonoidHom.comp_apply, normalizerToGL_torus] using
      normalizerToGL_coefficient F n a
  apply Equiv.ext
  intro s
  apply BruhatState.ext
  · change torusToGL F n (coefficient F n a) * s.matrix =
      s.matrix * torusToGL F n (coefficient F n a)
    simp only [hd, one_mul, mul_one]
  · exact (Subgroup.mem_center_iff.mp
      (normalizerCoefficient_le_center F n ⟨a, rfl⟩) s.normalizer).symm

/-- The unchanged coefficient acts faithfully on the lifted state set. -/
theorem bruhatCoefficient_injective (n : ℕ) :
    Function.Injective (fun a : Multiplicative (MilnorKTheory F 2) =>
      bruhatTorusLeft F n (coefficient F n a)) :=
  (bruhatTorusLeft_injective F n).comp (coefficient_injective F n)

end StableSteinberg.RootCoordinate

end

end
