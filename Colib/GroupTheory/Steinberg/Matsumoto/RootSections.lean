/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Mathlib.GroupTheory.Subgroup.Center
public import Colib.GroupTheory.Steinberg.Matsumoto.NormalizerMatrix
public import Colib.GroupTheory.Steinberg.Matsumoto.FiniteRootLifting
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.SignedSection
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Colib.GroupTheory.Steinberg.Matsumoto.Torus
public import Colib.GroupTheory.Steinberg.Matsumoto.Weyl

/-!
# RootSections

Adapted from `Quillen/Algebra/Group/StableSteinberg/Matsumoto/RootSections.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## CentralConjugation -/

section

universe u v
namespace StableSteinberg.RootSectionProducer

variable {E : Type u} {G : Type v} [Group E] [Group G]

/-- Across a central kernel, conjugation depends only on the projected conjugator. -/
theorem conjugate_eq_of_projection_eq (p : E →* G) (hc : p.ker ≤ Subgroup.center E)
    {x y : E} (hxy : p x = p y) (z : E) : x * z * x⁻¹ = y * z * y⁻¹ := by
  let c := y⁻¹ * x
  have hz : c ∈ Subgroup.center E := hc (by
    change p (y⁻¹ * x) = 1
    rw [map_mul, map_inv, hxy, inv_mul_cancel])
  have hcomm : Commute c z := (Subgroup.mem_center_iff.mp hz z).symm
  have hfix : c * z * c⁻¹ = z := by
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hx : x = y * c := by simp [c]
  calc
    x * z * x⁻¹ = y * (c * z * c⁻¹) * y⁻¹ := by rw [hx]; simp [mul_assoc]
    _ = y * z * y⁻¹ := by rw [hfix]

end StableSteinberg.RootSectionProducer

end

/-! ## RootMatrixTransport -/

section

noncomputable section
universe u
namespace StableSteinberg.RootSectionProducer
open StableSteinberg
variable (F : Type u) [Field F]

/-- An explicit permutation carrying the first ordered pair to the second. -/
def pairPermutation {m : ℕ} (a b i j : Fin m) : Equiv.Perm (Fin m) :=
  Equiv.swap ((Equiv.swap a i) b) j * Equiv.swap a i

lemma pairPermutation_left {m : ℕ} (a b i j : Fin m) (hab : a ≠ b) (hij : i ≠ j) :
    pairPermutation a b i j a = i := by
  let ρ := Equiv.swap a i
  have ha : ρ a = i := Equiv.swap_apply_left a i
  have hb : ρ b ≠ i := by
    intro h
    exact hab (ρ.injective (ha.trans h.symm))
  change Equiv.swap (ρ b) j (ρ a) = i
  rw [ha]
  simp [Equiv.swap_apply_def, hb.symm, hij]

lemma pairPermutation_right {m : ℕ} (a b i j : Fin m) :
    pairPermutation a b i j b = j := Equiv.swap_apply_left _ _

@[simp] lemma pairPermutation_self {m : ℕ} (a b : Fin m) : pairPermutation a b a b = 1 := by
  apply Equiv.ext
  intro x
  simp [pairPermutation]

/-- Literal column coefficients of the accepted signed matrix section. -/
def signedColumns {m : ℕ} (σ : Equiv.Perm (Fin m)) : Fin m → Fˣ :=
  fun j => (-1 : Fˣ) ^ _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount σ j

lemma matrix_mul_elementary_entry {m : ℕ} (g : Matrix.GeneralLinearGroup (Fin m) F)
    (i j : Fin m) (hij : i ≠ j) (a : F) (r s : Fin m) :
    (g * _root_.Matrix.GeneralLinearGroup.elementary i j hij a).val r s =
      g.val r s + if s = j then g.val r i * a else 0 := by
  change (g.val * (1 + Matrix.single i j a)) r s = _
  rw [mul_add, mul_one, Matrix.add_apply]
  by_cases hs : s = j
  · subst s
    simp
  · rw [Matrix.mul_single_apply_of_ne a i j r s hs, ite_eq_right hs, add_zero]

/-- Actual column-monomial conjugation, with the literal unit weight ratio. -/
theorem columnUnit_conjugate_root {m : ℕ} (σ : Equiv.Perm (Fin m)) (d : Fin m → Fˣ)
    (a b : Fin m) (hab : a ≠ b) (z : F) :
    _root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit F σ d *
      _root_.Matrix.GeneralLinearGroup.elementary a b hab z *
        (_root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit F σ d)⁻¹ =
      _root_.Matrix.GeneralLinearGroup.elementary (σ a) (σ b) (σ.injective.ne hab)
        (((d a * (d b)⁻¹ : Fˣ) : F) * z) := by
  have hmove : _root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit F σ d *
    _root_.Matrix.GeneralLinearGroup.elementary a b hab z =
      _root_.Matrix.GeneralLinearGroup.elementary (σ a) (σ b) (σ.injective.ne hab)
        (((d a * (d b)⁻¹ : Fˣ) : F) * z) * _root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit
          F σ d := by
    apply Units.ext
    ext r s
    rw [matrix_mul_elementary_entry,
      _root_.Matrix.GeneralLinearGroup.SignedSection.elementary_left_mul_entry]
    simp only [_root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit_entry]
    by_cases hr : r = σ a
    · subst r
      by_cases hs : s = b
      · subst s
        simp [σ.injective.ne hab, Units.val_inv_eq_inv_val]
        all_goals field_simp
      · have hbs : b ≠ s := Ne.symm hs
        simp [hs, hbs, σ.injective.eq_iff]
    · simp [hr]
  have hh := congrArg (fun x : Matrix.GeneralLinearGroup (Fin m) F =>
    x * (_root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit F σ d)⁻¹) hmove
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh

/-- Pulling back a diagonal through a weighted permutation only permutes its entries. -/
theorem columnUnit_conjugate_diagonal {m : ℕ} (σ : Equiv.Perm (Fin m))
    (d w : Fin m → Fˣ) :
    (_root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit F σ d)⁻¹ *
      FiniteRootLifting.diagonalUnit F w *
        _root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit F σ d =
      FiniteRootLifting.diagonalUnit F (fun r => w (σ r)) := by
  have he : FiniteRootLifting.diagonalUnit F w *
    _root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit F σ d =
      _root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit F σ d *
        FiniteRootLifting.diagonalUnit F (fun r => w (σ r)) := by
    apply Units.ext
    change Matrix.diagonal (fun r => (w r : F)) *
      (_root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit F σ d).val =
      (_root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit F σ d).val * Matrix.diagonal (fun r
        => (w (σ r) : F))
    ext r s
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [_root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit_entry]
    by_cases hr : r = σ s <;> simp [hr, mul_comm]
  have hh := congrArg (fun x : Matrix.GeneralLinearGroup (Fin m) F =>
    (_root_.Matrix.GeneralLinearGroup.SignedSection.columnUnit F σ d)⁻¹ * x) he
  simpa only [mul_assoc, inv_mul_cancel_left] using hh

lemma permuted_weights_prod {m : ℕ} (σ : Equiv.Perm (Fin m)) (w : Fin m → Fˣ)
    (hw : ∏ r, w r = 1) : ∏ r, w (σ r) = 1 := by
  rw [Equiv.prod_comp]
  exact hw

/-- The accepted signed section is a genuine determinant-one finite matrix. -/
lemma signedSection_det_value (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    Matrix.det (_root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F σ).val = 1 := by
  exact congrArg Units.val (RootCoordinate.signedSection_det F n σ)

/-- An explicit M1 torus element covering a literal product-one diagonal tuple. -/
def diagonalTorusLift {n : ℕ} (w : Fin (n + 1) → Fˣ) : RootCoordinate.Torus F n :=
  RootCoordinate.torusLift F n (RootCoordinate.corootsOfDiagonal F w)

lemma diagonalTorusLift_coordinates {n : ℕ} (w : Fin (n + 1) → Fˣ) (hw : ∏ r, w r = 1) :
    RootCoordinate.diagonalCoordinates F (diagonalTorusLift F w).diagonal = w :=
  RootCoordinate.diagonalCoordinates_corootsOfDiagonal F w hw

lemma torusToGL_diagonalTorusLift {n : ℕ} (w : Fin (n + 1) → Fˣ) (hw : ∏ r, w r = 1) :
    RootCoordinate.torusToGL F n (diagonalTorusLift F w) = FiniteRootLifting.diagonalUnit F w := by
  apply Units.ext
  change Matrix.diagonal (fun r =>
    (RootCoordinate.diagonalCoordinates F (diagonalTorusLift F w).diagonal r : F)) = _
  rw [diagonalTorusLift_coordinates F w hw]
  rfl

lemma torusToGL_eq_diagonalUnit {n : ℕ} (t : RootCoordinate.Torus F n) :
    RootCoordinate.torusToGL F n t =
      FiniteRootLifting.diagonalUnit F (RootCoordinate.diagonalCoordinates F t.diagonal) := by
  apply Units.ext
  rfl

end StableSteinberg.RootSectionProducer

end

end

/-! ## TransportedRootSections -/

section

noncomputable section
universe u v
namespace StableSteinberg.RootSectionProducer
open StableSteinberg
variable (F : Type u) [Field F]
variable {E : Type v} [Group E] {n : ℕ}

/-- The primitive projection covers each actual determinant-one matrix. -/
def DetOneOnto (p : E →* Matrix.GeneralLinearGroup (Fin (n + 1)) F) : Prop :=
  ∀ g : Matrix.GeneralLinearGroup (Fin (n + 1)) F, Matrix.det g.val = 1 → ∃ e, p e = g

/-- The accepted actual determinant-one signed section of a pair-transport permutation. -/
def transportMatrix (a b i j : Fin (n + 1)) : Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  _root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F (pairPermutation a b i j)

/-- The literal coefficient gained by transporting the one base root. -/
def transportWeight (a b i j : Fin (n + 1)) : Fˣ :=
  signedColumns F (pairPermutation a b i j) a *
    (signedColumns F (pairPermutation a b i j) b)⁻¹

/-- Choose only a lift of an actual determinant-one signed monomial matrix. -/
def transportLift (p : E →* Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (honto : DetOneOnto F p) (a b i j : Fin (n + 1)) : E :=
  Classical.choose (honto (transportMatrix F a b i j)
    (signedSection_det_value F n (pairPermutation a b i j)))

lemma transportLift_projection (p : E →* Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (honto : DetOneOnto F p) (a b i j : Fin (n + 1)) :
    p (transportLift F p honto a b i j) = transportMatrix F a b i j :=
  Classical.choose_spec (honto (transportMatrix F a b i j)
    (signedSection_det_value F n (pairPermutation a b i j)))

/-- Conjugation and field rescaling preserve the actual additive-section homomorphism. -/
def conjugateAdditiveSection (U : Multiplicative F →* E) (e : E) (c : F) :
    Multiplicative F →* E where
  toFun z := e * U (Multiplicative.ofAdd (c * z.toAdd)) * e⁻¹
  map_one' := by
    change e * U (Multiplicative.ofAdd (c * 0)) * e⁻¹ = 1
    simp
  map_mul' z w := by
    change e * U (Multiplicative.ofAdd (c * (z.toAdd + w.toAdd))) * e⁻¹ =
      (e * U (Multiplicative.ofAdd (c * z.toAdd)) * e⁻¹) *
        (e * U (Multiplicative.ofAdd (c * w.toAdd)) * e⁻¹)
    rw [mul_add]
    change e * U (Multiplicative.ofAdd (c * z.toAdd) *
      Multiplicative.ofAdd (c * w.toAdd)) * e⁻¹ = _
    rw [map_mul]
    simp [mul_assoc]

/-- Every root section is constructed from the one base section, with inverse weight. -/
def rootSections (p : E →* Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (honto : DetOneOnto F p) (a b : Fin (n + 1)) (U : Multiplicative F →* E) :
    (i j : Fin (n + 1)) → i ≠ j → Multiplicative F →* E :=
  fun i j _ => conjugateAdditiveSection F U (transportLift F p honto a b i j)
    (((transportWeight F a b i j)⁻¹ : Fˣ) : F)

lemma rootSections_apply (p : E →* Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (honto : DetOneOnto F p) (a b : Fin (n + 1)) (U : Multiplicative F →* E)
    (i j : Fin (n + 1)) (hij : i ≠ j) (z : F) :
    FiniteRootLifting.root (rootSections F p honto a b U) i j hij z =
      transportLift F p honto a b i j *
        U (Multiplicative.ofAdd ((((transportWeight F a b i j)⁻¹ : Fˣ) : F) * z)) *
        (transportLift F p honto a b i j)⁻¹ := rfl

/-- The constructed additive sections project coefficientwise to the literal original roots. -/
theorem rootSections_projection (p : E →* Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (honto : DetOneOnto F p) (a b : Fin (n + 1)) (hab : a ≠ b)
    (U : Multiplicative F →* E)
    (hU : ∀ z : F, p (U (Multiplicative.ofAdd z)) =
      _root_.Matrix.GeneralLinearGroup.elementary a b hab z)
    (i j : Fin (n + 1)) (hij : i ≠ j) (z : F) :
    p (FiniteRootLifting.root (rootSections F p honto a b U) i j hij z) =
      _root_.Matrix.GeneralLinearGroup.elementary i j hij z := by
  let σ := pairPermutation a b i j
  let c := transportWeight F a b i j
  let M := transportMatrix F a b i j
  have ha : σ a = i := pairPermutation_left a b i j hab hij
  have hb : σ b = j := pairPermutation_right a b i j
  have hs : (c : F) * (((c⁻¹ : Fˣ) : F) * z) = z := by simp
  have hm := columnUnit_conjugate_root F σ (signedColumns F σ) a b hab
    (((c⁻¹ : Fˣ) : F) * z)
  change M * _root_.Matrix.GeneralLinearGroup.elementary a b hab (((c⁻¹ : Fˣ) : F) * z) * M⁻¹ =
    _root_.Matrix.GeneralLinearGroup.elementary (σ a) (σ b) (σ.injective.ne hab)
      ((c : F) * (((c⁻¹ : Fˣ) : F) * z)) at hm
  have hm' : M * _root_.Matrix.GeneralLinearGroup.elementary a b hab (((c⁻¹ : Fˣ) : F) * z) * M⁻¹ =
      _root_.Matrix.GeneralLinearGroup.elementary i j hij z := by
    simpa only [ha, hb, hs] using hm
  rw [rootSections_apply, map_mul, map_mul, map_inv, transportLift_projection, hU]
  exact hm'

/-- The given base section itself is retained, rather than merely another projected lift. -/
theorem rootSections_base (p : E →* Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hc : p.ker ≤ Subgroup.center E) (honto : DetOneOnto F p)
    (a b : Fin (n + 1)) (hab : a ≠ b) (U : Multiplicative F →* E) (z : F) :
    FiniteRootLifting.root (rootSections F p honto a b U) a b hab z =
      U (Multiplicative.ofAdd z) := by
  have hw : transportWeight F a b a b = 1 := by simp [transportWeight, signedColumns]
  have hx : p (transportLift F p honto a b a b) = p 1 := by
    rw [transportLift_projection]
    simp [transportMatrix]
  have he := conjugate_eq_of_projection_eq p hc hx (U (Multiplicative.ofAdd z))
  rw [rootSections_apply, hw]
  simpa only [inv_one, Units.val_one, one_mul, mul_one] using he

end StableSteinberg.RootSectionProducer

end

end

/-! ## RootSectionCovariance -/

section

noncomputable section
universe u v
namespace StableSteinberg.RootSectionProducer
open StableSteinberg
variable (F : Type u) [Field F]
variable {E : Type v} [Group E] {n : ℕ}

/-- The sole covariance primitive concerns only the one supplied additive root section. -/
def BaseDiagonalCovariance (τ : RootCoordinate.Torus F n →* E)
    (a b : Fin (n + 1)) (U : Multiplicative F →* E) : Prop :=
  ∀ (t : RootCoordinate.Torus F n) (z : F),
    τ t * U (Multiplicative.ofAdd z) * (τ t)⁻¹ =
      U (Multiplicative.ofAdd
        (((RootCoordinate.diagonalCoordinates F t.diagonal a *
          (RootCoordinate.diagonalCoordinates F t.diagonal b)⁻¹ : Fˣ) : F) * z))

/-- Covariance for every constructed root, proved from the one base-root covariance. -/
theorem rootSections_tau_covariance
    (p : E →* Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hc : p.ker ≤ Subgroup.center E) (honto : DetOneOnto F p)
    (a b : Fin (n + 1)) (hab : a ≠ b)
    (τ : RootCoordinate.Torus F n →* E) (U : Multiplicative F →* E)
    (hτ : ∀ t, p (τ t) = RootCoordinate.torusToGL F n t)
    (hbase : BaseDiagonalCovariance F τ a b U)
    (t : RootCoordinate.Torus F n) (i j : Fin (n + 1)) (hij : i ≠ j) (z : F) :
    τ t * FiniteRootLifting.root (rootSections F p honto a b U) i j hij z * (τ t)⁻¹ =
      FiniteRootLifting.root (rootSections F p honto a b U) i j hij
        (((RootCoordinate.diagonalCoordinates F t.diagonal i *
          (RootCoordinate.diagonalCoordinates F t.diagonal j)⁻¹ : Fˣ) : F) * z) := by
  let σ := pairPermutation a b i j
  let x := transportLift F p honto a b i j
  let c := transportWeight F a b i j
  let w := RootCoordinate.diagonalCoordinates F t.diagonal
  let w' := fun r => w (σ r)
  let t' := diagonalTorusLift F w'
  let q := x⁻¹ * τ t * x
  let δ : Fˣ := w i * (w j)⁻¹
  let z₀ : F := ((c⁻¹ : Fˣ) : F) * z
  have ha : σ a = i := pairPermutation_left a b i j hab hij
  have hb : σ b = j := pairPermutation_right a b i j
  have hw' : ∏ r, w' r = 1 :=
    permuted_weights_prod F σ w (RootCoordinate.diagonalCoordinates_prod F t.diagonal)
  have hx : p x = transportMatrix F a b i j := transportLift_projection F p honto a b i j
  have hq : p q = p (τ t') := by
    calc
      p q = (transportMatrix F a b i j)⁻¹ * RootCoordinate.torusToGL F n t *
          transportMatrix F a b i j := by simp only [q, map_mul, map_inv, hx, hτ]
      _ = FiniteRootLifting.diagonalUnit F w' := by
        rw [torusToGL_eq_diagonalUnit F t]
        exact columnUnit_conjugate_diagonal F σ (signedColumns F σ) w
      _ = p (τ t') :=
        ((hτ t').trans (torusToGL_diagonalTorusLift F w' hw')).symm
  have ht' : RootCoordinate.diagonalCoordinates F t'.diagonal = w' :=
    diagonalTorusLift_coordinates F w' hw'
  have hact : q * U (Multiplicative.ofAdd z₀) * q⁻¹ =
      U (Multiplicative.ofAdd ((δ : F) * z₀)) := by
    calc
      _ = τ t' * U (Multiplicative.ofAdd z₀) * (τ t')⁻¹ :=
        conjugate_eq_of_projection_eq p hc hq (U (Multiplicative.ofAdd z₀))
      _ = _ := by
        have he := hbase t' z₀
        rw [ht'] at he
        simpa only [w', ha, hb] using he
  have hz : (δ : F) * z₀ = ((c⁻¹ : Fˣ) : F) * ((δ : F) * z) := by
    dsimp only [z₀]
    ring
  calc
    τ t * FiniteRootLifting.root (rootSections F p honto a b U) i j hij z * (τ t)⁻¹ =
        x * (q * U (Multiplicative.ofAdd z₀) * q⁻¹) * x⁻¹ := by
      rw [rootSections_apply]
      change τ t * (x * U (Multiplicative.ofAdd z₀) * x⁻¹) * (τ t)⁻¹ = _
      simp [q, mul_assoc]
    _ = x * U (Multiplicative.ofAdd ((δ : F) * z₀)) * x⁻¹ := by rw [hact]
    _ = FiniteRootLifting.root (rootSections F p honto a b U) i j hij ((δ : F) * z) := by
      rw [rootSections_apply]
      change x * U (Multiplicative.ofAdd ((δ : F) * z₀)) * x⁻¹ =
        x * U (Multiplicative.ofAdd (((c⁻¹ : Fˣ) : F) * ((δ : F) * z))) * x⁻¹
      rw [hz]

/-- A single torus lift of each product-one diagonal works simultaneously for every root. -/
theorem rootSections_diagonal_covariance
    (p : E →* Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hc : p.ker ≤ Subgroup.center E) (honto : DetOneOnto F p)
    (a b : Fin (n + 1)) (hab : a ≠ b)
    (τ : RootCoordinate.Torus F n →* E) (U : Multiplicative F →* E)
    (hτ : ∀ t, p (τ t) = RootCoordinate.torusToGL F n t)
    (hbase : BaseDiagonalCovariance F τ a b U) :
    FiniteRootLifting.DiagonalCovariance p (rootSections F p honto a b U) := by
  intro w hw
  refine ⟨τ (diagonalTorusLift F w), (hτ _).trans (torusToGL_diagonalTorusLift F w hw), ?_⟩
  intro i j hij z
  have he := rootSections_tau_covariance F p hc honto a b hab τ U hτ hbase
    (diagonalTorusLift F w) i j hij z
  simpa only [diagonalTorusLift_coordinates F w hw] using he

/-- Actual root sections and common-diagonal covariance from only the fixed primitive data. -/
theorem construct_root_sections
    (p : E →* Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hc : p.ker ≤ Subgroup.center E) (honto : DetOneOnto F p)
    (a b : Fin (n + 1)) (hab : a ≠ b)
    (τ : RootCoordinate.Torus F n →* E) (U : Multiplicative F →* E)
    (hτ : ∀ t, p (τ t) = RootCoordinate.torusToGL F n t)
    (hU : ∀ z : F, p (U (Multiplicative.ofAdd z)) =
      _root_.Matrix.GeneralLinearGroup.elementary a b hab z)
    (hbase : BaseDiagonalCovariance F τ a b U) :
    ∃ R : (i j : Fin (n + 1)) → i ≠ j → Multiplicative F →* E,
      (∀ (i j : Fin (n + 1)) (hij : i ≠ j) (z : F),
        p (FiniteRootLifting.root R i j hij z) =
          _root_.Matrix.GeneralLinearGroup.elementary i j hij z) ∧
      FiniteRootLifting.DiagonalCovariance p R ∧
      (∀ z : F, FiniteRootLifting.root R a b hab z = U (Multiplicative.ofAdd z)) := by
  refine ⟨rootSections F p honto a b U, ?_, ?_, ?_⟩
  · exact rootSections_projection F p honto a b hab U hU
  · exact rootSections_diagonal_covariance F p hc honto a b hab τ U hτ hbase
  · exact rootSections_base F p hc honto a b hab U

end StableSteinberg.RootSectionProducer

end

end

/-! ## RootSectionRelations -/

section

noncomputable section
universe u v
namespace StableSteinberg.RootSectionProducer
open StableSteinberg
open scoped commutatorElement
variable (F : Type u) [Field F] [CharZero F]
variable {E : Type v} [Group E] {n : ℕ}

/-- The accepted finite-root theorem now applies with no root-family input. -/
theorem rootSections_original_relations
    (p : E →* Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hc : p.ker ≤ Subgroup.center E) (honto : DetOneOnto F p)
    (a b : Fin (n + 1)) (hab : a ≠ b)
    (τ : RootCoordinate.Torus F n →* E) (U : Multiplicative F →* E)
    (hτ : ∀ t, p (τ t) = RootCoordinate.torusToGL F n t)
    (hU : ∀ z : F, p (U (Multiplicative.ofAdd z)) =
      _root_.Matrix.GeneralLinearGroup.elementary a b hab z)
    (hbase : BaseDiagonalCovariance F τ a b U) (hn : 5 ≤ n + 1) :
    let R := rootSections F p honto a b U
    (∀ (i j : Fin (n + 1)) (hij : i ≠ j) (s t : F),
      FiniteRootLifting.root R i j hij s * FiniteRootLifting.root R i j hij t =
        FiniteRootLifting.root R i j hij (s + t)) ∧
    (∀ (i j k l : Fin (n + 1)) (hij : i ≠ j) (hkl : k ≠ l)
        (_hjk : j ≠ k) (_hli : l ≠ i) (s t : F),
      ⁅FiniteRootLifting.root R i j hij s, FiniteRootLifting.root R k l hkl t⁆ = 1) ∧
    (∀ (i j k : Fin (n + 1)) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s t : F),
      ⁅FiniteRootLifting.root R i j hij s, FiniteRootLifting.root R j k hjk t⁆ =
        FiniteRootLifting.root R i k hik (s * t)) :=
  FiniteRootLifting.original_root_relations p hc (rootSections F p honto a b U)
    (rootSections_projection F p honto a b hab U hU)
    (rootSections_diagonal_covariance F p hc honto a b hab τ U hτ hbase) hn

end StableSteinberg.RootSectionProducer

end

end
