/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matsumoto.BruhatExtension
public import Colib.GroupTheory.Steinberg.Matsumoto.BruhatLeftGroup
public import Colib.GroupTheory.Steinberg.Matsumoto.BruhatActions
public import Colib.GroupTheory.Steinberg.Matsumoto.Torus
public import Colib.GroupTheory.Steinberg.Matsumoto.Weyl
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Colib.LinearAlgebra.Matrix.Bruhat.Coordinates
public import Colib.GroupTheory.Steinberg.Matsumoto.RootSections
public import Colib.GroupTheory.Steinberg.Matsumoto.FiniteRootLifting
public import Colib.GroupTheory.Steinberg.Matsumoto.Normalizer
public import Colib.GroupTheory.Steinberg.Matsumoto.LiftedWeyl
public import Colib.GroupTheory.Steinberg.Matsumoto.MatrixBasics
public import Colib.GroupTheory.Steinberg.Matsumoto.DetectorTransfer
public import Colib.GroupTheory.MonoidHom.CentralKernel
public import Colib.GroupTheory.Steinberg.Basic
public import Colib.GroupTheory.StableGeneralLinear.Basic
public import Colib.GroupTheory.StableGeneralLinear.Elementary
public import Colib.RingTheory.KTheory.MilnorK.Steinberg

/-!
# Injectivity

Adapted from Quillen Matsumoto/Injectivity.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native Stacks
homogeneous Milnor group and native matrix units throughout.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## RootCoordinateFiniteBase -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma finiteBaseRoot_lt (n : ℕ) : (0 : Fin (n + 2)) < 1 := Fin.zero_lt_one

/-- The actual additive base section, in matrix dimension n+2 so the two indices always exist. -/
def bruhatBaseRootSection (n : ℕ) : Multiplicative F →* BruhatLeftGroup F (n + 1) where
  toFun z := bruhatUpperRoot F (0 : Fin (n + 2)) 1 (finiteBaseRoot_lt n) z.toAdd
  map_one' := by
    change bruhatUpperInclusion F (n + 1)
      (upperRootMatrix F (0 : Fin (n + 2)) 1 (finiteBaseRoot_lt n) 0) = 1
    have he : upperRootMatrix F (0 : Fin (n + 2)) 1 (finiteBaseRoot_lt n) 0 = 1 := by
      apply Subtype.ext
      exact Matrix.GeneralLinearGroup.elementary_zero (0 : Fin (n + 2)) 1 (finiteBaseRoot_lt n).ne
    rw [he, map_one]
  map_mul' z w := bruhatUpperRoot_add F _ _ (finiteBaseRoot_lt n) z.toAdd w.toAdd

lemma bruhatBaseRootSection_projection (n : ℕ) (z : F) :
    bruhatLeftToGL F (n + 1) (bruhatBaseRootSection F n (Multiplicative.ofAdd z)) =
      Matrix.GeneralLinearGroup.elementary (0 : Fin (n + 2)) 1 (finiteBaseRoot_lt n).ne z :=
  bruhatUpperRoot_projection F _ _ (finiteBaseRoot_lt n) z

/-- The actual projection covers matrices whose literal determinant is one. -/
lemma bruhatLeftToGL_surjective_det_value (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (hg : Matrix.det g.val = 1) :
    ∃ e : BruhatLeftGroup F n, bruhatLeftToGL F n e = g := by
  apply bruhatLeftToGL_surjective_det_one F n g
  apply Units.ext
  exact hg

/-- The constructed base homomorphism has the exact primitive diagonal covariance. -/
theorem bruhatBaseRootSection_covariance (n : ℕ) (t : Torus F (n + 1)) (z : F) :
    bruhatTorusInclusion F (n + 1) t * bruhatBaseRootSection F n (Multiplicative.ofAdd z) *
        (bruhatTorusInclusion F (n + 1) t)⁻¹ =
      bruhatBaseRootSection F n (Multiplicative.ofAdd
        (((diagonalCoordinates F t.diagonal (0 : Fin (n + 2)) *
          (diagonalCoordinates F t.diagonal 1)⁻¹ : Fˣ) : F) * z)) :=
  bruhatUpperRoot_diagonal_covariance F t _ _ (finiteBaseRoot_lt n) z

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateFiniteRoots -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- Actual additive root sections in dimension n+2, constructed from the upper01 section. -/
def bruhatRootSections (n : ℕ) :
    (i j : Fin (n + 2)) → i ≠ j → Multiplicative F →* BruhatLeftGroup F (n + 1) :=
  RootSectionProducer.rootSections F (bruhatLeftToGL F (n + 1))
    (bruhatLeftToGL_surjective_det_value F (n + 1)) 0 1 (bruhatBaseRootSection F n)

theorem bruhatRootSections_projection (n : ℕ) (i j : Fin (n + 2)) (hij : i ≠ j) (a : F) :
    bruhatLeftToGL F (n + 1) (FiniteRootLifting.root (bruhatRootSections F n) i j hij a) =
      Matrix.GeneralLinearGroup.elementary i j hij a :=
  RootSectionProducer.rootSections_projection F (bruhatLeftToGL F (n + 1))
    (bruhatLeftToGL_surjective_det_value F (n + 1)) 0 1 (finiteBaseRoot_lt n).ne
    (bruhatBaseRootSection F n) (bruhatBaseRootSection_projection F n) i j hij a

/-- One actual torus lift of every product-one diagonal works simultaneously for all roots. -/
theorem bruhatRootSections_diagonal_covariance (n : ℕ) :
    FiniteRootLifting.DiagonalCovariance (bruhatLeftToGL F (n + 1)) (bruhatRootSections F n) :=
  RootSectionProducer.rootSections_diagonal_covariance F (bruhatLeftToGL F (n + 1))
    (bruhatLeftToGL_ker_central F (n + 1))
    (bruhatLeftToGL_surjective_det_value F (n + 1)) 0 1 (finiteBaseRoot_lt n).ne
    (bruhatTorusInclusion F (n + 1)) (bruhatBaseRootSection F n)
    (bruhatLeftToGL_torus F (n + 1)) (bruhatBaseRootSection_covariance F n)

/-- The constructed root family retains the original additive base section exactly. -/
theorem bruhatRootSections_base (n : ℕ) (a : F) :
    FiniteRootLifting.root (bruhatRootSections F n) 0 1 (finiteBaseRoot_lt n).ne a =
      bruhatBaseRootSection F n (Multiplicative.ofAdd a) :=
  RootSectionProducer.rootSections_base F (bruhatLeftToGL F (n + 1))
    (bruhatLeftToGL_ker_central F (n + 1))
    (bruhatLeftToGL_surjective_det_value F (n + 1)) 0 1 (finiteBaseRoot_lt n).ne
    (bruhatBaseRootSection F n) a

variable [CharZero F]
open scoped commutatorElement

/-- All three original root relations in the actual group, with producer inputs discharged. -/
theorem bruhatRootSections_relations (n : ℕ) (hn : 3 ≤ n) :
    (∀ (i j : Fin (n + 2)) (hij : i ≠ j) (a b : F),
      FiniteRootLifting.root (bruhatRootSections F n) i j hij a *
        FiniteRootLifting.root (bruhatRootSections F n) i j hij b =
          FiniteRootLifting.root (bruhatRootSections F n) i j hij (a + b)) ∧
    (∀ (i j k l : Fin (n + 2)) (hij : i ≠ j) (hkl : k ≠ l)
        (_hjk : j ≠ k) (_hli : l ≠ i) (a b : F),
      ⁅FiniteRootLifting.root (bruhatRootSections F n) i j hij a,
        FiniteRootLifting.root (bruhatRootSections F n) k l hkl b⁆ = 1) ∧
    (∀ (i j k : Fin (n + 2)) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F),
      ⁅FiniteRootLifting.root (bruhatRootSections F n) i j hij a,
        FiniteRootLifting.root (bruhatRootSections F n) j k hjk b⁆ =
          FiniteRootLifting.root (bruhatRootSections F n) i k hik (a * b)) :=
  FiniteRootLifting.original_root_relations (bruhatLeftToGL F (n + 1))
    (bruhatLeftToGL_ker_central F (n + 1)) (bruhatRootSections F n)
    (bruhatRootSections_projection F n) (bruhatRootSections_diagonal_covariance F n) (by omega)

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateFiniteDetectors -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
open scoped commutatorElement
variable (F : Type u) [Field F]

/-- Standard stabilization of an original rank-n index by two final coordinates. -/
def finiteRootIndex {n : ℕ} (i : Fin n) : Fin (n + 2) := i.castSucc.castSucc

lemma finiteRootIndex_injective (n : ℕ) : Function.Injective (@finiteRootIndex n) := by
  intro i j he
  exact Fin.ext (congrArg (fun z : Fin (n + 2) => z.val) he)

/-- The actual finite detector element; diagonal index pairs are assigned the identity. -/
def finiteRootElement (n : ℕ) (i j : Fin n) (a : F) : BruhatLeftGroup F (n + 1) :=
  if h : i ≠ j then FiniteRootLifting.root (bruhatRootSections F n)
    (finiteRootIndex i) (finiteRootIndex j) ((finiteRootIndex_injective n).ne h) a else 1

lemma finiteRootElement_of_ne (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    finiteRootElement F n i j a = FiniteRootLifting.root (bruhatRootSections F n)
      (finiteRootIndex i) (finiteRootIndex j) ((finiteRootIndex_injective n).ne hij) a :=
  dite_eq_left hij

/-- The literal permutation of the actual lifted Bruhat state used by the eventual detector. -/
def finiteRootOperator (n : ℕ) (i j : Fin n) (a : F) : Equiv.Perm (BruhatState F (n + 1)) :=
  (finiteRootElement F n i j a).val

lemma finiteRootElement_projection (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    bruhatLeftToGL F (n + 1) (finiteRootElement F n i j a) =
      Matrix.GeneralLinearGroup.elementary (finiteRootIndex i) (finiteRootIndex j)
        ((finiteRootIndex_injective n).ne hij) a := by
  rw [finiteRootElement_of_ne F n i j hij]
  exact bruhatRootSections_projection F n _ _ _ a

theorem finiteRootOperator_add (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a b : F) :
    finiteRootOperator F n i j a * finiteRootOperator F n i j b =
      finiteRootOperator F n i j (a + b) := by
  have he : finiteRootElement F n i j a * finiteRootElement F n i j b =
      finiteRootElement F n i j (a + b) := by
    simp only [finiteRootElement_of_ne F n i j hij]
    exact (FiniteRootLifting.root_add (bruhatRootSections F n) _ _ _ a b).symm
  exact congrArg Subtype.val he

variable [CharZero F]

theorem finiteRootOperator_disjoint (n : ℕ) (hn : 3 ≤ n) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (a b : F) :
    ⁅finiteRootOperator F n i j a, finiteRootOperator F n k l b⁆ = 1 := by
  have he : ⁅finiteRootElement F n i j a, finiteRootElement F n k l b⁆ = 1 := by
    rw [finiteRootElement_of_ne F n i j hij, finiteRootElement_of_ne F n k l hkl]
    exact (bruhatRootSections_relations F n hn).2.1 _ _ _ _ _ _
      ((finiteRootIndex_injective n).ne hjk) ((finiteRootIndex_injective n).ne hli) a b
  exact congrArg Subtype.val he

theorem finiteRootOperator_chain (n : ℕ) (hn : 3 ≤ n) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F) :
    ⁅finiteRootOperator F n i j a, finiteRootOperator F n j k b⁆ =
      finiteRootOperator F n i k (a * b) := by
  have he : ⁅finiteRootElement F n i j a, finiteRootElement F n j k b⁆ =
      finiteRootElement F n i k (a * b) := by
    rw [finiteRootElement_of_ne F n i j hij, finiteRootElement_of_ne F n j k hjk,
      finiteRootElement_of_ne F n i k hik]
    exact (bruhatRootSections_relations F n hn).2.2 _ _ _ _ _ _ a b
  exact congrArg Subtype.val he

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateFiniteReadout -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The original coefficient group acts by the actual finite lifted permutations. -/
def finiteCoefficientOperator (n : ℕ) : Multiplicative (MilnorKTheory F 2) →*
    Equiv.Perm (BruhatState F (n + 1)) :=
  (BruhatLeftGroup F (n + 1)).subtype.comp (bruhatLeftCoefficient F (n + 1))

/-- Read the original Milnor coordinate of the normalizer evaluated at its identity state. -/
def finiteDetectorCoordinate (n : ℕ) (s : BruhatState F (n + 1)) : MilnorKTheory F 2 :=
  (normalizerEvaluation F (n + 1) s.normalizer).1.central

/-- The concrete identity state detects every unchanged Milnor coefficient exactly. -/
theorem finiteCoefficientOperator_coordinate (n : ℕ) (a : MilnorKTheory F 2) :
    finiteDetectorCoordinate F n
      (finiteCoefficientOperator F n (Multiplicative.ofAdd a) (bruhatBase F (n + 1))) = a := by
  change (normalizerEvaluation F (n + 1)
    (normalizerTorus F (n + 1) (coefficient F (n + 1) (Multiplicative.ofAdd a)) * 1)).1.central = a
  rw [mul_one]
  change ((coefficient F (n + 1) (Multiplicative.ofAdd a)) * 1).central = a
  rw [mul_one]
  rfl

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateFiniteWordMatrices -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The literal original three-elementary Weyl word at arbitrary distinct finite indices. -/
def finiteMatrixWeyl {m : ℕ} (i j : Fin m) (hij : i ≠ j) (a : Fˣ) :
    Matrix.GeneralLinearGroup (Fin m) F :=
  Matrix.GeneralLinearGroup.elementary i j hij (a : F) *
    Matrix.GeneralLinearGroup.elementary j i hij.symm (-((a⁻¹ : Fˣ) : F)) *
      Matrix.GeneralLinearGroup.elementary i j hij (a : F)

lemma finiteMatrixWeyl_mul_entry {m : ℕ} (i j : Fin m) (hij : i ≠ j) (a : Fˣ)
    (g : Matrix.GeneralLinearGroup (Fin m) F) (r s : Fin m) :
    (finiteMatrixWeyl F i j hij a * g).val r s =
      if r = i then (a : F) * g.val j s else
      if r = j then -((a⁻¹ : Fˣ) : F) * g.val i s else g.val r s := by
  simp only [finiteMatrixWeyl, mul_assoc, elementary_left_mul_entry]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    simp [hri, hrj, hij, hij.symm, Units.val_inv_eq_inv_val]
  all_goals field_simp
  all_goals ring

lemma finiteMatrixWeyl_entry {m : ℕ} (i j : Fin m) (hij : i ≠ j) (a : Fˣ) (r s : Fin m) :
    (finiteMatrixWeyl F i j hij a).val r s =
      if r = i then (if j = s then (a : F) else 0) else
      if r = j then (if i = s then -((a⁻¹ : Fˣ) : F) else 0) else
      if r = s then 1 else 0 := by
  simpa only [mul_one, Units.val_one, Matrix.one_apply, mul_ite, mul_zero] using
    finiteMatrixWeyl_mul_entry F i j hij a 1 r s

/-- The literal original normalization h(a)=w(a)w(-1) on arbitrary finite indices. -/
def finiteMatrixTorus {m : ℕ} (i j : Fin m) (hij : i ≠ j) (a : Fˣ) :
    Matrix.GeneralLinearGroup (Fin m) F :=
  finiteMatrixWeyl F i j hij a * finiteMatrixWeyl F i j hij (-1)

lemma finiteMatrixTorus_entry {m : ℕ} (i j : Fin m) (hij : i ≠ j) (a : Fˣ) (r s : Fin m) :
    (finiteMatrixTorus F i j hij a).val r s =
      if r = s then ((Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin m → Fˣ) r : F) else 0 := by
  rw [finiteMatrixTorus, finiteMatrixWeyl_mul_entry]
  simp only [finiteMatrixWeyl_entry]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsi : s = i <;> by_cases hsj : s = j <;>
      simp [hri, hrj, hsi, hsj, hij, hij.symm]

lemma torusToGL_simple_eq_finiteMatrixTorus {n : ℕ} (i : Fin n) (a : Fˣ) :
    torusToGL F n (simple F i a) =
      finiteMatrixTorus F i.castSucc i.succ i.castSucc_lt_succ.ne a := by
  apply Units.ext
  ext r s
  rw [torusToGL_simple_entry, finiteMatrixTorus_entry]
  rfl

lemma adjacentComposite_endpoints_ne {n : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val) :
    i.castSucc ≠ j.succ := by
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

/-- The shifted signed H02 section has exactly the original normalized endpoint diagonal. -/
lemma torusToGL_adjacentComposite_eq_finiteMatrixTorus {n : ℕ} (i j : Fin n)
    (hij : i.val + 1 = j.val) (a : Fˣ) :
    torusToGL F n (adjacentComposite F i j a) =
      finiteMatrixTorus F i.castSucc j.succ (adjacentComposite_endpoints_ne i j hij) a := by
  have hmid : j.castSucc = i.succ := Fin.ext hij.symm
  have h0 : i.castSucc ≠ j.succ := adjacentComposite_endpoints_ne i j hij
  have h1 : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  have h2 : i.succ ≠ j.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_succ] at hv
    omega
  have hd : simpleDiagonal F j a * simpleDiagonal F i a =
      (Pi.mulSingle i.castSucc a * Pi.mulSingle j.succ a⁻¹ : Fin (n + 1) → Fˣ) := by
    funext r
    by_cases hr0 : r = i.castSucc <;> by_cases hr1 : r = i.succ <;>
      by_cases hr2 : r = j.succ <;>
        simp_all [simpleDiagonal, eq_comm]
  rw [adjacentComposite, map_mul]
  apply Units.ext
  ext r s
  rw [finiteMatrixTorus_entry]
  change (Matrix.diagonal (fun x => (diagonalCoordinates F (Pi.mulSingle j a) x : F)) *
    Matrix.diagonal (fun x => (diagonalCoordinates F (Pi.mulSingle i a) x : F))) r s = _
  rw [diagonalCoordinates_single, diagonalCoordinates_single, Matrix.diagonal_mul_diagonal]
  have he := congrFun hd r
  by_cases hrs : r = s
  · subst s
    simpa only [Matrix.diagonal_apply_eq, ↓reduceIte, Pi.mul_apply, Units.val_mul] using
      congrArg (fun u : Fˣ => (u : F)) he
  · simp only [Matrix.diagonal_apply_ne _ hrs, hrs, ↓reduceIte]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateFiniteWordElements -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The original three-root Weyl word evaluated in the actual finite detector group. -/
def finiteWeylElement (n : ℕ) (i j : Fin n) (a : Fˣ) : BruhatLeftGroup F (n + 1) :=
  finiteRootElement F n i j (a : F) *
    finiteRootElement F n j i (-((a⁻¹ : Fˣ) : F)) * finiteRootElement F n i j (a : F)

/-- The original h word, with its W(-1) normalization preserved literally. -/
def finiteTorusElement (n : ℕ) (i j : Fin n) (a : Fˣ) : BruhatLeftGroup F (n + 1) :=
  finiteWeylElement F n i j a * finiteWeylElement F n i j (-1)

lemma finiteWeylElement_projection (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    bruhatLeftToGL F (n + 1) (finiteWeylElement F n i j a) =
      finiteMatrixWeyl F (finiteRootIndex i) (finiteRootIndex j)
        ((finiteRootIndex_injective n).ne hij) a := by
  simp only [finiteWeylElement, map_mul, finiteRootElement_projection F n i j hij,
    finiteRootElement_projection F n j i hij.symm]
  rfl

lemma finiteTorusElement_projection (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : Fˣ) :
    bruhatLeftToGL F (n + 1) (finiteTorusElement F n i j a) =
      finiteMatrixTorus F (finiteRootIndex i) (finiteRootIndex j)
        ((finiteRootIndex_injective n).ne hij) a := by
  rw [finiteTorusElement, map_mul, finiteWeylElement_projection F n i j hij,
    finiteWeylElement_projection F n i j hij]
  rfl

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateFiniteCommutator -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
open scoped commutatorElement
variable (F : Type u) [Field F]

/-- The literal finite 01/02 root words have the positive original Milnor commutator mark. -/
theorem finiteRootOperator_commutator_mark (n : ℕ) (hn : 3 ≤ n) (a b : Fˣ) :
    CommutatorDetectorTransfer.finiteCommutator (finiteRootOperator F) n hn a b =
      finiteCoefficientOperator F n (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])) := by
  let h2n : 2 ≤ n := (by decide : 2 ≤ 3).trans hn
  let p0 : Fin n := (0 : Fin 2).castLE h2n
  let p1 : Fin n := (1 : Fin 2).castLE h2n
  let q0 : Fin n := (0 : Fin 3).castLE hn
  let q2 : Fin n := (2 : Fin 3).castLE hn
  let i : Fin (n + 1) := ⟨0, by omega⟩
  let j : Fin (n + 1) := ⟨1, by omega⟩
  have hij : i.val + 1 = j.val := rfl
  have hp : p0 ≠ p1 := by
    intro he
    have hv : (0 : ℕ) = 1 := congrArg (fun z : Fin n => z.val) he
    omega
  have hq : q0 ≠ q2 := by
    intro he
    have hv : (0 : ℕ) = 2 := congrArg (fun z : Fin n => z.val) he
    omega
  have hpi : finiteRootIndex p0 = i.castSucc := Fin.ext rfl
  have hpj : finiteRootIndex p1 = i.succ := Fin.ext rfl
  have hqi : finiteRootIndex q0 = i.castSucc := Fin.ext rfl
  have hqj : finiteRootIndex q2 = j.succ := Fin.ext rfl
  have hP : bruhatLeftToGL F (n + 1) (finiteTorusElement F n p0 p1 a) =
      bruhatLeftToGL F (n + 1) (bruhatTorusInclusion F (n + 1) (simple F i a)) := by
    rw [bruhatLeftToGL_torus]
    have he := finiteTorusElement_projection F n p0 p1 hp a
    simp only [hpi, hpj] at he
    exact he.trans (torusToGL_simple_eq_finiteMatrixTorus F i a).symm
  have hQ : bruhatLeftToGL F (n + 1) (finiteTorusElement F n q0 q2 b) =
      bruhatLeftToGL F (n + 1)
        (bruhatTorusInclusion F (n + 1) (adjacentComposite F i j b)) := by
    rw [bruhatLeftToGL_torus]
    have he := finiteTorusElement_projection F n q0 q2 hq b
    simp only [hqi, hqj] at he
    exact he.trans (torusToGL_adjacentComposite_eq_finiteMatrixTorus F i j hij b).symm
  have he : ⁅finiteTorusElement F n p0 p1 a, finiteTorusElement F n q0 q2 b⁆ =
      bruhatLeftCoefficient F (n + 1) (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])) := by
    calc
      _ = bruhatTorusInclusion F (n + 1) ⁅simple F i a, adjacentComposite F i j b⁆ :=
        _root_.MonoidHom.CentralKernel.commutator_eq_torus_commutator (bruhatLeftToGL F (n + 1))
          (bruhatLeftToGL_ker_central F (n + 1)) (bruhatTorusInclusion F (n + 1)) hP hQ
      _ = _ := by
        rw [simple_composite_commutator F i j hij]
        rfl
  change ⁅(finiteTorusElement F n p0 p1 a).val, (finiteTorusElement F n q0 q2 b).val⁆ =
    (bruhatLeftCoefficient F (n + 1) (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b]))).val
  exact congrArg Subtype.val he

end StableSteinberg.RootCoordinate

end

end

/-! ## StableSteinbergMilnorInjectivity -/

section

/-!
# Injectivity of the original marked Milnor map in characteristic zero

The detector of rank n acts on the actual Bruhat state in matrix dimension n+2;
each original rank-n root uses two standard final-coordinate inclusions. The
single eventual cutoff is 5. No compatibility between the finite state sets is
assumed or needed by the original finite-rank-labelled presentation transfer.
-/

noncomputable section
universe u
namespace StableSteinberg
open RootCoordinate
variable (F : Type u) [Field F] [CharZero F]

/-- The original Milnor map to the Steinberg kernel is injective in characteristic zero. -/
theorem milnorToKernel_injective_charZero : Function.Injective (milnorToKernel F) := by
  apply CommutatorDetectorTransfer.milnorToKernel_injective_of_commutator_detectors
    (F := F) (S := fun n => BruhatState F (n + 1)) 5 (finiteRootOperator F)
    (fun n _ i j hij a b => finiteRootOperator_add F n i j hij a b)
    (fun n hn i j k l hij hkl hjk hli a b =>
      finiteRootOperator_disjoint F n (by omega) i j k l hij hkl hjk hli a b)
    (fun n hn i j k hij hjk hik a b =>
      finiteRootOperator_chain F n (by omega) i j k hij hjk hik a b)
    (finiteCoefficientOperator F) (by decide)
    (fun n hn a b => finiteRootOperator_commutator_mark F n (by omega) a b)
    (fun n _ => bruhatBase F (n + 1)) (finiteDetectorCoordinate F)
  intro n _ a
  exact finiteCoefficientOperator_coordinate F n a

end StableSteinberg

end

end
