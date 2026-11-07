/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Steinberg
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Colib.GroupTheory.Steinberg.Basic
public import Colib.GroupTheory.StableGeneralLinear.Basic
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Colib.GroupTheory.StableGeneralLinear.Elementary
public import Colib.GroupTheory.Steinberg.Torus

/-!
# DetectorTransfer

Adapted from Quillen Matsumoto/DetectorTransfer.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native Stacks
homogeneous Milnor group and native matrix units throughout.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## StableDetectorTransfer -/

section

/-!
# Eventual-product transfer for finite Steinberg detectors

This file constructs an actual quotient of a dependent product of groups by
the normal subgroup of eventually identity families. It then represents the
original finite-rank-labelled stable Steinberg presentation in that quotient.
The input consists of finite permutation actions above one fixed rank. No
stabilization maps between their state sets are used.

The final injectivity conclusion remains conditional on those finite actions,
their positive ordered-defect marking, and faithful coefficient translations.
It does not construct the finite detector family.
-/
noncomputable section

universe u v

namespace StableSteinberg.EventualProduct

open Filter

variable (G : ℕ → Type v) [∀ n, _root_.Group (G n)]

/-- Families that are the identity at all sufficiently large natural indices. -/
def eventuallyOne : Subgroup (∀ n, G n) where
  carrier := {g | ∀ᶠ n in atTop, g n = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    filter_upwards [ha, hb] with n han hbn
    simp [han, hbn]
  inv_mem' := by
    intro a ha
    filter_upwards [ha] with n han
    simp [han]

instance eventuallyOne_normal : (eventuallyOne G).Normal where
  conj_mem := by
    intro a ha b
    filter_upwards [ha] with n han
    change b n * a n * (b n)⁻¹ = 1
    simp [han]

/-- The quotient of the dependent product by eventually identity families. -/
abbrev Quotient := (∀ n, G n) ⧸ eventuallyOne G

/-- The actual quotient homomorphism from the dependent product. -/
def quotientHom : (∀ n, G n) →* Quotient G := QuotientGroup.mk' (eventuallyOne G)

lemma quotientHom_eq_one (g : ∀ n, G n) :
    quotientHom G g = 1 ↔ ∀ᶠ n in atTop, g n = 1 :=
  QuotientGroup.eq_one_iff g

lemma quotientHom_eq_of_eventuallyEq {g h : ∀ n, G n}
    (he : ∀ᶠ n in atTop, g n = h n) : quotientHom G g = quotientHom G h := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  filter_upwards [he] with n hn
  change g n / h n = 1
  simp [hn]

end StableSteinberg.EventualProduct

namespace StableSteinberg.FiniteDetectorTransfer

open Filter
open scoped commutatorElement

variable {F : Type u} [Field F] {S : ℕ → Type v}

/-- The dependent product of the actual finite permutation groups. -/
abbrev PermProduct (S : ℕ → Type v) := ∀ n, Equiv.Perm (S n)

/-- The actual eventual quotient for a family of finite state sets. -/
abbrev DetectorQuotient (S : ℕ → Type v) :=
  EventualProduct.Quotient (fun n => Equiv.Perm (S n))

variable (n₀ : ℕ) (R : ∀ n, Fin n → Fin n → F → Equiv.Perm (S n))

/-- A root datum acts at each sufficiently large rank by its literal index casts. -/
def rootFamily (g : Generator F) : PermProduct S := fun n =>
  if hn : g.rank ≤ n ∧ n₀ ≤ n then
    R n (g.row.castLE hn.1) (g.col.castLE hn.1) g.entry
  else 1

omit [Field F] in
lemma rootFamily_high (r : ℕ) (i j : Fin r) (hij : i ≠ j) (a : F)
    (n : ℕ) (hr : r ≤ n) (hn : n₀ ≤ n) :
    rootFamily n₀ R ⟨r, i, j, hij, a⟩ n = R n (i.castLE hr) (j.castLE hr) a := by
  simp [rootFamily, hr, hn]

/-- Quotient-valued images of the original finite-rank-labelled generators. -/
def rootClass (g : Generator F) : DetectorQuotient S :=
  EventualProduct.quotientHom (fun n => Equiv.Perm (S n)) (rootFamily n₀ R g)

omit [Field F] in
/-- A different finite cutoff gives exactly the same quotient-valued root. -/
lemma rootClass_cutoff_eq (m₀ : ℕ) (g : Generator F) :
    rootClass n₀ R g = rootClass m₀ R g := by
  rcases g with ⟨r, i, j, hij, a⟩
  apply EventualProduct.quotientHom_eq_of_eventuallyEq
  filter_upwards [eventually_ge_atTop (max r (max n₀ m₀))] with n hn
  have hr : r ≤ n := (le_max_left r (max n₀ m₀)).trans hn
  have hcut : max n₀ m₀ ≤ n := (le_max_right r (max n₀ m₀)).trans hn
  rw [rootFamily_high n₀ R r i j hij a n hr ((le_max_left n₀ m₀).trans hcut),
    rootFamily_high m₀ R r i j hij a n hr ((le_max_right n₀ m₀).trans hcut)]

variable
    (hadd : ∀ n, n₀ ≤ n → ∀ (i j : Fin n), i ≠ j → ∀ a b,
      R n i j a * R n i j b = R n i j (a + b))
    (hdisjoint : ∀ n, n₀ ≤ n → ∀ (i j k l : Fin n),
      i ≠ j → k ≠ l → j ≠ k → l ≠ i → ∀ a b,
      ⁅R n i j a, R n k l b⁆ = 1)
    (hchain : ∀ n, n₀ ≤ n → ∀ (i j k : Fin n),
      i ≠ j → j ≠ k → i ≠ k → ∀ a b,
      ⁅R n i j a, R n j k b⁆ = R n i k (a * b))

include hadd hdisjoint hchain

/-- Each original relator is the identity at all sufficiently large coordinates. -/
lemma relator_eventually_one (r : FreeGroup (Generator F)) (hr : r ∈ relations F) :
    ∀ᶠ n in atTop, FreeGroup.lift (rootFamily n₀ R) r n = 1 := by
  cases hr with
  | rootAdd r i j hij a b =>
      filter_upwards [eventually_ge_atTop (max r n₀)] with n hn
      have hrn : r ≤ n := (le_max_left r n₀).trans hn
      have hn₀ : n₀ ≤ n := (le_max_right r n₀).trans hn
      simp only [word, map_mul, map_inv, FreeGroup.lift_apply_of, Pi.mul_apply, Pi.inv_apply]
      rw [rootFamily_high n₀ R r i j hij a n hrn hn₀,
        rootFamily_high n₀ R r i j hij b n hrn hn₀,
        rootFamily_high n₀ R r i j hij (a + b) n hrn hn₀]
      rw [hadd n hn₀ _ _ (fun h => hij (Fin.castLE_injective hrn h))]
      exact mul_inv_cancel _
  | disjoint r i j k l hij hkl hjk hli a b =>
      filter_upwards [eventually_ge_atTop (max r n₀)] with n hn
      have hrn : r ≤ n := (le_max_left r n₀).trans hn
      have hn₀ : n₀ ≤ n := (le_max_right r n₀).trans hn
      simp only [word, map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅rootFamily n₀ R ⟨r, i, j, hij, a⟩ n,
        rootFamily n₀ R ⟨r, k, l, hkl, b⟩ n⁆ = 1
      rw [rootFamily_high n₀ R r i j hij a n hrn hn₀,
        rootFamily_high n₀ R r k l hkl b n hrn hn₀]
      exact hdisjoint n hn₀ _ _ _ _
        (fun h => hij (Fin.castLE_injective hrn h))
        (fun h => hkl (Fin.castLE_injective hrn h))
        (fun h => hjk (Fin.castLE_injective hrn h))
        (fun h => hli (Fin.castLE_injective hrn h)) a b
  | chain r i j k hij hjk hik a b =>
      filter_upwards [eventually_ge_atTop (max r n₀)] with n hn
      have hrn : r ≤ n := (le_max_left r n₀).trans hn
      have hn₀ : n₀ ≤ n := (le_max_right r n₀).trans hn
      simp only [word, map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅rootFamily n₀ R ⟨r, i, j, hij, a⟩ n,
        rootFamily n₀ R ⟨r, j, k, hjk, b⟩ n⁆ *
        (rootFamily n₀ R ⟨r, i, k, hik, a * b⟩ n)⁻¹ = 1
      rw [rootFamily_high n₀ R r i j hij a n hrn hn₀,
        rootFamily_high n₀ R r j k hjk b n hrn hn₀,
        rootFamily_high n₀ R r i k hik (a * b) n hrn hn₀,
        hchain n hn₀ _ _ _
          (fun h => hij (Fin.castLE_injective hrn h))
          (fun h => hjk (Fin.castLE_injective hrn h))
          (fun h => hik (Fin.castLE_injective hrn h))]
      exact mul_inv_cancel _
  | stabilize r i j hij a =>
      filter_upwards [eventually_ge_atTop (max (r + 1) n₀)] with n hn
      have hrn : r + 1 ≤ n := (le_max_left (r + 1) n₀).trans hn
      have hn₀ : n₀ ≤ n := (le_max_right (r + 1) n₀).trans hn
      simp only [word, map_mul, map_inv, FreeGroup.lift_apply_of, Pi.mul_apply, Pi.inv_apply]
      rw [rootFamily_high n₀ R r i j hij a n ((Nat.le_succ r).trans hrn) hn₀,
        rootFamily_high n₀ R (r + 1) i.castSucc j.castSucc _ a n hrn hn₀]
      have hi : i.castLE ((Nat.le_succ r).trans hrn) = i.castSucc.castLE hrn :=
        Fin.ext rfl
      have hj : j.castLE ((Nat.le_succ r).trans hrn) = j.castSucc.castLE hrn :=
        Fin.ext rfl
      rw [hi, hj]
      exact mul_inv_cancel _

/-- All four original relator constructors vanish in the actual quotient. -/
lemma rootClass_relations (r : FreeGroup (Generator F)) (hr : r ∈ relations F) :
    FreeGroup.lift (rootClass n₀ R) r = 1 := by
  have hlift : FreeGroup.lift (rootClass n₀ R) =
      (EventualProduct.quotientHom (fun n => Equiv.Perm (S n))).comp
        (FreeGroup.lift (rootFamily n₀ R)) := by
    apply FreeGroup.ext_hom
    intro g
    simp [rootClass]
  rw [hlift]
  exact (EventualProduct.quotientHom_eq_one _ _).mpr
    (relator_eventually_one n₀ R hadd hdisjoint hchain r hr)

/-- The original presentation acts in the dependent eventual quotient. -/
def representation : Group F →* DetectorQuotient S :=
  PresentedGroup.toGroup (rootClass_relations n₀ R hadd hdisjoint hchain)

@[simp] lemma representation_x (r : ℕ) (i j : Fin r) (hij : i ≠ j) (a : F) :
    representation n₀ R hadd hdisjoint hchain (x F r i j hij a) =
      rootClass n₀ R ⟨r, i, j, hij, a⟩ :=
  PresentedGroup.toGroup.of _

/-- The represented root has exactly the requested representative with cutoff `max(r,3)`. -/
lemma representation_x_rank_three (r : ℕ) (i j : Fin r) (hij : i ≠ j) (a : F) :
    representation n₀ R hadd hdisjoint hchain (x F r i j hij a) =
      rootClass 3 R ⟨r, i, j, hij, a⟩ := by
  rw [representation_x]
  exact rootClass_cutoff_eq n₀ R 3 _

omit hadd hdisjoint hchain

/-- The literal finite Weyl word on the casts of the original indices `0,1`. -/
def finiteWeyl (n : ℕ) (hn : 2 ≤ n) (a : Fˣ) : Equiv.Perm (S n) :=
  R n ((0 : Fin 2).castLE hn) ((1 : Fin 2).castLE hn) (a : F) *
    R n ((1 : Fin 2).castLE hn) ((0 : Fin 2).castLE hn) (-((a⁻¹ : Fˣ) : F)) *
    R n ((0 : Fin 2).castLE hn) ((1 : Fin 2).castLE hn) (a : F)

/-- The finite normalized torus word with the original choice `w(a) w(-1)`. -/
def finiteTorus (n : ℕ) (hn : 2 ≤ n) (a : Fˣ) : Equiv.Perm (S n) :=
  finiteWeyl R n hn a * finiteWeyl R n hn (-1)

/-- The positive ordered defect of the literal finite torus words. -/
def finiteDefect (n : ℕ) (hn : 2 ≤ n) (a b : Fˣ) : Equiv.Perm (S n) :=
  finiteTorus R n hn a * finiteTorus R n hn b * (finiteTorus R n hn (a * b))⁻¹

/-- The product family of the exact original Weyl words. -/
def weylFamily (a : Fˣ) : PermProduct S :=
  rootFamily n₀ R ⟨2, 0, 1, by decide, (a : F)⟩ *
    rootFamily n₀ R ⟨2, 1, 0, by decide, -((a⁻¹ : Fˣ) : F)⟩ *
    rootFamily n₀ R ⟨2, 0, 1, by decide, (a : F)⟩

/-- The product family of the exact original torus words. -/
def torusFamily (a : Fˣ) : PermProduct S := weylFamily n₀ R a * weylFamily n₀ R (-1)

/-- The product family of the exact positive ordered defect words. -/
def defectFamily (a b : Fˣ) : PermProduct S :=
  torusFamily n₀ R a * torusFamily n₀ R b * (torusFamily n₀ R (a * b))⁻¹

lemma weylFamily_high (n : ℕ) (hr : 2 ≤ n) (hn : n₀ ≤ n) (a : Fˣ) :
    weylFamily n₀ R a n = finiteWeyl R n hr a := by
  simp only [weylFamily, Pi.mul_apply]
  rw [rootFamily_high n₀ R 2 0 1 (by decide) (a : F) n hr hn,
    rootFamily_high n₀ R 2 1 0 (by decide) (-((a⁻¹ : Fˣ) : F)) n hr hn]
  rfl

lemma defectFamily_high (n : ℕ) (hr : 2 ≤ n) (hn : n₀ ≤ n) (a b : Fˣ) :
    defectFamily n₀ R a b n = finiteDefect R n hr a b := by
  simp only [defectFamily, torusFamily, Pi.mul_apply, Pi.inv_apply,
    weylFamily_high n₀ R n hr hn, finiteDefect, finiteTorus]

include hadd hdisjoint hchain

/-- The representation keeps the original ordered defect, including its sign. -/
lemma representation_torusDefect (a b : Fˣ) :
    representation n₀ R hadd hdisjoint hchain (torusDefect a b) =
      EventualProduct.quotientHom (fun n => Equiv.Perm (S n)) (defectFamily n₀ R a b) := by
  simp only [torusDefect, h, w, map_mul, map_inv, representation_x, rootClass,
    defectFamily, torusFamily, weylFamily]

omit hadd hdisjoint hchain

variable (T : ∀ n, Multiplicative (MilnorKTheory F 2) →* Equiv.Perm (S n))

/-- The actual product homomorphism of finite coefficient translations. -/
def translationProduct : Multiplicative (MilnorKTheory F 2) →* PermProduct S where
  toFun m n := T n m
  map_one' := by funext n; exact map_one (T n)
  map_mul' a b := by funext n; exact map_mul (T n) a b

/-- Coefficients mapped into the actual quotient of the dependent product. -/
def coefficientMap : MilnorKTheory F 2 →+ Additive (DetectorQuotient S) :=
  ((EventualProduct.quotientHom (fun n => Equiv.Perm (S n))).comp
    (translationProduct T)).toAdditiveRight

lemma coefficientMap_apply (m : MilnorKTheory F 2) :
    coefficientMap T m = Additive.ofMul
      (EventualProduct.quotientHom (fun n => Equiv.Perm (S n))
        (fun n => T n (Multiplicative.ofAdd m))) := rfl

/-- Eventual coefficient faithfulness gives an injective quotient coefficient map. -/
lemma coefficientMap_injective
    (hfaithful : ∀ n, n₀ ≤ n → ∀ m : MilnorKTheory F 2,
      T n (Multiplicative.ofAdd m) = 1 → m = 0) :
    Function.Injective (coefficientMap T) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro m hm
  have he : ∀ᶠ n in atTop, T n (Multiplicative.ofAdd m) = 1 :=
    (EventualProduct.quotientHom_eq_one _ _).mp
      (show EventualProduct.quotientHom (fun n => Equiv.Perm (S n))
        (fun n => T n (Multiplicative.ofAdd m)) = 1 from hm)
  obtain ⟨n, hn, hnm⟩ := (he.and (eventually_ge_atTop n₀)).exists
  exact hfaithful n hnm m hn

/-- Faithfulness can be checked by evaluating translations at actual identity states. -/
lemma coefficientMap_injective_of_identity_states
    (s₀ : ∀ n, n₀ ≤ n → S n) (coordinate : ∀ n, S n → MilnorKTheory F 2)
    (hcoordinate : ∀ n (hn : n₀ ≤ n) (m : MilnorKTheory F 2),
      coordinate n (T n (Multiplicative.ofAdd m) (s₀ n hn)) = m) :
    Function.Injective (coefficientMap T) := by
  apply coefficientMap_injective n₀ T
  intro n hn m hm
  have hm0 : coordinate n (s₀ n hn) = 0 := by
    simpa using hcoordinate n hn 0
  have hme := hcoordinate n hn m
  rw [hm] at hme
  exact hme.symm.trans hm0

/-- The supplied Milnor symbol extensionality implies its actual symbol generation. -/
lemma milnorSymbol_closure :
    AddSubgroup.closure (Set.range (milnorKTupleSymbol (k := F) (n := 2))) = ⊤ := by
  let H : AddSubgroup (MilnorKTheory F 2) :=
    AddSubgroup.closure (Set.range (milnorKTupleSymbol (k := F) (n := 2)))
  have hq : QuotientAddGroup.mk' H = 0 := by
    apply milnorKTheory_addHom_ext
    intro a
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact AddSubgroup.subset_closure ⟨a, rfl⟩
  apply top_unique
  intro m _
  apply (QuotientAddGroup.eq_zero_iff _).mp
  exact DFunLike.congr_fun hq m

/-- Symbol comparison remains valid for additive homomorphisms into noncommutative groups. -/
lemma milnorAddHom_ext {A : Type*} [AddGroup A] (f g : MilnorKTheory F 2 →+ A)
    (he : ∀ a : Fin 2 → Fˣ, f (milnorKTupleSymbol a) = g (milnorKTupleSymbol a)) :
    f = g := by
  apply AddMonoidHom.eq_of_eqOn_dense (milnorSymbol_closure (F := F))
  rintro _ ⟨a, rfl⟩
  exact he a

include hadd hdisjoint hchain

/-- Restrict the representation to the original elementary kernel. -/
def kernelRepresentation :
    Additive ((toElementary F).ker) →+ Additive (DetectorQuotient S) :=
  ((representation n₀ R hadd hdisjoint hchain).comp (toElementary F).ker.subtype).toAdditive

variable (hlarge : 3 ≤ n₀)
    (hdefect : ∀ n (hn : n₀ ≤ n) (a b : Fˣ),
      finiteDefect R n ((show 2 ≤ n₀ from (by omega)).trans hn) a b =
        T n (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])))

include hlarge hdefect

/-- The composite with the ORIGINAL Milnor map equals the faithful coefficient map.
The finite positive ordered-defect marking is an explicit unresolved producer input. -/
lemma kernelRepresentation_comp_milnorToKernel :
    (kernelRepresentation n₀ R hadd hdisjoint hchain).comp (milnorToKernel F) =
      coefficientMap T := by
  apply milnorAddHom_ext
  intro a
  simp only [AddMonoidHom.comp_apply, milnorToKernel_symbol]
  change Additive.ofMul
      (representation n₀ R hadd hdisjoint hchain (torusDefect (a 0) (a 1))) = _
  rw [representation_torusDefect]
  apply congrArg Additive.ofMul
  apply EventualProduct.quotientHom_eq_of_eventuallyEq
  filter_upwards [eventually_ge_atTop n₀] with n hn
  rw [defectFamily_high n₀ R n ((show 2 ≤ n₀ from (by omega)).trans hn) hn]
  have hp : (![a 0, a 1] : Fin 2 → Fˣ) = a := by
    ext i
    fin_cases i <;> rfl
  change finiteDefect R n _ (a 0) (a 1) = T n (Multiplicative.ofAdd (milnorKTupleSymbol a))
  simpa only [hp] using hdefect n hn (a 0) (a 1)

/-- Finite detector actions imply injectivity of the ORIGINAL stable Milnor-to-kernel map.
No compatibility between state sets at different ranks is assumed. -/
theorem milnorToKernel_injective_of_finite_detectors
    (s₀ : ∀ n, n₀ ≤ n → S n) (coordinate : ∀ n, S n → MilnorKTheory F 2)
    (hcoordinate : ∀ n (hn : n₀ ≤ n) (m : MilnorKTheory F 2),
      coordinate n (T n (Multiplicative.ofAdd m) (s₀ n hn)) = m) :
    Function.Injective (milnorToKernel F) := by
  have hcomp := kernelRepresentation_comp_milnorToKernel n₀ R hadd hdisjoint hchain T
    hlarge hdefect
  have hi := coefficientMap_injective_of_identity_states n₀ T s₀ coordinate hcoordinate
  intro a b hab
  apply hi
  have ha := DFunLike.congr_fun hcomp a
  have hb := DFunLike.congr_fun hcomp b
  rw [← ha, ← hb]
  exact congrArg (kernelRepresentation n₀ R hadd hdisjoint hchain) hab

end StableSteinberg.FiniteDetectorTransfer

end

end

/-! ## CommutatorDetectorTransfer -/

section

/-!
# Stable transfer from the positive finite `h,h02` commutator marking

This consumer reuses the frozen actual dependent eventual quotient and original
presentation representation. It replaces the finite multiplicative-defect input
with the positive commutator of the literal finite `h` and `h02` root words.
The original stable commutator identity is used only after representation.
-/
noncomputable section

universe u v

namespace StableSteinberg.CommutatorDetectorTransfer

open Filter FiniteDetectorTransfer
open scoped commutatorElement

variable {F : Type u} [Field F] {S : ℕ → Type v}
    (n₀ : ℕ) (R : ∀ n, Fin n → Fin n → F → Equiv.Perm (S n))

/-- The actual finite `02,20` Weyl word on casts of the original rank-three indices. -/
def finiteWeyl02 (n : ℕ) (hn : 3 ≤ n) (a : Fˣ) : Equiv.Perm (S n) :=
  R n ((0 : Fin 3).castLE hn) ((2 : Fin 3).castLE hn) (a : F) *
    R n ((2 : Fin 3).castLE hn) ((0 : Fin 3).castLE hn) (-((a⁻¹ : Fˣ) : F)) *
    R n ((0 : Fin 3).castLE hn) ((2 : Fin 3).castLE hn) (a : F)

/-- The actual finite `h02` word with the original `w02(a) w02(-1)` normalization. -/
def finiteTorus02 (n : ℕ) (hn : 3 ≤ n) (a : Fˣ) : Equiv.Perm (S n) :=
  finiteWeyl02 R n hn a * finiteWeyl02 R n hn (-1)

/-- The positive finite commutator of the original `01` and `02` torus words. -/
def finiteCommutator (n : ℕ) (hn : 3 ≤ n) (a b : Fˣ) : Equiv.Perm (S n) :=
  ⁅finiteTorus R n ((by decide : 2 ≤ 3).trans hn) a, finiteTorus02 R n hn b⁆

/-- Product family of the exact original rank-three Weyl word. -/
def weyl02Family (a : Fˣ) : PermProduct S :=
  rootFamily n₀ R ⟨3, 0, 2, by decide, (a : F)⟩ *
    rootFamily n₀ R ⟨3, 2, 0, by decide, -((a⁻¹ : Fˣ) : F)⟩ *
    rootFamily n₀ R ⟨3, 0, 2, by decide, (a : F)⟩

/-- Product family of the literal original `h02` word. -/
def torus02Family (a : Fˣ) : PermProduct S :=
  weyl02Family n₀ R a * weyl02Family n₀ R (-1)

/-- Product family of the literal positive `h,h02` commutator. -/
def commutatorFamily (a b : Fˣ) : PermProduct S :=
  ⁅torusFamily n₀ R a, torus02Family n₀ R b⁆

lemma torusFamily_high (n : ℕ) (hr : 2 ≤ n) (hn : n₀ ≤ n) (a : Fˣ) :
    torusFamily n₀ R a n = finiteTorus R n hr a := by
  simp only [torusFamily, Pi.mul_apply, weylFamily_high n₀ R n hr hn, finiteTorus]

lemma weyl02Family_high (n : ℕ) (hr : 3 ≤ n) (hn : n₀ ≤ n) (a : Fˣ) :
    weyl02Family n₀ R a n = finiteWeyl02 R n hr a := by
  simp only [weyl02Family, Pi.mul_apply]
  rw [rootFamily_high n₀ R 3 0 2 (by decide) (a : F) n hr hn,
    rootFamily_high n₀ R 3 2 0 (by decide) (-((a⁻¹ : Fˣ) : F)) n hr hn]
  rfl

lemma torus02Family_high (n : ℕ) (hr : 3 ≤ n) (hn : n₀ ≤ n) (a : Fˣ) :
    torus02Family n₀ R a n = finiteTorus02 R n hr a := by
  simp only [torus02Family, Pi.mul_apply, weyl02Family_high n₀ R n hr hn, finiteTorus02]

lemma commutatorFamily_high (n : ℕ) (hr : 3 ≤ n) (hn : n₀ ≤ n) (a b : Fˣ) :
    commutatorFamily n₀ R a b n = finiteCommutator R n hr a b := by
  change ⁅torusFamily n₀ R a n, torus02Family n₀ R b n⁆ = _
  rw [torusFamily_high n₀ R n ((by decide : 2 ≤ 3).trans hr) hn,
    torus02Family_high n₀ R n hr hn]
  rfl

variable
    (hadd : ∀ n, n₀ ≤ n → ∀ (i j : Fin n), i ≠ j → ∀ a b,
      R n i j a * R n i j b = R n i j (a + b))
    (hdisjoint : ∀ n, n₀ ≤ n → ∀ (i j k l : Fin n),
      i ≠ j → k ≠ l → j ≠ k → l ≠ i → ∀ a b,
      ⁅R n i j a, R n k l b⁆ = 1)
    (hchain : ∀ n, n₀ ≤ n → ∀ (i j k : Fin n),
      i ≠ j → j ≠ k → i ≠ k → ∀ a b,
      ⁅R n i j a, R n j k b⁆ = R n i k (a * b))

/-- The existing representation keeps the exact original `h` word. -/
lemma representation_h (a : Fˣ) :
    representation n₀ R hadd hdisjoint hchain (h a) =
      EventualProduct.quotientHom (fun n => Equiv.Perm (S n)) (torusFamily n₀ R a) := by
  simp only [h, w, map_mul, representation_x, rootClass, torusFamily, weylFamily]

/-- The existing representation keeps the exact original `h02` word. -/
lemma representation_h02 (a : Fˣ) :
    representation n₀ R hadd hdisjoint hchain (h02 a) =
      EventualProduct.quotientHom (fun n => Equiv.Perm (S n)) (torus02Family n₀ R a) := by
  simp only [h02, w02, map_mul, representation_x, rootClass, torus02Family, weyl02Family]

include hadd hdisjoint hchain

/-- Use the proved ORIGINAL stable commutator identity after passing to the representation. -/
lemma representation_torusDefect_via_commutator (a b : Fˣ) :
    representation n₀ R hadd hdisjoint hchain (torusDefect a b) =
      EventualProduct.quotientHom (fun n => Equiv.Perm (S n))
        (commutatorFamily n₀ R a b) := by
  rw [← commutator_h_h02 a b, map_commutatorElement,
    representation_h n₀ R hadd hdisjoint hchain,
    representation_h02 n₀ R hadd hdisjoint hchain]
  exact (map_commutatorElement
    (EventualProduct.quotientHom (fun n => Equiv.Perm (S n))) _ _).symm

variable (T : ∀ n, Multiplicative (MilnorKTheory F 2) →* Equiv.Perm (S n))
    (hlarge : 3 ≤ n₀)
    (hcommutator : ∀ n (hn : n₀ ≤ n) (a b : Fˣ),
      finiteCommutator R n (hlarge.trans hn) a b =
        T n (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])))

include hlarge hcommutator

/-- The original Milnor map has the coefficient composite using only the finite commutator mark. -/
lemma kernelRepresentation_comp_milnorToKernel_of_commutator :
    (kernelRepresentation n₀ R hadd hdisjoint hchain).comp (milnorToKernel F) =
      coefficientMap T := by
  apply milnorAddHom_ext
  intro a
  simp only [AddMonoidHom.comp_apply, milnorToKernel_symbol]
  change Additive.ofMul
      (representation n₀ R hadd hdisjoint hchain (torusDefect (a 0) (a 1))) = _
  rw [representation_torusDefect_via_commutator]
  apply congrArg Additive.ofMul
  apply EventualProduct.quotientHom_eq_of_eventuallyEq
  filter_upwards [eventually_ge_atTop n₀] with n hn
  rw [commutatorFamily_high n₀ R n (hlarge.trans hn) hn]
  have hp : (![a 0, a 1] : Fin 2 → Fˣ) = a := by
    ext i
    fin_cases i <;> rfl
  change finiteCommutator R n _ (a 0) (a 1) =
    T n (Multiplicative.ofAdd (milnorKTupleSymbol a))
  simpa only [hp] using hcommutator n hn (a 0) (a 1)

/-- Injectivity of the ORIGINAL Milnor map from the actual finite positive commutator marking. -/
theorem milnorToKernel_injective_of_commutator_detectors
    (s₀ : ∀ n, n₀ ≤ n → S n) (coordinate : ∀ n, S n → MilnorKTheory F 2)
    (hcoordinate : ∀ n (hn : n₀ ≤ n) (m : MilnorKTheory F 2),
      coordinate n (T n (Multiplicative.ofAdd m) (s₀ n hn)) = m) :
    Function.Injective (milnorToKernel F) := by
  have hcomp := kernelRepresentation_comp_milnorToKernel_of_commutator n₀ R hadd hdisjoint
    hchain T hlarge hcommutator
  have hi := coefficientMap_injective_of_identity_states n₀ T s₀ coordinate hcoordinate
  intro a b hab
  apply hi
  have ha := DFunLike.congr_fun hcomp a
  have hb := DFunLike.congr_fun hcomp b
  rw [← ha, ← hb]
  exact congrArg (kernelRepresentation n₀ R hadd hdisjoint hchain) hab

end StableSteinberg.CommutatorDetectorTransfer

end

end
