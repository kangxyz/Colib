/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.FiniteTermFiltration
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula
public import Mathlib.Algebra.BigOperators.Fin

/-! # Actual finite brutal-filtration formulas in the original K-groups

Structural additivity is iterated inside a specified actual term-bound stratum.
The resulting finite product uses the original single-term layer K-maps and
literal existing group multiplication, including degree zero. No categorywide
bound, arithmetic-additivity hypothesis, or quasi-isomorphism truncation is used.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/FiniteTermKFormula.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex


noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u
namespace CategoryTheory.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The actual lower endpoint induces the identity of the original stratum K-group. -/
theorem finiteTerm_KMap_identity (a b n : ℤ) (hn : n ≤ a) (k : ℕ) :
    KMap (finiteTermTruncationExact P a b n).waldhausenExact k =
      MonoidHom.id ((ofExactCategory (fixedTermsExactStructure P a b)).K k) := by
  have he := KMap_eq_of_iso (finiteTermTruncationExact P a b n).waldhausenExact
    (IsExact.id (ofExactCategory (fixedTermsExactStructure P a b)).cof
      (ofExactCategory (fixedTermsExactStructure P a b)).weq)
    (finiteTermIdentityIso P a b n hn) k
  exact he.trans (KMap_id _ k)

/-- The actual upper endpoint induces the trivial original K-map. -/
theorem finiteTerm_KMap_zero (a b n : ℤ) (hn : b < n) (k : ℕ) :
    KMap (finiteTermTruncationExact P a b n).waldhausenExact k = 1 := by
  have he := KMap_eq_of_iso (finiteTermTruncationExact P a b n).waldhausenExact
    (zeroFunctor_isExact (ofExactCategory (fixedTermsExactStructure P a b))
      (ofExactCategory (fixedTermsExactStructure P a b))) (finiteTermZeroIso P a b n hn) k
  exact he.trans (KMap_zeroFunctor _ _ k)

/-- One actual adjacent layer gives literal multiplication of the original K-maps. -/
theorem finiteTerm_KMap_step (a b n : ℤ) (k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a b)).K k) :
    KMap (finiteTermTruncationExact P a b n).waldhausenExact k x =
      KMap (finiteTermTruncationExact P a b (n + 1)).waldhausenExact k x *
        KMap (finiteTermLayerExact P a b n).waldhausenExact k x :=
  Additivity.KMap_additivity_mul _ _ (finiteTermTransition P a b (by omega : n ≤ n + 1))
    (finiteTermProjection P a b n) (finiteTerm_isCofibrationSequence P a b n) k x

/-- Finite iteration uses the existing group operations, not a formal sum placeholder. -/
theorem finiteTerm_KMap_iterated (a b n : ℤ) (m k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a b)).K k) :
    let := Additivity.KCommGroup (ofExactCategory (fixedTermsExactStructure P a b)) k
    KMap (finiteTermTruncationExact P a b n).waldhausenExact k x =
      KMap (finiteTermTruncationExact P a b (n + (m : ℤ))).waldhausenExact k x *
        ∏ i ∈ Finset.range m, KMap (finiteTermLayerExact P a b (n + (i : ℤ))).waldhausenExact k
          x := by
  let := Additivity.KCommGroup (ofExactCategory (fixedTermsExactStructure P a b)) k
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, finiteTerm_KMap_step P a b (n + (m : ℤ)) k x]
    simp only [Finset.prod_range_succ, Nat.cast_add, Nat.cast_one, add_assoc]
    ac_rfl

/-- Every actual class in the fixed stratum is the finite product of its original
single-term layers, whenever the displayed finite interval covers that stratum. -/
theorem finiteTerm_KMap_layers (a b : ℤ) (m : ℕ) (hm : b < a + (m : ℤ)) (k : ℕ)
    (x : (ofExactCategory (fixedTermsExactStructure P a b)).K k) :
    let := Additivity.KCommGroup (ofExactCategory (fixedTermsExactStructure P a b)) k
    x = ∏ i : Fin m, KMap (finiteTermLayerExact P a b (a + (i : ℤ))).waldhausenExact k x := by
  let := Additivity.KCommGroup (ofExactCategory (fixedTermsExactStructure P a b)) k
  have h := finiteTerm_KMap_iterated P a b a m k x
  rw [finiteTerm_KMap_identity P a b a le_rfl k, finiteTerm_KMap_zero P a b _ hm k] at h
  simpa only [MonoidHom.id_apply, MonoidHom.one_apply, one_mul, Finset.prod_range] using h

end CategoryTheory.Waldhausen.GilletWaldhausen
