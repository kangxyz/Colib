/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.BlockOperations
public import Colib.GroupTheory.StableGeneralLinear.ElementaryQuotient

/-!
Implementation provenance: `Quillen/Algebra/Group/StableQuotientInvariance.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Stable quotient invariance under bases and block sums

These identities concern the actual stable elementary quotient over any ring.
They retain finite ranks as labels and do not assume invariant basis number.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w x
namespace StableGeneralLinear
open Matrix.GeneralLinearGroup
variable (R : Type u) [Ring R]

/-- The original finite-stage matrix class in the stable elementary quotient. -/
def finiteClass (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R →* ElementaryQuotient R :=
  (quotientMap R).comp (of R n)

/-- Inner changes of basis do not change the original finite matrix class. -/
lemma finiteClass_conjugate (n : ℕ) (g p : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteClass R n (p * g * p⁻¹) = finiteClass R n g := by
  simp [map_mul, map_inv, mul_comm]

/-- Appending an identity block does not change the finite matrix class. -/
lemma finiteClass_transition {n m : ℕ} (h : n ≤ m) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteClass R m (transition R n m h g) = finiteClass R n g := by
  change quotientMap R (of R m (transition R n m h g)) = _
  rw [of_transition]
  rfl

/-- Permuting a labelled finite basis leaves its actual stable quotient class unchanged. -/
lemma finiteClass_reindex (n : ℕ) (e : Fin n ≃ Fin n) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteClass R n (Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv g) =
      finiteClass R n g := by
  rw [reindex_eq_conjugate, finiteClass_conjugate]

/-- The class is independent of enumerations of the same finite coordinate set. -/
lemma finiteClass_enumeration {I : Type v} [Fintype I] [DecidableEq I]
    {n m : ℕ} (e : I ≃ Fin n) (f : I ≃ Fin m) (g : (Matrix I I R)ˣ) :
    finiteClass R n ((Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv) g) =
      finiteClass R m ((Units.mapEquiv (Matrix.reindexRingEquiv R f).toMulEquiv) g) := by
  have hn : n = m := by
    simpa using Fintype.card_congr (e.symm.trans f)
  subst m
  have h := finiteClass_reindex R n (e.symm.trans f)
    (Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv g)
  rw [reindex_trans] at h
  have he : e.trans (e.symm.trans f) = f := by ext i; simp
  rw [he] at h
  exact h.symm

/-- The class of a block matrix with an identity right block is the original class. -/
lemma finiteClass_blockSum_one (n m : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteClass R (n + m) ((Units.mapEquiv (Matrix.reindexRingEquiv R finSumFinEquiv).toMulEquiv)
      (blockSum g (1 : Matrix.GeneralLinearGroup (Fin m) R))) = finiteClass R n g := by
  have ht : transition R n (n + m) (Nat.le_add_right n m) g =
      (Units.mapEquiv (Matrix.reindexRingEquiv R finSumFinEquiv).toMulEquiv)
        (blockSum g (1 : Matrix.GeneralLinearGroup (Fin m) R)) := by
    apply Units.ext
    exact transition_val_fromBlocks R n m g
  rw [← ht]
  exact finiteClass_transition R _ g

/-- Appending an identity on the left also preserves the original stable quotient class. -/
lemma finiteClass_one_blockSum (n m : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteClass R (m + n) ((Units.mapEquiv (Matrix.reindexRingEquiv R finSumFinEquiv).toMulEquiv)
      (blockSum (1 : Matrix.GeneralLinearGroup (Fin m) R) g)) = finiteClass R n g := by
  rw [← reindex_blockSum_swap R g (1 : Matrix.GeneralLinearGroup (Fin m) R), reindex_trans]
  exact (finiteClass_enumeration R
    ((Equiv.sumComm (Fin n) (Fin m)).trans finSumFinEquiv)
    finSumFinEquiv (blockSum g (1 : Matrix.GeneralLinearGroup (Fin m) R))).trans
      (finiteClass_blockSum_one R n m g)

/-- The original stable quotient converts block direct sum to multiplication. -/
lemma finiteClass_blockSum (n m : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (h : Matrix.GeneralLinearGroup (Fin m) R) :
    finiteClass R (n + m) ((Units.mapEquiv (Matrix.reindexRingEquiv R finSumFinEquiv).toMulEquiv)
      (blockSum g h)) = finiteClass R n g * finiteClass R m h := by
  have hb : blockSum g h =
      blockSum g (1 : Matrix.GeneralLinearGroup (Fin m) R) *
        blockSum (1 : Matrix.GeneralLinearGroup (Fin n) R) h := by
    rw [← blockSum_mul, mul_one, one_mul]
  rw [hb, map_mul, map_mul, finiteClass_blockSum_one, finiteClass_one_blockSum]

/-- Isomorphic free modules give the same automorphism class, even with unequal rank labels. -/
theorem finiteClass_rectangular_conjugate {n m : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) (h : Matrix.GeneralLinearGroup (Fin m) R)
    (a : Matrix (Fin n) (Fin m) R) (b : Matrix (Fin m) (Fin n) R)
    (hab : a * b = 1) (hba : b * a = 1) (hconj : a * h.val = g.val * a) :
    finiteClass R n g = finiteClass R m h := by
  let w := rectangularSwap R a b hab hba
  have hw : w * blockSum (1 : Matrix.GeneralLinearGroup (Fin n) R) h =
      blockSum g (1 : Matrix.GeneralLinearGroup (Fin m) R) * w := by
    apply Units.ext
    change Matrix.fromBlocks 0 a b 0 * Matrix.fromBlocks 1 0 0 h.val =
      Matrix.fromBlocks g.val 0 0 1 * Matrix.fromBlocks 0 a b 0
    simp [Matrix.fromBlocks_multiply, hconj]
  let c := (finiteClass R (n + m)).comp
    (Units.mapEquiv
      (Matrix.reindexRingEquiv R (finSumFinEquiv (m := n) (n := m))).toMulEquiv).toMonoidHom
  have hc := congrArg c hw
  change c (w * blockSum (1 : Matrix.GeneralLinearGroup (Fin n) R) h) =
    c (blockSum g (1 : Matrix.GeneralLinearGroup (Fin m) R) * w) at hc
  rw [map_mul, map_mul] at hc
  have hh : c (blockSum (1 : Matrix.GeneralLinearGroup (Fin n) R) h) = finiteClass R m h :=
    finiteClass_one_blockSum R m n h
  have hg : c (blockSum g (1 : Matrix.GeneralLinearGroup (Fin m) R)) = finiteClass R n g :=
    finiteClass_blockSum_one R n m g
  rw [hh, hg, mul_comm (finiteClass R n g)] at hc
  exact (mul_left_cancel hc).symm

end StableGeneralLinear
