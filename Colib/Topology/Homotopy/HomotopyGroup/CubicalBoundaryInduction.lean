/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.CubicalUpperFaceFold
public import Colib.Topology.Homotopy.HomotopyGroup.CoordinatePermutation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite geometric side killing and genuine cubical boundary addition

Each step applies the actual lower fold and then the actual upper fold in one
lateral coordinate. The state records the current continuous cube, its actual
codimension-two constancy, the literal constancy of already killed sides, the
unchanged bottom map, unaffected original side classes, and the exact top
class ledger. No boundary-addition or orientation certificate is an input.

The terminal cube is a displayed relative homotopy from the original bottom
to its top. Coordinate permutation parity then converts the time-first ledger
to the increasing-coordinate cubical boundary formula. Finite sums are only
used in degree `m + 2`, where the original homotopy group is commutative.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/CubicalBoundaryInduction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual cubical maps,
relative homotopies, quotient multiplication, and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval
universe u

namespace Topology
variable {Z : Type u} [TopologicalSpace Z] {z : Z}

/-- The lateral parameter is the literal inverse range-cycle pullback of the
face parameter that deletes the fixed coordinate in increasing order. -/
theorem lateralGenLoop_eq_permute {n : ℕ}
    (F : C((Fin (n + 2) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 2)), F x = z)
    (k : Fin (n + 1)) (e : I) (he : e = 0 ∨ e = 1) :
    lateralGenLoop F hF k e he =
      permuteGenLoop k.cycleRange.symm (cubicalSphericalFace F hF k.succ e he) := by
  ext t
  rw [permuteGenLoop_cycleRange_symm_apply]
  change F (lateralFaceParameter k e t) =
    F (k.succ.insertNth e (Fin.cons (t k) (k.removeNth t)))
  simp only [Fin.insertNth_succ_cons, Fin.insertNth_removeNth, lateralFaceParameter]

/-- The explicit lateral reparametrization has exactly the time-first sign. -/
theorem lateralGenLoop_additiveClass {n : ℕ}
    (F : C((Fin (n + 2) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 2)), F x = z)
    (k : Fin (n + 1)) (e : I) (he : e = 0 ∨ e = 1) :
    Additive.ofMul (cubicalClass (lateralGenLoop F hF k e he)) =
      ((-1 : ℤ) ^ k.val) •
        Additive.ofMul (cubicalClass (cubicalSphericalFace F hF k.succ e he)) := by
  rw [lateralGenLoop_eq_permute]
  exact permuteGenLoop_cycleRange_symm_additiveClass k _

/-- Lower folding preserves the class of every other original lateral face,
by the actual face-relative homotopy pulled back along the same permutation. -/
theorem lateralGenLoop_fold_other_class {n : ℕ}
    (F : C((Fin (n + 2) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 2)), F x = z)
    (k l : Fin (n + 1)) (hlk : l ≠ k) (e : I) (he : e = 0 ∨ e = 1) :
    cubicalClass (lateralGenLoop (foldContinuousCube F 0 k.succ)
      (foldContinuousCube_codimTwo F hF 0 k.succ (Fin.succ_ne_zero k).symm) l e he) =
      cubicalClass (lateralGenLoop F hF l e he) := by
  rw [lateralGenLoop_eq_permute, lateralGenLoop_eq_permute]
  symm
  exact Quotient.sound ⟨permuteGenLoopHomotopy l.cycleRange.symm
    (otherFaceFoldHomotopy F hF 0 k.succ l.succ (Fin.succ_ne_zero k).symm
      (Fin.succ_ne_zero l) (fun h ↦ hlk (Fin.succ_inj.mp h)) e he)⟩

/-- Upper folding preserves every other lateral class by its actual relative homotopy. -/
theorem lateralGenLoop_upperFold_other_class {n : ℕ}
    (F : C((Fin (n + 2) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 2)), F x = z)
    (k l : Fin (n + 1)) (hlk : l ≠ k) (e : I) (he : e = 0 ∨ e = 1) :
    cubicalClass (lateralGenLoop (foldUpperContinuousCube F 0 k.succ)
      (foldUpperContinuousCube_codimTwo F hF 0 k.succ (Fin.succ_ne_zero k).symm)
      l e he) = cubicalClass (lateralGenLoop F hF l e he) := by
  rw [lateralGenLoop_eq_permute, lateralGenLoop_eq_permute]
  symm
  exact Quotient.sound ⟨permuteGenLoopHomotopy l.cycleRange.symm
    (otherFaceUpperFoldHomotopy F hF 0 k.succ l.succ (Fin.succ_ne_zero k).symm
      (Fin.succ_ne_zero l) (fun h ↦ hlk (Fin.succ_inj.mp h)) e he)⟩

variable {m : ℕ}

/-- The exact contribution of a lateral coordinate to the folded top class. -/
def cubicalLateralContribution (F : C((Fin (m + 3) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), F x = z) (k : Fin (m + 2)) :
    Additive (HomotopyGroup.Pi (m + 2) Z z) :=
  Additive.ofMul (cubicalClass (lateralGenLoop F hF k 0 (Or.inl rfl))) -
    Additive.ofMul (cubicalClass (lateralGenLoop F hF k 1 (Or.inr rfl)))

/-- A finite stage consists of an actual folded cube and proved geometric and
class invariants, relative to one original cube and the already killed sides. -/
structure CubicalKillState (F : C((Fin (m + 3) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), F x = z)
    (s : Finset (Fin (m + 2))) where
  /-- The current full continuous cube. -/
  cube : C((Fin (m + 3) → I), Z)
  /-- Its actual codimension-two boundary is still based. -/
  based : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), cube x = z
  /-- Both sides of every selected coordinate are literally constant. -/
  killed : ∀ k ∈ s, ∀ x, x k.succ = 0 ∨ x k.succ = 1 → cube x = z
  /-- The original bottom loop is preserved as a map. -/
  bottom : bottomGenLoop cube based = bottomGenLoop F hF
  /-- A not-yet-killed side retains its original homotopy class. -/
  untouched : ∀ k ∉ s, ∀ (e : I) (he : e = 0 ∨ e = 1),
    cubicalClass (lateralGenLoop cube based k e he) =
      cubicalClass (lateralGenLoop F hF k e he)
  /-- The exact additive ledger of the current top. -/
  ledger : Additive.ofMul (cubicalClass (topGenLoop cube based)) =
    Additive.ofMul (cubicalClass (topGenLoop F hF)) +
      ∑ k ∈ s, cubicalLateralContribution F hF k

namespace CubicalKillState
variable {F : C((Fin (m + 3) → I), Z)}
variable {hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), F x = z}
variable {s : Finset (Fin (m + 2))}

/-- Before folding, the state is the original cube with an empty ledger. -/
def initial (F : C((Fin (m + 3) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), F x = z) :
    CubicalKillState F hF ∅ where
  cube := F
  based := hF
  killed := by simp
  bottom := rfl
  untouched := by intros; rfl
  ledger := by simp

/-- One induction step kills both sides of a new coordinate by the two actual
folds, while proving each of the retained invariants from their geometric APIs. -/
def insert (P : CubicalKillState F hF s) (k : Fin (m + 2)) (hk : k ∉ s) :
    CubicalKillState F hF (insert k s) := by
  let L := foldContinuousCube P.cube 0 k.succ
  have hL : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), L x = z :=
    foldContinuousCube_codimTwo P.cube P.based 0 k.succ (Fin.succ_ne_zero k).symm
  let U := foldUpperContinuousCube L 0 k.succ
  have hU : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), U x = z :=
    foldUpperContinuousCube_codimTwo L hL 0 k.succ (Fin.succ_ne_zero k).symm
  have hLzero (x : Fin (m + 3) → I) (hx : x k.succ = 0) : L x = z := by
    have h := foldContinuousCube_lower_side P.cube P.based 0 k.succ
      (Fin.succ_ne_zero k).symm (k.succ.removeNth x)
    simpa only [Fin.insertNth_removeNth, ← hx, Function.update_eq_self] using h
  refine ⟨U, hU, ?_, ?_, ?_, ?_⟩
  · intro l hl x hx
    rcases Finset.mem_insert.mp hl with hlk | hl
    · subst l
      rcases hx with hx | hx
      · change L (cubeUpperFaceFold 0 k.succ 1 x) = z
        rw [cubeUpperFaceFold_left 0 k.succ (Fin.succ_ne_zero k).symm 1 x hx]
        exact hLzero x hx
      · have h := foldUpperContinuousCube_upper_side L hL 0 k.succ
          (Fin.succ_ne_zero k).symm (k.succ.removeNth x)
        simpa only [Fin.insertNth_removeNth, ← hx, Function.update_eq_self] using h
    · have hlk : l ≠ k := by intro h; subst l; exact hk hl
      change P.cube (cubeFaceFold 0 k.succ 1
        (cubeUpperFaceFold 0 k.succ 1 x)) = z
      apply P.killed l hl
      simpa only [cubeFaceFold_other 0 k.succ l.succ (Fin.succ_ne_zero l)
          (fun h ↦ hlk (Fin.succ_inj.mp h)),
        cubeUpperFaceFold_other 0 k.succ l.succ (Fin.succ_ne_zero l)
          (fun h ↦ hlk (Fin.succ_inj.mp h))] using hx
  · exact (bottomGenLoop_upperFold L hL k).trans
      ((bottomGenLoop_fold P.cube P.based k).trans P.bottom)
  · intro l hl e he
    have hls : l ∉ s := fun h ↦ hl (Finset.mem_insert_of_mem h)
    have hlk : l ≠ k := by
      intro h
      subst l
      exact hl (Finset.mem_insert_self k s)
    exact (lateralGenLoop_upperFold_other_class L hL k l hlk e he).trans
      ((lateralGenLoop_fold_other_class P.cube P.based k l hlk e he).trans
        (P.untouched l hls e he))
  · change Additive.ofMul (cubicalClass (topGenLoop
        (foldUpperContinuousCube L 0 k.succ) hU)) = _
    rw [topGenLoop_upperFold_class L hL k, ofMul_mul, ofMul_inv]
    rw [lateralGenLoop_fold_upper P.cube P.based k,
      topGenLoop_fold_class P.cube P.based k, ofMul_mul]
    rw [P.untouched k hk 1 (Or.inr rfl), P.untouched k hk 0 (Or.inl rfl), P.ledger]
    rw [Finset.sum_insert hk]
    unfold cubicalLateralContribution
    abel

end CubicalKillState

/-- Every finite set of lateral coordinates can genuinely be killed while
retaining the stated actual-map and original-class invariants. -/
theorem exists_cubicalKillState (F : C((Fin (m + 3) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), F x = z)
    (s : Finset (Fin (m + 2))) : Nonempty (CubicalKillState F hF s) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨CubicalKillState.initial F hF⟩
  | @insert k s hk ih =>
    obtain ⟨P⟩ := ih
    exact ⟨P.insert k hk⟩

/-- The terminal full cube is an actual boundary-relative homotopy, so its
ledger equates the original top plus every side contribution to the bottom. -/
theorem cubical_lateral_ledger (F : C((Fin (m + 3) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), F x = z) :
    Additive.ofMul (cubicalClass (topGenLoop F hF)) +
      ∑ k : Fin (m + 2), cubicalLateralContribution F hF k =
        Additive.ofMul (cubicalClass (bottomGenLoop F hF)) := by
  obtain ⟨P⟩ := exists_cubicalKillState F hF Finset.univ
  have hends : cubicalClass (bottomGenLoop P.cube P.based) =
      cubicalClass (topGenLoop P.cube P.based) :=
    Quotient.sound ⟨allSidesConstantHomotopy P.cube P.based
      (fun k x hx ↦ P.killed k (Finset.mem_univ k) x hx)⟩
  rw [P.bottom] at hends
  exact P.ledger.symm.trans (congrArg Additive.ofMul hends.symm)

/-- Genuine signed cubical boundary addition in the original homotopy group.
Every face deletes its fixed coordinate and retains the others in increasing
order; the parity is proved from actual coordinate permutations. -/
theorem cubical_signed_boundary_addition (F : C((Fin (m + 3) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (m + 3)), F x = z) :
    ∑ j : Fin (m + 3), ((-1 : ℤ) ^ j.val) •
      (Additive.ofMul (cubicalClass (cubicalSphericalFace F hF j 1 (Or.inr rfl))) -
        Additive.ofMul (cubicalClass (cubicalSphericalFace F hF j 0 (Or.inl rfl)))) =
      (0 : Additive (HomotopyGroup.Pi (m + 2) Z z)) := by
  have h := cubical_lateral_ledger F hF
  have hterm (k : Fin (m + 2)) :
      ((-1 : ℤ) ^ k.succ.val) •
        (Additive.ofMul (cubicalClass
          (cubicalSphericalFace F hF k.succ 1 (Or.inr rfl))) -
        Additive.ofMul (cubicalClass
          (cubicalSphericalFace F hF k.succ 0 (Or.inl rfl)))) =
        cubicalLateralContribution F hF k := by
    unfold cubicalLateralContribution
    rw [lateralGenLoop_additiveClass, lateralGenLoop_additiveClass]
    simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, smul_sub]
    abel
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul]
  simp_rw [hterm]
  change Additive.ofMul (cubicalClass (topGenLoop F hF)) -
      Additive.ofMul (cubicalClass (bottomGenLoop F hF)) +
        ∑ k : Fin (m + 2), cubicalLateralContribution F hF k = 0
  rw [← h]
  abel

end Topology
