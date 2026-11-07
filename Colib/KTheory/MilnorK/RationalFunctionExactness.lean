/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.MilnorExactSequence

/-!
# Native rational-function Milnor decomposition

The native total residue induces an equivalence from the quotient by constants
to the native direct sum of residue-field Milnor groups. Together with the
existing constant retraction, it gives an equivalence from the rational-function
Milnor group to the product of constants and that direct sum.

The constant inclusion, constant retraction, total residue, point indexing and
residue fields are precisely those already defined in Stacks. Their existing
injectivity, kernel and surjectivity theorems are reused, not reproved.

The quotient endpoint adapts `Aglib.KTheory.MilnorK.RationalExactness` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The product decomposition additionally
retains Stacks' specific constant retraction. No equality with Aglib's separate
origin-specialization retraction is asserted. Every positive source degree is
covered, including degree-zero residue groups, over an arbitrary field.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

variable (k : Type u) [Field k]

attribute [local instance] Ideal.Quotient.field

/-- The native total residue kills the actual inclusion of constants. -/
@[simp] theorem milnorKTotalResidue_constantInclusion (n : ℕ)
    (x : MilnorKTheory k (n + 1)) :
    milnorKTotalResidue k n (constantInclusion (n + 1) x) = 0 := by
  apply AddMonoidHom.mem_ker.mp
  rw [ker_milnorKTotalResidue]
  exact ⟨x, rfl⟩

/-- On the actual residue kernel, the existing retraction recovers the unique
constant class whose inclusion is the given rational-function class. -/
theorem constantInclusion_constantRetraction_of_totalResidue_eq_zero (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) (hx : milnorKTotalResidue k n x = 0) :
    constantInclusion (n + 1) (constantRetraction (n + 1) x) = x := by
  have hx' : x ∈ (constantInclusion (k := k) (n + 1)).range := by
    rw [← ker_milnorKTotalResidue]
    exact hx
  obtain ⟨a, rfl⟩ := hx'
  rw [constantRetraction_constantInclusion]

private theorem ker_totalResidue_linear (n : ℕ) :
    LinearMap.ker (milnorKTotalResidue k n).toIntLinearMap =
      LinearMap.range (constantInclusion (k := k) (n + 1)).toIntLinearMap := by
  ext x
  change x ∈ (milnorKTotalResidue k n).ker ↔
    x ∈ (constantInclusion (k := k) (n + 1)).range
  rw [ker_milnorKTotalResidue]

/-- The quotient by constants is the existing direct sum of finitely supported
native residue-field classes, via the original total residue. -/
def milnorKQuotientConstantsEquivResidues (n : ℕ) :
    (MilnorKTheory (RatFunc k) (n + 1) ⧸
      LinearMap.range (constantInclusion (k := k) (n + 1)).toIntLinearMap) ≃ₗ[ℤ]
      DirectSum (MonicIrreduciblePoint k)
        (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n) :=
  (Submodule.quotEquivOfEq _ _ (ker_totalResidue_linear k n).symm).trans
    ((milnorKTotalResidue k n).toIntLinearMap.quotKerEquivOfSurjective
      (milnorKTotalResidue_surjective n))

/-- The quotient equivalence computes the original total residue, without a
replacement map or a change of residue-field coordinates. -/
@[simp] theorem milnorKQuotientConstantsEquivResidues_mk (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    milnorKQuotientConstantsEquivResidues k n (Submodule.Quotient.mk x) =
      milnorKTotalResidue k n x := by
  simp only [milnorKQuotientConstantsEquivResidues, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The original retraction and total residue jointly give a bijection. The
surjectivity proof corrects a residue lift by its actual constant component. -/
theorem bijective_constantRetraction_totalResidue (n : ℕ) :
    Function.Bijective (fun x : MilnorKTheory (RatFunc k) (n + 1) ↦
      (constantRetraction (n + 1) x, milnorKTotalResidue k n x)) := by
  constructor
  · intro x y h
    have hret := congrArg Prod.fst h
    have hres := congrArg Prod.snd h
    have hz : milnorKTotalResidue k n (x - y) = 0 := by
      rw [map_sub, hres, sub_self]
    have hrec := constantInclusion_constantRetraction_of_totalResidue_eq_zero k n (x - y) hz
    have hr : constantRetraction (n + 1) (x - y) = 0 := by
      rw [map_sub, hret, sub_self]
    rw [hr, map_zero] at hrec
    exact sub_eq_zero.mp hrec.symm
  · rintro ⟨a, z⟩
    obtain ⟨x, hx⟩ := milnorKTotalResidue_surjective n z
    refine ⟨x + constantInclusion (n + 1) (a - constantRetraction (n + 1) x), ?_⟩
    apply Prod.ext
    · change constantRetraction (n + 1)
        (x + constantInclusion (n + 1) (a - constantRetraction (n + 1) x)) = a
      rw [map_add, constantRetraction_constantInclusion, add_sub, add_sub_cancel_left]
    · change milnorKTotalResidue k n
        (x + constantInclusion (n + 1) (a - constantRetraction (n + 1) x)) = z
      rw [map_add, milnorKTotalResidue_constantInclusion, add_zero, hx]

/-- The native rational-function Milnor group is the product of its actual
constant component and its actual total finite residue vector. -/
def milnorKRationalDecomposition (n : ℕ) :
    MilnorKTheory (RatFunc k) (n + 1) ≃ₗ[ℤ]
      MilnorKTheory k (n + 1) × DirectSum (MonicIrreduciblePoint k)
        (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n) :=
  LinearEquiv.ofBijective
    ((constantRetraction (k := k) (n + 1)).toIntLinearMap.prod
      (milnorKTotalResidue k n).toIntLinearMap)
    (bijective_constantRetraction_totalResidue k n)

/-- Both components of the decomposition are the original native maps. -/
@[simp] theorem milnorKRationalDecomposition_apply (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    milnorKRationalDecomposition k n x =
      (constantRetraction (n + 1) x, milnorKTotalResidue k n x) := rfl

/-- A constant class has itself as first component and zero finite residues. -/
@[simp] theorem milnorKRationalDecomposition_constantInclusion (n : ℕ)
    (x : MilnorKTheory k (n + 1)) :
    milnorKRationalDecomposition k n (constantInclusion (n + 1) x) = (x, 0) := by
  rw [milnorKRationalDecomposition_apply, constantRetraction_constantInclusion,
    milnorKTotalResidue_constantInclusion]

/-- The inverse decomposition has the prescribed constant component. -/
@[simp] theorem constantRetraction_milnorKRationalDecomposition_symm (n : ℕ)
    (a : MilnorKTheory k (n + 1))
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n)) :
    constantRetraction (n + 1) ((milnorKRationalDecomposition k n).symm (a, z)) = a :=
  congrArg Prod.fst ((milnorKRationalDecomposition k n).apply_symm_apply (a, z))

/-- The inverse decomposition has the prescribed actual residue vector. -/
@[simp] theorem milnorKTotalResidue_milnorKRationalDecomposition_symm (n : ℕ)
    (a : MilnorKTheory k (n + 1))
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n)) :
    milnorKTotalResidue k n ((milnorKRationalDecomposition k n).symm (a, z)) = z :=
  congrArg Prod.snd ((milnorKRationalDecomposition k n).apply_symm_apply (a, z))

/-- Every finite residue vector has a unique lift with zero native constant
retraction. This includes residue vectors in Milnor degree zero. -/
theorem existsUnique_totalResidue_lift_zero_constantRetraction (n : ℕ)
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n)) :
    ∃! x : MilnorKTheory (RatFunc k) (n + 1),
      constantRetraction (n + 1) x = 0 ∧ milnorKTotalResidue k n x = z := by
  refine ⟨(milnorKRationalDecomposition k n).symm (0, z), ⟨?_, ?_⟩, ?_⟩
  · exact constantRetraction_milnorKRationalDecomposition_symm k n 0 z
  · exact milnorKTotalResidue_milnorKRationalDecomposition_symm k n 0 z
  · intro x hx
    apply (milnorKRationalDecomposition k n).injective
    rw [LinearEquiv.apply_symm_apply, milnorKRationalDecomposition_apply, hx.1, hx.2]

end Stacks.Chow
