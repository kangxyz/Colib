import Colib.KTheory.MilnorK.RationalFunctionExactness
import Colib.KTheory.MilnorK.Symbols.Transport
import Mathlib.FieldTheory.RatFunc.AsPolynomial

open Stacks.Chow MonicIrreducibleOfDegree

universe u

variable (k : Type u) [Field k]

attribute [local instance] Ideal.Quotient.field

-- The constant map is exactly the maintained field transport, not a new map.
example (n : ℕ) :
    (constantInclusion (k := k) n).toIntLinearMap =
      milnorKTheoryMap (RatFunc.C : k →+* RatFunc k) n := by
  rw [milnorKTheoryMap_eq_transport]
  change (milnorKTransport (constantsHom k) n).toIntLinearMap = _
  rw [constantsHom, RatFunc.algebraMap_comp_C]

-- Quotienting by actual constants computes the existing residue vector.
example (n : ℕ) (x : MilnorKTheory (RatFunc k) (n + 1)) :
    milnorKQuotientConstantsEquivResidues k n (Submodule.Quotient.mk x) =
      milnorKTotalResidue k n x :=
  milnorKQuotientConstantsEquivResidues_mk k n x

-- All three short exactness assertions are already supplied by Stacks.
example (n : ℕ) :
    Function.Injective (constantInclusion (k := k) (n + 1)) ∧
      (milnorKTotalResidue k n).ker = (constantInclusion (k := k) (n + 1)).range ∧
      Function.Surjective (milnorKTotalResidue k n) :=
  ⟨constantInclusion_injective (n + 1), ker_milnorKTotalResidue n,
    milnorKTotalResidue_surjective n⟩

-- The degree-one source and degree-zero residue endpoint is retained.
example (x : MilnorKTheory k 1) :
    milnorKRationalDecomposition k 0 (constantInclusion 1 x) = (x, 0) :=
  milnorKRationalDecomposition_constantInclusion k 0 x

example (z : DirectSum (MonicIrreduciblePoint k)
    (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) 0)) :
    ∃! x : MilnorKTheory (RatFunc k) 1,
      constantRetraction 1 x = 0 ∧ milnorKTotalResidue k 0 x = z :=
  existsUnique_totalResidue_lift_zero_constantRetraction k 0 z

-- No perfectness, characteristic or separability instance is required.
example (n : ℕ) (a : MilnorKTheory k (n + 1))
    (z : DirectSum (MonicIrreduciblePoint k)
      (fun p ↦ MilnorKTheory (Polynomial k ⧸ Ideal.span {poly p.2}) n)) :
    milnorKTotalResidue k n ((milnorKRationalDecomposition k n).symm (a, z)) = z :=
  milnorKTotalResidue_milnorKRationalDecomposition_symm k n a z
