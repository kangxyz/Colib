/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Symbols.SplitMixed
public import Colib.KTheory.MilnorK.Symbols.Surjectivity
public import Colib.KTheory.MilnorK.Symbols.Transport
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.AdjoinRoot
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.LowDegreeRepresentative

/-!
# Finite native polynomial witnesses for mixed-symbol generation

The representatives are Stacks' `polyRep`, in the literal polynomial quotient.
The class is expressed as a finite sum of existing homogeneous tuple symbols,
not as an element of another presentation. Its witnesses are chosen before
any coefficient field or actual irreducible factor is supplied.

The native factor map is Mathlib's `AdjoinRoot.map`. Since `AdjoinRoot p` is
itself the quotient by `Ideal.span {p}`, no quotient equivalence or model
adapter is introduced. The strict representative bound is kept literally;
no source filtration with a shifted index is copied.

The finite-witness argument adapts `Aglib.KTheory.MilnorK.SplitPolynomialGeneration`,
lines 108-232, at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`. Its
free-symbol quotient and root-map wrapper are replaced by existing native APIs.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open Polynomial

universe u v

/-- Every homogeneous class is a finite integer combination of its native
ordered tuple symbols. This does not introduce a free-symbol quotient. -/
theorem exists_finsupp_milnorKTupleSymbol {E : Type u} [Field E] (n : ℕ)
    (x : MilnorKTheory E n) :
    ∃ c : (Fin n → Eˣ) →₀ ℤ, c.sum (fun a z => z • milnorKTupleSymbol a) = x := by
  let f := Finsupp.linearCombination ℤ (fun a : Fin n → Eˣ => milnorKTupleSymbol a)
  have hf : Function.Surjective f.toAddMonoidHom := by
    apply milnorKTheory_surjective_of_tupleSymbol
    intro a
    refine ⟨Finsupp.single a 1, ?_⟩
    simp [f]
  obtain ⟨c, hc⟩ := hf x
  exact ⟨c, hc⟩

variable {k : Type u} [Field k] (p : k[X]) (hp : p.Monic) [Fact (Irreducible p)]

/-- The actual native coefficient-factor map sends a reduced representative
to the evaluation of its coefficient image at the actual target root. -/
theorem aeval_map_polyRep_eq_adjoinRoot_map {L : Type v} [Field L]
    (φ : k →+* L) (q : L[X]) [Fact (Irreducible q)] (hq : q ∣ p.map φ)
    (a : (AdjoinRoot p)ˣ) :
    aeval (AdjoinRoot.root q)
        ((polyRep hp (Fact.out : Irreducible p).ne_one a).map φ) =
      AdjoinRoot.map φ p q hq (a : AdjoinRoot p) := by
  have hmk (r : k[X]) :
      AdjoinRoot.map φ p q hq (AdjoinRoot.mk p r) = AdjoinRoot.mk q (r.map φ) := by
    change r.eval₂ ((AdjoinRoot.of q).comp φ) (AdjoinRoot.root q) =
      AdjoinRoot.mk q (r.map φ)
    rw [← Polynomial.eval₂_map]
    exact AdjoinRoot.aeval_eq (r.map φ)
  rw [AdjoinRoot.aeval_eq, ← hmk]
  congr 1
  exact mk_polyRep hp (Fact.out : Irreducible p).ne_one a

/-- Splitting the native reduced representatives of one tuple makes its
actual image mixed, at every literal irreducible coefficient factor. Neither
monicity of that factor nor a prime-degree hypothesis is required. -/
theorem restricted_milnorKTupleSymbol_mem_mixedSpan_of_polyRep_splits
    {L : Type v} [Field L] (φ : k →+* L) (q : L[X]) [Fact (Irreducible q)]
    (hq : q ∣ p.map φ) (m : ℕ) (a : Fin (m + 1) → (AdjoinRoot p)ˣ)
    (hsplit : ∀ i,
      ((polyRep hp (Fact.out : Irreducible p).ne_one (a i)).map φ).Splits) :
    milnorKTheoryMap (AdjoinRoot.map φ p q hq) (m + 1) (milnorKTupleSymbol a) ∈
      milnorKMixedSpan (algebraMap L (AdjoinRoot q)) m := by
  let r : Fin (m + 1) → L[X] := fun i =>
    (polyRep hp (Fact.out : Irreducible p).ne_one (a i)).map φ
  have heval (i : Fin (m + 1)) :
      aeval (AdjoinRoot.root q) (r i) = AdjoinRoot.map φ p q hq (a i) :=
    aeval_map_polyRep_eq_adjoinRoot_map p hp φ q hq (a i)
  have hne (i : Fin (m + 1)) : aeval (AdjoinRoot.root q) (r i) ≠ 0 := by
    rw [heval]
    exact (Units.map (AdjoinRoot.map φ p q hq).toMonoidHom (a i)).ne_zero
  have htuple :
      (fun i => Units.mk0 (aeval (AdjoinRoot.root q) (r i)) (hne i)) =
        Units.map (AdjoinRoot.map φ p q hq).toMonoidHom ∘ a := by
    funext i
    apply Units.ext
    exact heval i
  rw [milnorKTheoryMap_tupleSymbol, ← htuple]
  exact milnorKTupleSymbol_aeval_mem_mixedSpan (AdjoinRoot.root q) m r hsplit hne

include hp

/-- A finite family of native reduced representatives is chosen before all
coefficient fields and actual factors. Splitting that family makes the
original restricted class mixed, in independent field universes. -/
@[colib_tag "COL-0227",
  colib_ref "aglib_principal_euler_pin" "KTheory/MilnorK/SplitPolynomialGeneration.lean:170-212"
    "adaptation"
    "One finite native polyRep family before all coefficient fields and actual factors"]
theorem exists_finite_milnorK_mixed_splitting_witness (m : ℕ)
    (x : MilnorKTheory (AdjoinRoot p) (m + 1)) :
    ∃ s : Finset k[X],
      (∀ r ∈ s, r ≠ 0 ∧ r.natDegree < p.natDegree) ∧
      ∀ (L : Type v) [Field L] (φ : k →+* L) (q : L[X]) [Fact (Irreducible q)]
        (hq : q ∣ p.map φ),
        (∀ r ∈ s, (r.map φ).Splits) →
        milnorKTheoryMap (AdjoinRoot.map φ p q hq) (m + 1) x ∈
          milnorKMixedSpan (algebraMap L (AdjoinRoot q)) m := by
  classical
  obtain ⟨z, rfl⟩ := exists_finsupp_milnorKTupleSymbol (m + 1) x
  let s : Finset k[X] := z.support.biUnion fun a =>
    Finset.univ.image fun i => polyRep hp (Fact.out : Irreducible p).ne_one (a i)
  have hmem (a : Fin (m + 1) → (AdjoinRoot p)ˣ) (ha : a ∈ z.support)
      (i : Fin (m + 1)) : polyRep hp (Fact.out : Irreducible p).ne_one (a i) ∈ s :=
    Finset.mem_biUnion.mpr
      ⟨a, ha, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  refine ⟨s, ?_, ?_⟩
  · intro r hr
    obtain ⟨a, _, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨polyRep_ne_zero hp (Fact.out : Irreducible p).ne_one (a i),
      natDegree_polyRep_lt hp (Fact.out : Irreducible p).ne_one (a i)⟩
  · intro L _ φ q _ hq hsplit
    simp only [Finsupp.sum, map_sum, LinearMap.map_smul]
    apply Submodule.sum_mem
    intro a ha
    apply Submodule.smul_mem
    exact restricted_milnorKTupleSymbol_mem_mixedSpan_of_polyRep_splits p hp
      φ q hq m a (fun i => hsplit _ (hmem a ha i))

/-- The same finite witnesses produce an explicit signed mixed-symbol
expansion after every coefficient map where those witnesses split. -/
@[colib_tag "COL-0227",
  colib_ref "aglib_principal_euler_pin" "KTheory/MilnorK/SplitPolynomialGeneration.lean:216-231"
    "adaptation"
    "Literal signed expansions under native AdjoinRoot.map in independent universes"]
theorem exists_finite_milnorK_reduced_mixed_expansion (m : ℕ)
    (x : MilnorKTheory (AdjoinRoot p) (m + 1)) :
    ∃ s : Finset k[X],
      (∀ r ∈ s, r ≠ 0 ∧ r.natDegree < p.natDegree) ∧
      ∀ (L : Type v) [Field L] (φ : k →+* L) (q : L[X]) [Fact (Irreducible q)]
        (hq : q ∣ p.map φ),
        (∀ r ∈ s, (r.map φ).Splits) →
        ∃ c : ((Fin m → Lˣ) × (AdjoinRoot q)ˣ) →₀ ℤ,
          (c.sum fun ab z => z • milnorKTupleSymbol
            (Fin.snoc (Units.map (algebraMap L (AdjoinRoot q)).toMonoidHom ∘ ab.1) ab.2)) =
              milnorKTheoryMap (AdjoinRoot.map φ p q hq) (m + 1) x := by
  obtain ⟨s, hs, hgen⟩ := exists_finite_milnorK_mixed_splitting_witness.{u, v} p hp m x
  refine ⟨s, hs, ?_⟩
  intro L _ φ q _ hq hsplit
  exact milnorKMixedSpan_exists_finsupp (algebraMap L (AdjoinRoot q)) m _
    (hgen L φ q hq hsplit)

end Stacks.Chow
