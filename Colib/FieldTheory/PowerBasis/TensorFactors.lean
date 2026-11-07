/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Charpoly.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.RingTheory.AdjoinRoot
public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.GaloisDegree

/-!
# Literal factors and root coordinates of an actual tensor decomposition

Given a native power basis of `E/F` and an actual equivalence
`K ⊗[F] E ≃ₐ[K] Π j, D j`, the actual coordinate of its generator gives a native
power basis of every existing `D j`. Its minimal polynomial is a literal monic
factor, and the complete family multiplies to the coefficient image of the
original minimal polynomial. Normalized factors retain every occurrence; the
separable case gives an actual index bijection and multiplicity one.

The quotient equivalences send each literal root to its specified coordinate.
Their whole coefficient-map squares are proved as equalities of ring maps, not
assumed from the existence of abstract field equivalences. No alternative field,
tensor, norm, factor structure, or persistent coordinate-map definition is added.
The generator theorem is invoked directly from pinned Stacks.
-/

@[expose] public noncomputable section

open Polynomial UniqueFactorizationMonoid
open scoped TensorProduct

namespace PowerBasis

variable {F K E : Type*} [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra F E]
  {ι : Type*} {D : ι → Type*} [∀ j, Field (D j)] [∀ j, Algebra K (D j)]

/-- Every actual product coordinate has a native power basis with the actual tensor root.
Neither finiteness of the index type nor separability is needed for this assertion. -/
theorem exists_powerBasis_of_tensorProductPiEquiv
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (j : ι) :
    ∃ b : PowerBasis K (D j), b.gen = ε (1 ⊗ₜ[F] pb.gen) j := by
  classical
  let f : (K ⊗[F] E) →ₐ[K] D j := (Pi.evalAlgHom K D j).comp ε.toAlgHom
  have hf : Function.Surjective f := (Function.surjective_eval j).comp ε.surjective
  let : Module.Finite K (K ⊗[F] E) := Module.Finite.of_basis (pb.basis.baseChange K)
  let : Module.Finite K (D j) := Module.Finite.of_surjective f.toLinearMap hf
  have hgen : Algebra.adjoin K {f (1 ⊗ₜ[F] pb.gen)} = ⊤ :=
    IsDiscreteValuationRing.adjoin_eq_top_of_surjective_tensorProduct_factor
      F K E (D j) pb.gen pb.adjoin_gen_eq_top f hf
  exact ⟨PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite K _) hgen, rfl⟩

variable [Fintype ι]

/-- The minimal polynomials of the actual factor coordinates multiply to the literal
coefficient image of the original minimal polynomial. No separability is required. -/
theorem map_minpoly_eq_prod_tensorProductPiEquiv
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) :
    (minpoly F pb.gen).map (algebraMap F K) =
      ∏ j, minpoly K (ε (1 ⊗ₜ[F] pb.gen) j) := by
  classical
  choose b hb using exists_powerBasis_of_tensorProductPiEquiv pb ε
  let : Module.Finite F E := pb.finite
  let : ∀ j, Module.Finite K (D j) := fun j => (b j).finite
  have hp : (Algebra.lmul F E pb.gen).charpoly = minpoly F pb.gen := by
    rw [← LinearMap.charpoly_toMatrix _ pb.basis]
    exact charpoly_leftMulMatrix pb
  have hq (j : ι) :
      (Algebra.lmul K (D j) (ε (1 ⊗ₜ[F] pb.gen) j)).charpoly =
        minpoly K (ε (1 ⊗ₜ[F] pb.gen) j) := by
    rw [← hb j, ← LinearMap.charpoly_toMatrix _ (b j).basis]
    exact charpoly_leftMulMatrix (b j)
  rw [← hp, Algebra.map_charpoly_lmul_eq_prod_tensor D ε pb.gen]
  exact Finset.prod_congr rfl fun j _ => hq j

omit [Fintype ι] in
/-- The actual coordinate minimal polynomial divides the mapped original polynomial. -/
theorem minpoly_tensorProductPiEquiv_gen_dvd [Finite ι]
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (j : ι) :
    minpoly K (ε (1 ⊗ₜ[F] pb.gen) j) ∣
      (minpoly F pb.gen).map (algebraMap F K) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [map_minpoly_eq_prod_tensorProductPiEquiv pb ε]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

open Classical in
/-- The full normalized-factor multiset consists literally of the coordinate minimal
polynomials, including their occurrences. Monicity removes associatedness ambiguity. -/
theorem normalizedFactors_map_minpoly_tensorProductPiEquiv
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) :
    normalizedFactors ((minpoly F pb.gen).map (algebraMap F K)) =
      Finset.univ.val.map (fun j => minpoly K (ε (1 ⊗ₜ[F] pb.gen) j)) := by
  classical
  choose b hb using exists_powerBasis_of_tensorProductPiEquiv pb ε
  have hint (j : ι) : IsIntegral K (ε (1 ⊗ₜ[F] pb.gen) j) :=
    hb j ▸ (b j).isIntegral_gen
  rw [map_minpoly_eq_prod_tensorProductPiEquiv pb ε, Finset.prod_eq_multiset_prod]
  rw [normalizedFactors_prod_eq]
  · rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro j _
    exact (minpoly.monic (hint j)).normalize_eq_self
  · intro q hq
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hq
    exact minpoly.irreducible (hint j)

open Classical in
omit [Fintype ι] in
/-- Every literal monic irreducible divisor occurs as an actual coordinate minimal
polynomial. This statement preserves occurrence information and needs no separability. -/
theorem mem_normalizedFactors_map_minpoly_iff_tensorProductPiEquiv [Finite ι]
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (q : K[X]) :
    q ∈ normalizedFactors ((minpoly F pb.gen).map (algebraMap F K)) ↔
      ∃ j, minpoly K (ε (1 ⊗ₜ[F] pb.gen) j) = q := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [normalizedFactors_map_minpoly_tensorProductPiEquiv pb ε]
  simp

omit [Fintype ι] in
/-- Separability makes the literal coordinate-factor assignment injective. -/
theorem minpoly_tensorProductPiEquiv_gen_injective [Finite ι]
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (hsep : (minpoly F pb.gen).Separable) :
    Function.Injective (fun j => minpoly K (ε (1 ⊗ₜ[F] pb.gen) j)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hnonzero : (minpoly F pb.gen).map (algebraMap F K) ≠ 0 :=
    ((minpoly.monic pb.isIntegral_gen).map _).ne_zero
  have hnodup := (squarefree_iff_nodup_normalizedFactors hnonzero).mp hsep.map.squarefree
  rw [normalizedFactors_map_minpoly_tensorProductPiEquiv pb ε] at hnodup
  intro i j hij
  exact Multiset.inj_on_of_nodup_map hnodup i (Finset.mem_univ i) j
    (Finset.mem_univ j) hij

open Classical in
omit [Fintype ι] in
/-- The actual product indices identify with the existing subtype of literal normalized
factors. The equality specifying the bijection is part of the conclusion. -/
theorem exists_normalizedFactors_equiv_tensorProductPiEquiv [Finite ι]
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (hsep : (minpoly F pb.gen).Separable) :
    ∃ e : ι ≃ {q : K[X] //
        q ∈ normalizedFactors ((minpoly F pb.gen).map (algebraMap F K))},
      ∀ j, (e j).val = minpoly K (ε (1 ⊗ₜ[F] pb.gen) j) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let f : ι → {q : K[X] //
      q ∈ normalizedFactors ((minpoly F pb.gen).map (algebraMap F K))} :=
    fun j => ⟨minpoly K (ε (1 ⊗ₜ[F] pb.gen) j),
      (mem_normalizedFactors_map_minpoly_iff_tensorProductPiEquiv pb ε _).mpr ⟨j, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact minpoly_tensorProductPiEquiv_gen_injective pb ε hsep (congrArg Subtype.val hij)
    · intro q
      obtain ⟨j, hj⟩ :=
        (mem_normalizedFactors_map_minpoly_iff_tensorProductPiEquiv pb ε q.val).mp q.property
      exact ⟨j, Subtype.ext hj⟩
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

omit [Fintype ι] in
/-- Every actual coordinate factor occurs with multiplicity one in the separable case. -/
theorem emultiplicity_minpoly_tensorProductPiEquiv_gen [Finite ι]
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (hsep : (minpoly F pb.gen).Separable) (j : ι) :
    emultiplicity (minpoly K (ε (1 ⊗ₜ[F] pb.gen) j))
      ((minpoly F pb.gen).map (algebraMap F K)) = 1 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨b, hb⟩ := exists_powerBasis_of_tensorProductPiEquiv pb ε j
  have hint : IsIntegral K (ε (1 ⊗ₜ[F] pb.gen) j) := hb ▸ b.isIntegral_gen
  have hnonzero : (minpoly F pb.gen).map (algebraMap F K) ≠ 0 :=
    ((minpoly.monic pb.isIntegral_gen).map _).ne_zero
  have hnodup := (squarefree_iff_nodup_normalizedFactors hnonzero).mp hsep.map.squarefree
  have hmem : minpoly K (ε (1 ⊗ₜ[F] pb.gen) j) ∈
      normalizedFactors ((minpoly F pb.gen).map (algebraMap F K)) :=
    (mem_normalizedFactors_map_minpoly_iff_tensorProductPiEquiv pb ε _).mpr ⟨j, rfl⟩
  simp only [emultiplicity_eq_count_normalizedFactors (minpoly.irreducible hint) hnonzero,
    (minpoly.monic hint).normalize_eq_self, Multiset.count_eq_one_of_mem hnodup hmem,
    Nat.cast_one]

omit [Fintype ι] in
/-- The original quotient and every literal factor quotient identify with the existing
fields at the specified roots. The whole ring-map square identifies the literal
`AdjoinRoot.map` with the actual tensor coordinate on every original field element. -/
theorem exists_adjoinRoot_equiv_tensorProductPiEquiv_map [Finite ι]
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) :
    ∃ (g : AdjoinRoot (minpoly F pb.gen) ≃ₐ[F] E)
      (e : ∀ j, AdjoinRoot (minpoly K (ε (1 ⊗ₜ[F] pb.gen) j)) ≃ₐ[K] D j),
      g (AdjoinRoot.root (minpoly F pb.gen)) = pb.gen ∧
      (∀ j, e j (AdjoinRoot.root (minpoly K (ε (1 ⊗ₜ[F] pb.gen) j))) =
        ε (1 ⊗ₜ[F] pb.gen) j) ∧
      ∀ j, (e j).toRingHom.comp
          (AdjoinRoot.map (algebraMap F K) (minpoly F pb.gen)
            (minpoly K (ε (1 ⊗ₜ[F] pb.gen) j))
            (minpoly_tensorProductPiEquiv_gen_dvd pb ε j)) =
        ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)).comp g.toRingHom := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let p : F[X] := minpoly F pb.gen
  let q : ι → K[X] := fun j => minpoly K (ε (1 ⊗ₜ[F] pb.gen) j)
  have hp : aeval (AdjoinRoot.root p) (minpoly F pb.gen) = 0 :=
    (AdjoinRoot.aeval_eq (f := p) p).trans (AdjoinRoot.mk_self (f := p))
  let g : AdjoinRoot p ≃ₐ[F] E := AdjoinRoot.equiv' p pb hp (minpoly.aeval F pb.gen)
  have hg : g (AdjoinRoot.root p) = pb.gen :=
    AdjoinRoot.liftAlgHom_root p (Algebra.ofId F E) pb.gen (minpoly.aeval F pb.gen)
  choose b hb using exists_powerBasis_of_tensorProductPiEquiv pb ε
  have hq (j : ι) : aeval (AdjoinRoot.root (q j)) (minpoly K (b j).gen) = 0 := by
    rw [hb j]
    exact (AdjoinRoot.aeval_eq (f := q j) (q j)).trans (AdjoinRoot.mk_self (f := q j))
  have heval (j : ι) : aeval (b j).gen (q j) = 0 := by
    rw [hb j]
    exact minpoly.aeval K (ε (1 ⊗ₜ[F] pb.gen) j)
  let e (j : ι) : AdjoinRoot (q j) ≃ₐ[K] D j :=
    AdjoinRoot.equiv' (q j) (b j) (hq j) (heval j)
  have he (j : ι) : e j (AdjoinRoot.root (q j)) = ε (1 ⊗ₜ[F] pb.gen) j :=
    (AdjoinRoot.liftAlgHom_root (q j) (Algebra.ofId K (D j)) (b j).gen (heval j)).trans (hb j)
  refine ⟨g, e, hg, he, ?_⟩
  intro j
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro c
    change e j (AdjoinRoot.map (algebraMap F K) p (q j)
        (minpoly_tensorProductPiEquiv_gen_dvd pb ε j) (AdjoinRoot.of p c)) =
      ε (1 ⊗ₜ[F] g (AdjoinRoot.of p c)) j
    rw [AdjoinRoot.map_of]
    change e j (algebraMap K (AdjoinRoot (q j)) (algebraMap F K c)) =
      ε (1 ⊗ₜ[F] g (algebraMap F (AdjoinRoot p) c)) j
    rw [(e j).commutes, g.commutes]
    have ht : (1 : K) ⊗ₜ[F] algebraMap F E c =
        algebraMap K (K ⊗[F] E) (algebraMap F K c) := by
      change (1 : K) ⊗ₜ[F] algebraMap F E c = algebraMap F K c ⊗ₜ[F] (1 : E)
      exact (RingHom.congr_fun
        (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
          (R := F) (A := K) (B := E)) c).symm
    rw [ht, ε.commutes]
    rfl
  · change e j (AdjoinRoot.map (algebraMap F K) p (q j)
        (minpoly_tensorProductPiEquiv_gen_dvd pb ε j) (AdjoinRoot.root p)) =
      ε (1 ⊗ₜ[F] g (AdjoinRoot.root p)) j
    rw [AdjoinRoot.map_root, he j, hg]

end PowerBasis

end
