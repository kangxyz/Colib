/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.TopExtRingQuotient
public import Colib.Util.References
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Native positive-length top Koszul Ext with arbitrary coefficients

For a Koszul-regular sequence of positive length and any coefficient module N,
the actual coefficient quotient N/IN computes top Ext through the existing
standard top-coordinate cocycle. The equivalence is linear over R/I and
coefficient quotient maps give native Yoneda postcomposition.

Adapted from the declarations in
`Aglib.Algebra.Homology.Koszul.Ext.Coefficients` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The free-presentation argument is
retained, using native exactness and the already established Stacks-model
ring kernel. There are no regularity, flatness, finiteness or Noetherian
conditions on N. The empty sequence is not included in this module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped Pointwise
noncomputable section
universe u w

namespace Koszul
variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)] {n : ℕ}

private theorem seqTopExtClass_ideal_smul_le_ker (f : Fin (n + 1) → R)
    (hf : IsKoszulRegular f)
    (N : ModuleCat.{u} R) :
    (Ideal.span (Set.range f)) • (⊤ : Submodule R N) ≤ LinearMap.ker (seqTopExtClass f hf N) := by
  apply Submodule.smul_le.mpr
  intro r hr x _
  change seqTopExtClass f hf N (r • x) = 0
  rw [(seqTopExtClass f hf N).map_smul]
  exact Ext.quotientSourceIsTorsionBySet (Ideal.span (Set.range f)) N (n + 1) (a := ⟨r, hr⟩)

private theorem seqTopExtClass_finsupp_eq_zero_mem (f : Fin (n + 1) → R)
    (hf : IsKoszulRegular f)
    {ι : Type u} (x : ι →₀ R)
    (hx : seqTopExtClass f hf (ModuleCat.of R (ι →₀ R)) x = 0) :
    x ∈ (Ideal.span (Set.range f)) • (⊤ : Submodule R (ι →₀ R)) := by
  classical
  have hcoord (i : ι) : x i ∈ Ideal.span (Set.range f) := by
    let g : ModuleCat.of R (ι →₀ R) ⟶ ModuleCat.of R R :=
      ModuleCat.ofHom (Finsupp.lapply i)
    have h := seqTopExtClass_comp_mk₀ f hf g x
    have hg : g x = x i := rfl
    have hz : seqTopExtClass f hf (ModuleCat.of R R) (x i) = 0 := by
      simpa only [hx, Ext.zero_comp, hg] using h.symm
    have hmem : x i ∈ LinearMap.ker (seqTopExtClass.{u,w} f hf (ModuleCat.of R R)) := hz
    exact (seqTopExtClass_ring_ker.{u,w} f hf) ▸ hmem
  rw [← Finsupp.sum_single x]
  change (∑ i ∈ x.support, Finsupp.single i (x i)) ∈
    (Ideal.span (Set.range f)) • (⊤ : Submodule R (ι →₀ R))
  apply Submodule.sum_mem
  intro i _
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using
    (Submodule.smul_mem_smul (hcoord i)
      (show (Finsupp.single i (1 : R) : ι →₀ R) ∈ (⊤ : Submodule R (ι →₀ R)) from trivial))

/-- The canonical top class has exactly the sequence-ideal multiples as its kernel,
for every coefficient. -/
@[colib_tag "COL-0134",
  stacks 06XP "Ingredient: covariant long exact Ext sequence; coefficient quotient proved here"]
theorem seqTopExtClass_ker (f : Fin (n + 1) → R) (hf : IsKoszulRegular f)
    (N : ModuleCat.{u} R) :
    LinearMap.ker (seqTopExtClass f hf N) = (Ideal.span (Set.range f)) • (⊤ : Submodule R N) := by
  apply le_antisymm
  · intro x hx
    let F : ModuleCat.{u} R := ModuleCat.of R (N →₀ R)
    let π : F ⟶ N := ModuleCat.ofHom (Finsupp.linearCombination R (id : N → N))
    let : Epi π := (ModuleCat.epi_iff_surjective π).mpr
      (Finsupp.linearCombination_id_surjective R N)
    let S := ShortComplex.kernelSequence π
    have hS : S.ShortExact := {
      exact := ShortComplex.kernelSequence_exact π
      mono_f := by change Mono (kernel.ι π); infer_instance
      epi_g := by change Epi π; infer_instance }
    obtain ⟨y, hy⟩ := Finsupp.linearCombination_id_surjective R N x
    have hπy : π y = x := hy
    have hc : (seqTopExtClass f hf F y).comp (Ext.mk₀ S.g) (add_zero (n + 1)) = 0 := by
      erw [seqTopExtClass_comp_mk₀]
      change seqTopExtClass f hf N (π y) = 0
      rw [hπy]
      exact hx
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₂
      (X := ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) hS (seqTopExtClass f hf F y) hc
    obtain ⟨k, hk⟩ := seqTopExtClass_surjective f hf (kernel π) z
    have hrep : seqTopExtClass f hf F ((kernel.ι π) k) = seqTopExtClass f hf F y := by
      calc
        _ = (seqTopExtClass f hf (kernel π) k).comp (Ext.mk₀ (kernel.ι π))
            (add_zero (n + 1)) := (seqTopExtClass_comp_mk₀ f hf (kernel.ι π) k).symm
        _ = _ := by rw [hk]; exact hz
    have hd : seqTopExtClass f hf F (y - (kernel.ι π) k) = 0 := by
      rw [map_sub, hrep, sub_self]
    have hm := seqTopExtClass_finsupp_eq_zero_mem f hf (y - (kernel.ι π) k) hd
    have hzero : π ((kernel.ι π) k) = 0 :=
      ConcreteCategory.congr_hom (kernel.condition π) k
    have hprod : π (y - (kernel.ι π) k) = x := by
      rw [π.hom.map_sub, hzero, sub_zero]
      exact hy
    have hmap := (Submodule.smul_top_le_comap_smul_top (Ideal.span (Set.range f)) π.hom) hm
    change π (y - (kernel.ι π) k) ∈ (Ideal.span (Set.range f)) • (⊤ : Submodule R N) at hmap
    rwa [hprod] at hmap
  · exact seqTopExtClass_ideal_smul_le_ker f hf N

/-- The actual coefficient quotient computes native top Ext through the canonical Koszul class. -/
@[colib_tag "COL-0134"]
def seqTopExtLinearEquiv (f : Fin (n + 1) → R) (hf : IsKoszulRegular f)
    (N : ModuleCat.{u} R) :
    (N ⧸ ((Ideal.span (Set.range f)) • (⊤ : Submodule R N))) ≃ₗ[R]
      Ext.{w} (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N (n + 1) :=
  (Submodule.quotEquivOfEq _ _ (seqTopExtClass_ker f hf N).symm).trans
    ((seqTopExtClass f hf N).quotKerEquivOfSurjective (seqTopExtClass_surjective f hf N))

/-- A quotient representative gives the same canonical finite-resolution cocycle class. -/
@[simp]
theorem seqTopExtLinearEquiv_apply_mk (f : Fin (n + 1) → R) (hf : IsKoszulRegular f)
    (N : ModuleCat.{u} R) (x : N) :
    seqTopExtLinearEquiv.{u,w} f hf N (Submodule.Quotient.mk x) = seqTopExtClass f hf N x := by
  simp only [seqTopExtLinearEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The unchanged top Ext equivalence is linear for the native quotient-ring actions. -/
@[colib_tag "COL-0134"]
def seqTopExtQuotientLinearEquiv (f : Fin (n + 1) → R) (hf : IsKoszulRegular f)
    (N : ModuleCat.{u} R) :
    letI := Ext.quotientSourceModule.{u,w} (Ideal.span (Set.range f)) N (n + 1)
    (N ⧸ ((Ideal.span (Set.range f)) • (⊤ : Submodule R N))) ≃ₗ[R ⧸ Ideal.span (Set.range f)]
      Ext.{w} (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N (n + 1) := by
  letI := Ext.quotientSourceModule.{u,w} (Ideal.span (Set.range f)) N (n + 1)
  refine {
    __ := (seqTopExtLinearEquiv.{u,w} f hf N).toAddEquiv
    map_smul' := ?_ }
  intro b x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
    ((Ideal.span (Set.range f)) • (⊤ : Submodule R N)) x
  change seqTopExtLinearEquiv.{u,w} f hf N
      (Ideal.Quotient.mk (Ideal.span (Set.range f)) r • Submodule.Quotient.mk m) =
    Ideal.Quotient.mk (Ideal.span (Set.range f)) r •
      seqTopExtLinearEquiv.{u,w} f hf N (Submodule.Quotient.mk m)
  rw [Module.Quotient.mk_smul_mk, seqTopExtLinearEquiv_apply_mk, seqTopExtLinearEquiv_apply_mk,
    Ext.quotientSourceModule_mk_smul]
  exact (seqTopExtClass f hf N).map_smul r m

/-- Quotient-linearity retains the canonical cocycle on every coefficient representative. -/
@[simp]
theorem seqTopExtQuotientLinearEquiv_apply_mk (f : Fin (n + 1) → R)
    (hf : IsKoszulRegular f) (N : ModuleCat.{u} R) (x : N) :
    seqTopExtQuotientLinearEquiv.{u,w} f hf N (Submodule.Quotient.mk x) = seqTopExtClass f hf N x :=
  seqTopExtLinearEquiv_apply_mk f hf N x

/-- The quotient-ring refinement keeps exactly the canonical additive equivalence. -/
@[simp]
theorem seqTopExtQuotientLinearEquiv_toAddEquiv (f : Fin (n + 1) → R)
    (hf : IsKoszulRegular f) (N : ModuleCat.{u} R) :
    letI := Ext.quotientSourceModule.{u,w} (Ideal.span (Set.range f)) N (n + 1)
    (seqTopExtQuotientLinearEquiv.{u,w} f hf N).toAddEquiv =
      (seqTopExtLinearEquiv.{u,w} f hf N).toAddEquiv := rfl

/-- Original coefficient quotient maps give exactly native Yoneda postcomposition. -/
@[colib_tag "COL-0134"]
theorem seqTopExtQuotientLinearEquiv_naturality (f : Fin (n + 1) → R)
    (hf : IsKoszulRegular f) {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') (x : N ⧸ ((Ideal.span (Set.range f)) • (⊤ : Submodule R N))) :
    (seqTopExtQuotientLinearEquiv.{u,w} f hf N x).comp (Ext.mk₀ g) (add_zero (n + 1)) =
      seqTopExtQuotientLinearEquiv.{u,w} f hf N'
        ((((Ideal.span (Set.range f)) • (⊤ : Submodule R N)).mapQ
          ((Ideal.span (Set.range f)) • (⊤ : Submodule R N')) g.hom
          (Submodule.smul_top_le_comap_smul_top (Ideal.span (Set.range f)) g.hom)) x) := by
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective
    ((Ideal.span (Set.range f)) • (⊤ : Submodule R N)) x
  change (seqTopExtQuotientLinearEquiv.{u,w} f hf N (Submodule.Quotient.mk m)).comp
      (Ext.mk₀ g) (add_zero (n + 1)) =
    seqTopExtQuotientLinearEquiv.{u,w} f hf N' (Submodule.Quotient.mk (g m))
  rw [seqTopExtQuotientLinearEquiv_apply_mk, seqTopExtQuotientLinearEquiv_apply_mk]
  exact seqTopExtClass_comp_mk₀ f hf g m

end Koszul
