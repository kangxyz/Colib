/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Principal degree-one Ext through the standard connecting class

For a regular scalar `a`, the standard short exact sequence
`R → R → R/(a)` computes `Ext¹(R/(a), N)` as `N/aN`.
All objects, quotient maps and extension classes are Mathlib's native ones.

This reproves the equivalence endpoint of Aglib's
`Algebra/Homology/Koszul/Single/Ext/Ideal.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The normalization here is explicitly
the standard short exact sequence's connecting class. Comparison with the
old resolution cocycle (including its sign) is not asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The standard principal quotient presentation, with literal quotient map. -/
abbrev principalShortComplex (a : R) : ShortComplex (ModuleCat.{u} R) :=
  shortComplexOfCompEqZero (LinearMap.lsmul R R a) (Ideal.span {a}).mkQ (by
    apply LinearMap.ext
    intro r
    change Ideal.Quotient.mk (Ideal.span {a}) (a * r) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mul_mem_right r _ (Ideal.subset_span (Set.mem_singleton a)))

/-- A regular scalar gives the standard short exact principal quotient presentation. -/
theorem principalShortComplex_shortExact (a : R) (ha : IsSMulRegular R a) :
    (principalShortComplex a).ShortExact := by
  apply shortComplex_shortExact
  · intro r
    change Ideal.Quotient.mk (Ideal.span {a}) r = 0 ↔ ∃ s, a * s = r
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨fun ⟨s, hs⟩ => ⟨s, hs.symm⟩, fun ⟨s, hs⟩ => ⟨s, hs.symm⟩⟩
  · exact ha
  · exact Submodule.mkQ_surjective _

end ModuleCat

namespace Koszul

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (a : R) (ha : IsSMulRegular R a) (N : ModuleCat.{u} R)

/-- A coefficient represents the standard connecting class followed by its linear map. -/
def principalExtOneClass : N →ₗ[R] Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 1 :=
  (Ext.bilinearCompOfLinear R _ _ N 1 0 1 (add_zero 1)
    (ModuleCat.principalShortComplex_shortExact a ha).extClass).comp
    ((Ext.linearEquiv₀ (R := R)).symm.toLinearMap.comp
      ((ModuleCat.homLinearEquiv (S := R)).symm.toLinearMap.comp
        (LinearMap.ringLmapEquivSelf R R N).symm.toLinearMap))

/-- The defining normalization uses the standard principal quotient sequence. -/
theorem principalExtOneClass_apply (x : N) :
    principalExtOneClass a ha N x =
      (ModuleCat.principalShortComplex_shortExact a ha).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))) (add_zero 1) := rfl

/-- Every degree-one class is represented by a coefficient. -/
theorem principalExtOneClass_surjective : Function.Surjective (principalExtOneClass a ha N) := by
  intro e
  have : Subsingleton (Ext.{w} (ModuleCat.of R R) N 1) :=
    Ext.subsingleton_of_projective _ _ 0
  obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₃
    (ModuleCat.principalShortComplex_shortExact a ha) N e (by subsingleton) (add_zero 1)
  let f := Ext.linearEquiv₀ (R := R) z
  refine ⟨f.hom 1, ?_⟩
  have hf : ModuleCat.ofHom (LinearMap.toSpanSingleton R N (f.hom 1)) = f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r • f.hom 1 = f.hom r
    simpa only [smul_eq_mul, mul_one] using (f.hom.map_smul r (1 : R)).symm
  rw [principalExtOneClass_apply, hf, Ext.mk₀_linearEquiv₀_apply]
  exact hz

/-- The standard connecting class vanishes precisely on scalar multiples. -/
theorem principalExtOneClass_eq_zero_iff (x : N) :
    principalExtOneClass a ha N x = 0 ↔ x ∈ LinearMap.range (LinearMap.lsmul R N a) := by
  rw [principalExtOneClass_apply]
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₁
      (ModuleCat.principalShortComplex_shortExact a ha) N
      (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))) (add_zero 1) hx
    let g := Ext.linearEquiv₀ (R := R) z
    have hg : (ModuleCat.principalShortComplex a).f ≫ g =
        ModuleCat.ofHom (LinearMap.toSpanSingleton R N x) := by
      apply (Ext.mk₀_bijective _ _).injective
      rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_linearEquiv₀_apply]
      exact hz
    refine ⟨g.hom 1, ?_⟩
    have h := ConcreteCategory.congr_hom hg (1 : R)
    change g.hom (a • (1 : R)) = (1 : R) • x at h
    simpa only [map_smul, one_smul, LinearMap.lsmul_apply] using h
  · rintro ⟨y, hy⟩
    have hg : (ModuleCat.principalShortComplex a).f ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton R N y) =
          ModuleCat.ofHom (LinearMap.toSpanSingleton R N x) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change (a * r) • y = r • x
      change a • y = x at hy
      rw [mul_smul, ← hy]
      exact smul_comm a r y
    rw [← hg, ← Ext.mk₀_comp_mk₀]
    exact (ModuleCat.principalShortComplex_shortExact a ha).extClass_comp_assoc _

/-- The kernel of the coefficient class map is the scalar-multiplication image. -/
theorem principalExtOneClass_ker :
    LinearMap.ker (principalExtOneClass a ha N) = LinearMap.range (LinearMap.lsmul R N a) := by
  ext x
  exact principalExtOneClass_eq_zero_iff a ha N x

/-- The native coefficient quotient computes degree-one Ext via the connecting class. -/
def principalExtOneLinearEquiv :
    (N ⧸ LinearMap.range (LinearMap.lsmul R N a)) ≃ₗ[R]
      Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 1 :=
  (Submodule.quotEquivOfEq _ _ (principalExtOneClass_ker a ha N).symm).trans
    ((principalExtOneClass a ha N).quotKerEquivOfSurjective
      (principalExtOneClass_surjective a ha N))

/-- A literal coefficient representative maps to the standard connecting class. -/
@[simp]
theorem principalExtOneLinearEquiv_apply_mk (x : N) :
    principalExtOneLinearEquiv a ha N (Submodule.Quotient.mk x) =
      principalExtOneClass a ha N x := by
  simp only [principalExtOneLinearEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Coefficient postcomposition preserves the normalized principal class. -/
@[simp]
theorem principalExtOneClass_comp_mk₀ {N' : ModuleCat.{u} R} (g : N ⟶ N') (x : N) :
    (principalExtOneClass a ha N x).comp (Ext.mk₀ g) (add_zero 1) =
      principalExtOneClass a ha N' (g x) := by
  rw [principalExtOneClass_apply, principalExtOneClass_apply,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  congr 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact g.hom.map_smul r x

end Koszul

attribute [colib_tag "COL-0120"] Koszul.principalExtOneClass
  Koszul.principalExtOneLinearEquiv Koszul.principalExtOneLinearEquiv_apply_mk
  Koszul.principalExtOneClass_comp_mk₀

attribute [stacks 06XP
  "Ingredient: contravariant long exact Ext after Lemma 13.27.3; not old cocycle comparison"]
  Koszul.principalExtOneLinearEquiv
