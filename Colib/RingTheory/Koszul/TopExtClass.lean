/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import StacksFrontier.RingTheory.Koszul.TorComparison.TopHomology

/-!
# Top Ext classes from the canonical Koszul resolution

The standard top exterior coordinate of Stacks' Koszul complex represents every
class in top Ext. Coefficients act linearly and their maps agree with Yoneda
postcomposition. The degree and quotient are those of the actual native resolution.

Adapted from `ChainComplex.Koszul.topExtClass` and its basic properties in
`Aglib.Algebra.Homology.Koszul.Ext.Top` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The old recursive complex is not copied.
The normalization is the existing Stacks `topEquiv`, which sends the standard
ordered wedge to one. Comparison with the old named class is not claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)] {n : ℕ}
  (f : Fin n → R) (hf : IsKoszulRegular f)

/-- The standard top exterior coordinate gives the native top Ext class of a coefficient. -/
def seqTopExtClass (N : ModuleCat.{u} R) :
    N →ₗ[R] Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N n := by
  let P := seqProjectiveResolution f hf
  let c (x : N) : P.complex.X n ⟶ N :=
    (topEquiv R n).toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R N x)
  have hc (x : N) : P.complex.d (n + 1) n ≫ c x = 0 :=
    (seqComplex_isZero_of_lt f (n + 1) (by omega)).eq_of_src _ _
  refine { toFun := fun x => P.extMk (c x) (n + 1) rfl (hc x)
           map_add' := ?_, map_smul' := ?_ }
  · intro x y
    rw [P.add_extMk]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change topEquiv R n z • (x + y) = topEquiv R n z • x + topEquiv R n z • y
    exact smul_add _ _ _
  · intro r x
    rw [Ext.smul_eq_comp_mk₀, P.extMk_comp_mk₀]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change topEquiv R n z • (r • x) = r • (topEquiv R n z • x)
    exact smul_comm _ _ _

/-- The top coefficient class is represented by the literal top-coordinate cocycle. -/
theorem seqTopExtClass_apply (N : ModuleCat.{u} R) (x : N) :
    seqTopExtClass f hf N x = (seqProjectiveResolution f hf).extMk
      ((topEquiv R n).toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))
      (n + 1) rfl ((seqComplex_isZero_of_lt f (n + 1) (by omega)).eq_of_src _ _) := rfl

/-- Every native top Ext class is represented by a coefficient. -/
theorem seqTopExtClass_surjective (N : ModuleCat.{u} R) :
    Function.Surjective (seqTopExtClass f hf N) := by
  let P := seqProjectiveResolution f hf
  intro e
  obtain ⟨g, hg, rfl⟩ := P.extMk_surjective e (n + 1) rfl
  let g₀ : ModuleCat.of R R ⟶ N := (topEquiv R n).toModuleIso.inv ≫ g
  have h₀ : ModuleCat.ofHom (LinearMap.toSpanSingleton R N (g₀.hom 1)) = g₀ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r • g₀.hom 1 = g₀.hom r
    simpa only [smul_eq_mul, mul_one] using (g₀.hom.map_smul r (1 : R)).symm
  refine ⟨g₀.hom 1, ?_⟩
  rw [seqTopExtClass_apply, h₀]
  dsimp only [g₀]
  erw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Coefficient morphisms agree with native Yoneda postcomposition of top classes. -/
@[simp]
theorem seqTopExtClass_comp_mk₀ {N N' : ModuleCat.{u} R} (g : N ⟶ N') (x : N) :
    (seqTopExtClass f hf N x).comp (Ext.mk₀ g) (add_zero n) =
      seqTopExtClass f hf N' (g x) := by
  rw [seqTopExtClass_apply, seqTopExtClass_apply]
  erw [ProjectiveResolution.extMk_comp_mk₀]
  congr 1
  erw [Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact g.hom.map_smul r x

/-- In positive top degree, a top class vanishes exactly when its cocycle is a boundary. -/
theorem seqTopExtClass_eq_zero_iff (N : ModuleCat.{u} R) (m : ℕ) (hm : m + 1 = n) (x : N) :
    seqTopExtClass f hf N x = 0 ↔
      ∃ g : (seqComplex f).X m ⟶ N, (seqComplex f).d n m ≫ g =
        (topEquiv R n).toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R N x) := by
  rw [seqTopExtClass_apply]
  exact (seqProjectiveResolution f hf).extMk_eq_zero_iff _ (n + 1) rfl _ m hm

/-- A supplied native resolution comparison acts on top classes by its top-coordinate scalar.
This isolates the Ext step of a determinant comparison, without assuming a matrix construction. -/
theorem seqTopExtClass_covariance (g : Fin n → R) (hg : IsKoszulRegular g)
    (q : ModuleCat.of R (R ⧸ Ideal.span (Set.range g)) ⟶
      ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))
    (Φ : ProjectiveResolution.Hom (seqProjectiveResolution g hg)
      (seqProjectiveResolution f hf) q) (d : R)
    (hTop : Φ.hom.f n ≫ (topEquiv R n).toModuleIso.hom =
      (topEquiv R n).toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.lsmul R R d))
    (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ q).comp (seqTopExtClass f hf N x) (zero_add n) =
      seqTopExtClass g hg N (d • x) := by
  rw [seqTopExtClass_apply, seqTopExtClass_apply]
  erw [ProjectiveResolution.mk₀_comp_extMk (φ := Φ)]
  congr 1
  erw [← Category.assoc, hTop, Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (d * r) • x = r • (d • x)
  rw [smul_smul, mul_comm]

end Koszul

attribute [colib_tag "COL-0118"] Koszul.seqTopExtClass Koszul.seqTopExtClass_apply
  Koszul.seqTopExtClass_surjective Koszul.seqTopExtClass_comp_mk₀
  Koszul.seqTopExtClass_eq_zero_iff Koszul.seqTopExtClass_covariance

attribute [stacks 06XP "Ingredient: Yoneda composition; native top-coordinate formulas proved here"]
  Koszul.seqTopExtClass_comp_mk₀
