/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjective
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
Implementation provenance:
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveComplement.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Finite free complements over an arbitrary ring

The complement and the finite basis size are retained explicitly. This is the
algebraic cofinality input for comparing projective and free module models;
no topological group-completion comparison is asserted here.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  preservesBinaryBiproducts_of_preservesBiproducts

namespace ModuleCat.FiniteProjective
variable {R : Type u} [Ring R]

/-- A finite projective module is a direct summand of a specified finite free
module, with a finite projective complementary summand. -/
theorem exists_complement_equiv_fin (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (Q : ModuleCat.{u} R), Module.Finite R Q ∧ Module.Projective R Q ∧
      Nonempty ((M × Q) ≃ₗ[R] (Fin n → R)) := by
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let Q := ModuleCat.of R f.ker
  let e : (Q × M) ≃ₗ[R] (Fin n → R) :=
    lequivProdOfRightSplitExact (j := f.ker.subtype) (g := f) (f := g)
      (Submodule.subtype_injective _) (Submodule.range_subtype _) hfg
  let q : (Fin n → R) →ₗ[R] Q := (LinearMap.fst R Q M).comp e.symm.toLinearMap
  have hq : Function.Surjective q := by
    intro x
    exact ⟨e (x, 0), by simp [q]⟩
  let : Module.Finite R Q := Module.Finite.of_surjective q hq
  let i : Q →ₗ[R] (Fin n → R) := e.toLinearMap.comp (LinearMap.inl R Q M)
  let : Module.Projective R Q := Module.Projective.of_split i q (by ext; simp [i, q])
  exact ⟨n, Q, inferInstance, inferInstance,
    ⟨(LinearEquiv.prodComm R M Q).trans e⟩⟩

/-- The finite free left module with its actual rank label. No uniqueness of rank is asserted. -/
def free (n : ℕ) : Category.{u, u} R :=
  ⟨ModuleCat.of R (Fin n → R), inferInstance, inferInstance⟩

/-- The free-complement witness is an isomorphism in the finite projective category. -/
theorem exists_complement_iso_free (P : Category.{u, u} R) :
    ∃ (n : ℕ) (Q : Category.{u, u} R), Nonempty (P ⊞ Q ≅ free (R := R) n) := by
  obtain ⟨n, Q, hQf, hQp, ⟨e⟩⟩ := exists_complement_equiv_fin P.obj
  let Q' : Category.{u, u} R := ⟨Q, hQf, hQp⟩
  refine ⟨n, Q', ⟨(property R).isoMk ?_⟩⟩
  exact (property R).ι.mapBiprod P Q' ≪≫ ModuleCat.biprodIsoProd _ _ ≪≫ e.toModuleIso

/-- Rank zero is a zero object, including over the zero ring. -/
theorem free_zero_isZero : IsZero (free (R := R) 0) := by
  apply IsZero.of_full_of_faithful_of_isZero (property R).ι
  change IsZero (ModuleCat.of R (Fin 0 → R))
  exact ModuleCat.isZero_of_subsingleton _

/-- Adding one rank-one free summand gives the next labelled finite free module. -/
def freeSuccIso (n : ℕ) : free (R := R) 1 ⊞ free n ≅ free (n + 1) :=
  (property R).isoMk ((property R).ι.mapBiprod _ _ ≪≫ ModuleCat.biprodIsoProd _ _ ≪≫
    ((LinearEquiv.prodCongr (LinearEquiv.funUnique (Fin 1) R R)
      (LinearEquiv.refl R (Fin n → R))).trans
        (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R))).toModuleIso)

end ModuleCat.FiniteProjective
