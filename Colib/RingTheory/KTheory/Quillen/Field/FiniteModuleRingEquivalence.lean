/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Quillen.Field.ProjectiveFiniteModules
public import Colib.Algebra.Category.FGModuleCat.IsFG
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Coefficient-ring equivalences on actual finite-module Q-groups

Restriction of scalars along a field isomorphism induces an exact equivalence
of the existing finite-module categories. Applying the commutative-field
opposite-ring equivalence explicitly transports right modules to left modules.
The forward K-map is precisely that of scalar restriction.

Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/KTheory/Field/FiniteModuleRingEquivalence.lean` (original K-groups).
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat

variable {F L : Type u} [Field F] [Field L] (e : F ≃+* L)

private theorem finite_restrictScalars_iff (M : ModuleCat.{u} L) :
    Module.Finite F ((ModuleCat.restrictScalars e.toRingHom).obj M) ↔ Module.Finite L M := by
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : (ModuleCat.restrictScalars e.toRingHom).obj M →ₛₗ[e.toRingHom] M :=
    { toFun := id, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  exact f.finite_iff_of_bijective ⟨Function.injective_id, Function.surjective_id⟩

/-- The equivalence is the restriction of the existing module scalar-restriction equivalence. -/
def finiteModuleRingEquivalence : FGModuleCat.{u} L ≌ FGModuleCat.{u} F :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).congrFullSubcategory (by
    funext M
    exact propext (finite_restrictScalars_iff e M))

instance finiteModuleRingEquivalence_additive :
    (finiteModuleRingEquivalence e).functor.Additive where
  map_add := by intros; rfl

/-- The actual restricted equivalence preserves the abelian exact structures. -/
def finiteModuleRingExact : ExactFunctor (abelianExactStructure (FGModuleCat.{u} L))
    (abelianExactStructure (FGModuleCat.{u} F)) where
  toFunctor := (finiteModuleRingEquivalence e).functor
  map_conflation _ h := h.map_of_exact _

instance finiteModuleRingExact_mapQ_isEquivalence :
    (finiteModuleRingExact e).mapQ.IsEquivalence := by
  let : (finiteModuleRingExact e).toFunctor.IsEquivalence :=
    (finiteModuleRingEquivalence e).isEquivalence_functor
  apply (finiteModuleRingExact e).mapQ_isEquivalence_of_equivalence
  · intro X Y i hi
    have : Mono ((finiteModuleRingExact e).toFunctor.map i) :=
      (abelianExactStructure_inflation_iff _ _).mp hi
    exact (abelianExactStructure_inflation_iff _ i).mpr
      ((finiteModuleRingExact e).toFunctor.mono_of_mono_map inferInstance)
  · intro X Y p hp
    have : Epi ((finiteModuleRingExact e).toFunctor.map p) :=
      (abelianExactStructure_deflation_iff _ _).mp hp
    exact (abelianExactStructure_deflation_iff _ p).mpr
      ((finiteModuleRingExact e).toFunctor.epi_of_epi_map inferInstance)

/-- The original Q K-map of scalar restriction is an equivalence. -/
def finiteModuleRingKEquiv (n : ℕ) :
    (abelianExactStructure (FGModuleCat.{u} L)).K n ≃*
      (abelianExactStructure (FGModuleCat.{u} F)).K n :=
  (finiteModuleRingExact e).KEquivOfMapQIsEquivalence n

/-- The equivalence retains scalar restriction as its original forward K-map. -/
@[simp] theorem finiteModuleRingKEquiv_apply (n : ℕ)
    (a : (abelianExactStructure (FGModuleCat.{u} L)).K n) :
    finiteModuleRingKEquiv e n a = (finiteModuleRingExact e).KMap n a := rfl

end FGModuleCat
