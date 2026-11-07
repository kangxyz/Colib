/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Examples.Algebra.FGModulesModuloTorsion

/-!
# Essential surjectivity of actual finite-module localization

The functor is the literal restriction of `ModuleCat.localizedModuleFunctor` to
Mathlib's `FGModuleCat`. Every finite module over `Localization S` is the localization
of the `R`-submodule spanned by a finite generating family. No Noetherian, domain or
nonzerodivisor hypothesis is needed for this construction.

## Implementation provenance

The functor specializes the native construction in
`StacksFrontier/Examples/Algebra/FGModulesModuloTorsion.lean` at Stacks commit
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`. The submodule witness inside the
essential-surjectivity proof is the proof of `Module.exists_fg_submodule_isLocalizedModule`
in `StacksFrontier/RingTheory/Flat/FlatLocalExtension.lean`, lines 88–104, at that
same commit. It is inlined here to avoid importing unrelated flat dévissage results.
-/
@[expose] public noncomputable section

universe u v

open CategoryTheory Module

namespace FGModuleCat

/-- Finite modules whose elements are individually annihilated by members of `S`. -/
def localizationTorsionProperty {R : Type u} [CommRing R] (S : Submonoid R) :
    ObjectProperty (FGModuleCat.{v} R) :=
  fun M ↦ ∀ x : M, ∃ s : S, (s : R) • x = 0

/-- The literal native scalar-localization functor restricted to finite modules. -/
def localizedModuleFunctor {R : Type u} [CommRing R] [Small.{v, u} R]
    (S : Submonoid R) : FGModuleCat.{v} R ⥤ FGModuleCat.{v} (Localization S) :=
  (ModuleCat.isFG (Localization S)).lift
    ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)) ⋙
      ModuleCat.localizedModuleFunctor S)
    (by
      intro M
      change Module.Finite (Localization S) (M.obj.localizedModule S)
      have : Module.Finite R M.obj := M.property
      exact Module.Finite.of_isLocalizedModule S (M.obj.localizedModuleMkLinearMap S))

instance localizedModuleFunctor_additive {R : Type u} [CommRing R] [Small.{v, u} R]
    (S : Submonoid R) : (localizedModuleFunctor.{u, v} S).Additive := by
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  let : F.Additive := ⟨by intros; rfl⟩
  dsimp [localizedModuleFunctor]
  infer_instance

/-- Forgetting finite generation gives exactly the original module-localization functor. -/
@[simp]
theorem localizedModuleFunctor_comp_forget {R : Type u} [CommRing R] [Small.{v, u} R]
    (S : Submonoid R) :
    localizedModuleFunctor.{u, v} S ⋙
      forget₂ (FGModuleCat.{v} (Localization S)) (ModuleCat.{v} (Localization S)) =
    forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ⋙ ModuleCat.localizedModuleFunctor S := rfl

/-- At the nonzerodivisors this is the original native fraction-ring functor, literally. -/
@[simp]
theorem localizedModuleFunctor_nonZeroDivisors (R : Type u) [CommRing R] [Small.{v, u} R] :
    localizedModuleFunctor.{u, v} (nonZeroDivisors R) =
      Stacks.Examples.fgFractionModuleFunctor R := rfl

/-- The generic torsion property specializes literally to the native fraction-ring kernel. -/
@[simp]
theorem localizationTorsionProperty_nonZeroDivisors (R : Type u) [CommRing R] :
    localizationTorsionProperty.{u, v} (nonZeroDivisors R) =
      Stacks.Examples.fgTorsionModuleProperty R := rfl

/-- Every finite localized module descends to an actual finite submodule over the base ring. -/
theorem localizedModuleFunctor_essSurj {R : Type u} [CommRing R] [Small.{v, u} R]
    (S : Submonoid R) : (localizedModuleFunctor.{u, v} S).EssSurj := by
  refine ⟨fun X => ?_⟩
  let : Module R X := Module.compHom X (algebraMap R (Localization S))
  let : IsScalarTower R (Localization S) X :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := Localization S) (M := X)
  let N : Submodule R X := Submodule.span R (Set.range g)
  let : Module.Finite R N := Module.Finite.span_of_finite R (Set.finite_range g)
  let : IsLocalizedModule S N.subtype := by
    refine ⟨(isLocalizedModule_id S X (Localization S)).map_units, ?_, ?_⟩
    · intro y
      obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span S (Localization S)
        (Set.range g) y (by rw [hg]; exact Submodule.mem_top)
      exact ⟨⟨⟨s • y, hs⟩, s⟩, rfl⟩
    · intro x₁ x₂ h
      exact ⟨1, by rw [show x₁ = x₂ from Subtype.ext h]⟩
  let M : FGModuleCat.{v} R := FGModuleCat.of R N
  let : Module.Finite R M.obj := M.property
  let : IsLocalizedModule S (M.obj.localizedModuleMkLinearMap S) :=
    M.obj.localizedModule_isLocalizedModule S
  let : Module.Finite (Localization S) (M.obj.localizedModule S) :=
    Module.Finite.of_isLocalizedModule S (M.obj.localizedModuleMkLinearMap S)
  let e : M.obj.localizedModule S ≃ₗ[R] X :=
    IsLocalizedModule.linearEquiv S (M.obj.localizedModuleMkLinearMap S) N.subtype
  exact ⟨M, ⟨(e.extendScalarsOfIsLocalization S (Localization S)).toFGModuleCatIso⟩⟩

end FGModuleCat
