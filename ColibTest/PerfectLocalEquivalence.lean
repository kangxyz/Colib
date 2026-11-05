module

import Colib.AlgebraicGeometry.Modules.LocalRepresentativeEquivalence
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace LocalEquivalenceProbe

variable (X : Scheme.{u}) [hD : ∀ U : X.Opens, HasDerivedCategory.{d} U.toScheme.Modules]

-- The old locallyPerfect witness with the old bound and local-basis definitions unfolded.
-- These predicates are private test scaffolding, not new public API.
private def source : ObjectProperty (CochainComplex X.Modules ℤ) := fun K =>
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ P : CochainComplex U.toScheme.Modules ℤ,
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
    (∀ n : ℤ, ∃ q : _root_.SheafOfModules.LocalGeneratorsData.{u} (P.X n),
      q.IsLocallyFreeData ∧ q.IsFiniteType) ∧
    Nonempty ((DerivedCategory.Q (C := U.toScheme.Modules)).obj
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj P)

private def target : ObjectProperty (CochainComplex X.Modules ℤ) :=
  Stacks.Cohomology.PerfectComplexes.IsPerfectComplex (X := X.toRingedSpace)

private theorem source_iff_target (K : CochainComplex X.Modules ℤ) :
    source X K ↔ target X K := by
  constructor
  · intro h
    apply (Scheme.Modules.Complex.isPerfectComplex_iff_local_bounded_finiteLocallyFree_models
      X K).mpr
    intro x
    obtain ⟨U, hxU, P, hb, ht, e⟩ := h x
    exact ⟨U, hxU, P, hb, fun n => SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u} (ht n), e⟩
  · intro h x
    obtain ⟨U, hxU, P, hb, ht, e⟩ :=
      (Scheme.Modules.Complex.isPerfectComplex_iff_local_bounded_finiteLocallyFree_models
        X K).mp h x
    exact ⟨U, hxU, P, hb, fun n => (ht n).exists_isFiniteLocallyFreeData, e⟩

private def comparison : (source X).FullSubcategory ≌ (target X).FullSubcategory where
  functor := ObjectProperty.ιOfLE (fun K => (source_iff_target X K).mp)
  inverse := ObjectProperty.ιOfLE (fun K => (source_iff_target X K).mpr)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

example : (comparison X).functor ⋙ (target X).ι = (source X).ι := rfl

example : (comparison X).inverse ⋙ (source X).ι = (target X).ι := rfl

example (K : (source X).FullSubcategory) : ((comparison X).functor.obj K).obj = K.obj := rfl

example (K : (target X).FullSubcategory) : ((comparison X).inverse.obj K).obj = K.obj := rfl

example {K L : (source X).FullSubcategory} (f : K ⟶ L) :
    ((comparison X).functor.map f).hom = f.hom := rfl

example {K L : (target X).FullSubcategory} (f : K ⟶ L) :
    ((comparison X).inverse.map f).hom = f.hom := rfl

example (K : (source X).FullSubcategory) : ((comparison X).unitIso.app K).hom.hom = 𝟙 K.obj := rfl

example (K : (target X).FullSubcategory) :
    ((comparison X).counitIso.app K).hom.hom = 𝟙 K.obj := rfl

example {K L : (source X).FullSubcategory} (f : K ⟶ L) :
    QuasiIso (((comparison X).functor.map f).hom) ↔ QuasiIso f.hom := Iff.rfl

example {K L : (target X).FullSubcategory} (f : K ⟶ L) :
    QuasiIso (((comparison X).inverse.map f).hom) ↔ QuasiIso f.hom := Iff.rfl

example : (comparison X).functor.IsEquivalence := inferInstance

example : (comparison X).inverse.IsEquivalence := inferInstance

end LocalEquivalenceProbe

namespace LocalEquivalenceProbe

local instance standardLocalModels (X : Scheme.{u}) :
    ∀ U : X.Opens, HasDerivedCategory.{u + 1} U.toScheme.Modules :=
  fun U => HasDerivedCategory.standard U.toScheme.Modules

/-- With the original standard local derived models, the old local-basis witness is exactly
native perfectness. This statement exposes the archived predicate instead of redefining it. -/
theorem standard_model_comparison (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    (∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ P : CochainComplex U.toScheme.Modules ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, ∃ q : _root_.SheafOfModules.LocalGeneratorsData.{u} (P.X n),
        q.IsLocallyFreeData ∧ q.IsFiniteType) ∧
      Nonempty ((DerivedCategory.Q (C := U.toScheme.Modules)).obj
          (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≅
        (DerivedCategory.Q (C := U.toScheme.Modules)).obj P)) ↔
    Stacks.Cohomology.PerfectComplexes.IsPerfectComplex (X := X.toRingedSpace) K :=
  source_iff_target X K

end LocalEquivalenceProbe
