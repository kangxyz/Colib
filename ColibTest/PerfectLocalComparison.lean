module

import Colib.AlgebraicGeometry.Modules.LocalRepresentativeComparison
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace LocalComparisonProbe

variable (X : Scheme.{u}) [hD : ∀ U : X.Opens, HasDerivedCategory.{d} U.toScheme.Modules]

-- This is the old locallyPerfect witness, with the old two class fields unfolded.
-- It is test scaffolding, not a proposed public replacement predicate.
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

private theorem source_le_target : source X ≤ target X := by
  intro K hK
  apply Scheme.Modules.Complex.isPerfectComplex_of_local_bounded_finiteLocallyFree_models X K
  intro x
  obtain ⟨U, hxU, P, hb, ht, e⟩ := hK x
  exact ⟨U, hxU, P, hb,
    fun n => SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u} (ht n), e⟩

private def inclusion : (source X).FullSubcategory ⥤ (target X).FullSubcategory :=
  ObjectProperty.ιOfLE (source_le_target X)

example : inclusion X ⋙ (target X).ι = (source X).ι := rfl

example (K : (source X).FullSubcategory) : ((inclusion X).obj K).obj = K.obj := rfl

example {K L : (source X).FullSubcategory} (f : K ⟶ L) :
    ((inclusion X).map f).hom = f.hom := rfl

example : (inclusion X).Full := by unfold inclusion; infer_instance

example : (inclusion X).Faithful := by unfold inclusion; infer_instance

example {K L : (source X).FullSubcategory} (f : K ⟶ L) :
    QuasiIso (((inclusion X).map f).hom) ↔ QuasiIso f.hom := Iff.rfl

end LocalComparisonProbe

namespace LocalComparisonProbe

-- Exact archived-model specialization: no supplied model family is an additional hypothesis.
local instance standardLocalModels (X : Scheme.{u}) :
    ∀ U : X.Opens, HasDerivedCategory.{u + 1} U.toScheme.Modules :=
  fun U => HasDerivedCategory.standard U.toScheme.Modules

/-- The source standard-model witness implies the native perfect-complex predicate. -/
theorem standard_model_comparison (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (hK : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ P : CochainComplex U.toScheme.Modules ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, ∃ q : _root_.SheafOfModules.LocalGeneratorsData.{u} (P.X n),
        q.IsLocallyFreeData ∧ q.IsFiniteType) ∧
      Nonempty ((DerivedCategory.Q (C := U.toScheme.Modules)).obj
          (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≅
        (DerivedCategory.Q (C := U.toScheme.Modules)).obj P)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfectComplex (X := X.toRingedSpace) K := by
  apply Scheme.Modules.Complex.isPerfectComplex_of_local_bounded_finiteLocallyFree_models X K
  intro x
  obtain ⟨U, hxU, P, hb, ht, e⟩ := hK x
  exact ⟨U, hxU, P, hb,
    fun n => SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u} (ht n), e⟩

end LocalComparisonProbe
