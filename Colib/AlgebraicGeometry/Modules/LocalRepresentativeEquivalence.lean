/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicGeometry.Modules.LocalRepresentativeComparison
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFreeRetract

/-!
# Local perfect representatives on a scheme

The local model in Stacks 08CM has finite support and terms which are global retracts of
finite free modules. On a scheme those terms are finite locally free by Stacks 0BCI, since
the structure-sheaf stalks are local rings. Thus the same local complex is a model in the
sense of Aglib `Modules/PerfectComplexes/Local.lean` at 2c34f185.

The predicate comparison below preserves the ambient chain complex and the chosen local derived
models. The local isomorphism is the inverse of the image of the original quasi-isomorphism,
composed with the native comparison between the two actual restriction functors.

This compares local perfectness predicates. It does not identify the global notions of
strict perfectness, construct a Waldhausen equivalence, or assert a K-theory comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.Scheme.Modules.Complex

universe u d

private theorem local_bounded_finiteLocallyFree_models_of_isPerfectComplex
    (X : Scheme.{u}) [hD : ∀ U : X.Opens, HasDerivedCategory.{d} U.toScheme.Modules]
    (K : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ P : CochainComplex U.toScheme.Modules ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := U.toScheme.ringCatSheaf) (P.X n)) ∧
      Nonempty ((DerivedCategory.Q (C := U.toScheme.Modules)).obj
          (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≅
        (DerivedCategory.Q (C := U.toScheme.Modules)).obj P) := by
  obtain ⟨I, U, hU, hmodels⟩ := hK
  intro x
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := Opens.mem_iSup.mp (by rw [hU]; trivial)
  obtain ⟨P, hP, f, hf⟩ := hmodels i
  let V : X.Opens := U i
  refine ⟨V, hxi, P, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Stacks.Cohomology.LocalNullHomotopy.exists_lower_bound hP
    obtain ⟨b, hb⟩ := Stacks.Cohomology.LocalNullHomotopy.exists_upper_bound hP
    exact ⟨a, b, fun n hn => hn.elim (ha n) (hb n)⟩
  · intro n
    obtain ⟨r, hret⟩ := (isDirectSummandOfFiniteFree_iff_retract (P.X n)).mp
      (hP.directSummand n)
    have : ∀ x : V.toScheme.carrier,
        IsLocalRing (ToType (TopCat.Presheaf.stalk V.toScheme.sheaf.obj x)) :=
      fun x => V.toScheme.toLocallyRingedSpace.isLocalRing x
    exact SheafOfModules.isFiniteLocallyFree_of_retract
      (X := V.toScheme.carrier) (O := V.toScheme.sheaf) hret
      (RingedSpace.isFiniteLocallyFree_finiteFree V.toScheme.toRingedSpace r)
  · have : (show OXMod.{u, u, u} X.toRingedSpace ⥤
        OXMod.{u, u, u} (X.toRingedSpace.restrict V.isOpenEmbedding) from
          Scheme.Modules.restrictFunctor V.ι).PreservesZeroMorphisms :=
      ⟨fun _ _ => by ext _ _; rfl⟩
    have : IsIso ((DerivedCategory.Q (C := V.toScheme.Modules)).map f) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso V.toScheme.Modules f).mpr hf
    exact ⟨((DerivedCategory.Q (C := V.toScheme.Modules)).mapIso
      ((NatIso.mapHomologicalComplex
        (RingedSpace.restrictModulesIsoRestrictFunctor X V)
          (ComplexShape.up ℤ)).app K)).symm ≪≫
      (asIso ((DerivedCategory.Q (C := V.toScheme.Modules)).map f)).symm⟩

/-- On a scheme, perfectness is precisely the existence of local bounded finite locally free
models for the actual restricted complex in the given local derived categories. -/
@[colib_tag "COL-0176",
  stacks 0BCJ "Scheme specialization of (1) iff (2), on a fixed complex with given local models",
  colib_ref "aglib" "Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Local.lean:48-54"
    "comparison" "The exposed locallyPerfect witness at 2c34f185, with its original restriction",
  colib_ref "aglib" "Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Strict.lean:45-50"
    "ingredient" "Interval bounds on terms and finite local freeness of the local model"]
theorem isPerfectComplex_iff_local_bounded_finiteLocallyFree_models
    (X : Scheme.{u}) [hD : ∀ U : X.Opens, HasDerivedCategory.{d} U.toScheme.Modules]
    (K : CochainComplex X.Modules ℤ) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K ↔
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ P : CochainComplex U.toScheme.Modules ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
        (∀ n : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          (R := U.toScheme.ringCatSheaf) (P.X n)) ∧
        Nonempty ((DerivedCategory.Q (C := U.toScheme.Modules)).obj
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≅
          (DerivedCategory.Q (C := U.toScheme.Modules)).obj P) :=
  ⟨local_bounded_finiteLocallyFree_models_of_isPerfectComplex X K,
    isPerfectComplex_of_local_bounded_finiteLocallyFree_models X K⟩

end AlgebraicGeometry.Scheme.Modules.Complex
