/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeRepresentation
public import Mathlib.Data.Int.Interval
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RepresentativeIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone

/-!
# Comparing local bounded finite locally free representatives with perfect complexes

This is the forward comparison for the actual local representatives used by
Aglib `Modules/PerfectComplexes/Local.lean` at 2c34f185. The input is its local witness,
with the boundedness and finite-local-basis predicates exposed. The restriction is the
original scheme restriction, and the derived isomorphism has its original direction.

The existing restriction isomorphism, Stacks 08CN representative independence, and the
existing complex-level local gluing theorem supply the comparison. The underlying complex
is unchanged. No converse, equivalence of categories or Waldhausen equivalence is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.Scheme.Modules.Complex

universe u d

private abbrev ringedDerivedModel (Y : Scheme.{u}) [h : HasDerivedCategory.{d} Y.Modules] :
    HasDerivedCategory.{d} (OXMod.{u, u, u} Y.toRingedSpace) := h

attribute [local instance] ringedDerivedModel

-- This supporting implication is private: the public consumer is the local comparison below.
private theorem isPerfectComplex_of_bounded_model {Y : Scheme.{u}}
    (P : CochainComplex Y.Modules ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hterms : ∀ n : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Y.ringCatSheaf) (P.X n)) :
    RingedSpace.IsPerfectComplex (X := Y.toRingedSpace) P := by
  classical
  obtain ⟨a, b, hbounded⟩ := hbounded
  have hb : {n : ℤ | ¬ IsZero (P.X n)}.Finite := by
    refine (Finset.finite_toSet (Finset.Icc a b)).subset ?_
    intro n hn
    by_contra hnot
    have houtside : n < a ∨ b < n := by
      simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hnot
    exact hn (hbounded n houtside)
  choose V hV hfree using fun y : Y =>
    RingedSpace.exists_free_iso_over_of_bounded P hb hterms y
  refine ⟨Y, V, top_unique fun y _ => Opens.mem_iSup.mpr ⟨y, hV y⟩, fun y =>
    ⟨RingedSpace.restrictComplex P (V y), ⟨?_, ?_⟩, 𝟙 _, inferInstance⟩⟩
  · exact hb.subset fun n hn hz => hn ((RingedSpace.restrictModules _ (V y)).map_isZero hz)
  · intro n
    obtain ⟨r, ⟨e⟩⟩ := hfree y n
    obtain ⟨e'⟩ := RingedSpace.nonempty_restrictModules_obj_iso_finiteFree (P.X n) (V y) r e
    exact (isDirectSummandOfFiniteFree_iff_retract _).mpr
      ⟨r, ⟨⟨e'.hom, e'.inv, by simp⟩⟩⟩

/-- Local bounded finite locally free representatives make the original complex perfect.
The chosen local derived models are parameters and the original local isomorphisms are retained.
-/
@[stacks 08CN "Part (2), representative independence, followed by complex-level local gluing",
  colib_ref "aglib" "Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Local.lean:48-54"
    "comparison" "Forward implication for the exposed local witness at 2c34f185"]
theorem isPerfectComplex_of_local_bounded_finiteLocallyFree_models
    (X : Scheme.{u}) [hD : ∀ U : X.Opens, HasDerivedCategory.{d} U.toScheme.Modules]
    (K : CochainComplex X.Modules ℤ)
    (hK : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ P : CochainComplex U.toScheme.Modules ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := U.toScheme.ringCatSheaf) (P.X n)) ∧
      Nonempty ((DerivedCategory.Q (C := U.toScheme.Modules)).obj
          (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≅
        (DerivedCategory.Q (C := U.toScheme.Modules)).obj P)) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K := by
  apply RingedSpace.isPerfectComplex_of_forall_isPerfectComplex_restrict
  intro x
  obtain ⟨U, hxU, P, hbounds, hterms, ⟨e⟩⟩ := hK x
  refine ⟨U, hxU, ?_⟩
  have hP : RingedSpace.IsPerfect.{u, d} (X := U.toScheme.toRingedSpace)
      ((DerivedCategory.Q (C := U.toScheme.Modules)).obj P) :=
    (isPerfectComplex_of_bounded_model P hbounds hterms).isPerfect
  have : (show OXMod.{u, u, u} X.toRingedSpace ⥤
      OXMod.{u, u, u} (X.toRingedSpace.restrict U.isOpenEmbedding) from
        Scheme.Modules.restrictFunctor U.ι).PreservesZeroMorphisms :=
    ⟨fun _ _ => by ext _ _; rfl⟩
  have e' : (DerivedCategory.Q (C := U.toScheme.Modules)).obj
        (RingedSpace.restrictComplex (X := X.toRingedSpace) K U) ≅
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj P :=
    (DerivedCategory.Q (C := U.toScheme.Modules)).mapIso
      ((NatIso.mapHomologicalComplex
        (RingedSpace.restrictModulesIsoRestrictFunctor X U) (ComplexShape.up ℤ)).app K) ≪≫ e
  exact RingedSpace.isPerfectComplex_of_isPerfect_representation hP ⟨e'⟩

end AlgebraicGeometry.Scheme.Modules.Complex
