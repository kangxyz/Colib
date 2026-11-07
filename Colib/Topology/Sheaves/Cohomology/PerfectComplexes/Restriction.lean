/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone
public import
  StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.NestedRestriction

/-!
# Restriction of native perfect complexes

Restrict the local strictly perfect representatives in the native Stacks definition to the
intersection with the given open. The existing nested-open isomorphism identifies the resulting
complex with the twice-restricted complex. No derived-category model is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}}

/-- Restriction to an open subspace preserves native perfectness. -/
@[colib_tag "COL-0229",
  stacks 08CM "Restricting the local strictly perfect representatives in the definition"]
theorem IsPerfectComplex.restrict {K : CochainComplex (OXMod.{u, u} X) ℤ}
    (hK : IsPerfectComplex K) (W : Opens X.carrier) :
    IsPerfectComplex (restrictComplex K W) := by
  apply isPerfectComplex_of_forall_exists
  intro x
  obtain ⟨U, hxU, P, hP, α, hα⟩ := hK.exists_local x.1
  let V : Opens (X.restrict W.isOpenEmbedding).carrier :=
    (Opens.map (Opens.inclusion' W)).obj U
  have hVU : W.isOpenEmbedding.functor.obj V ≤ U := by
    rintro y ⟨z, hz, rfl⟩
    exact hz
  obtain ⟨Q, hQ, β, hβ⟩ := exists_restricted_quasiIso hVU K P hP α hα
  let e := PseudoCoherence.moduleEquivOfIso (PseudoCoherence.nestedOpenIso X W V)
  let E := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let i : E.functor.obj (restrictComplex (restrictComplex K W) V) ≅
      restrictComplex K (W.isOpenEmbedding.functor.obj V) :=
    PseudoCoherence.nestedRestrictionComplexIso X W V K
  have hstrict : IsStrictlyPerfect (E.inverse.obj Q) :=
    PseudoCoherence.isStrictlyPerfect_moduleEquiv
      (PseudoCoherence.nestedOpenIso X W V).symm Q hQ
  have : QuasiIso β := hβ
  have : QuasiIso (E.inverse.map (β ≫ i.inv)) := by
    change QuasiIso ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map (β ≫ i.inv))
    infer_instance
  exact ⟨V, hxU, E.inverse.obj Q, hstrict,
    E.inverse.map (β ≫ i.inv) ≫ (E.unitIso.app _).inv, inferInstance⟩

end AlgebraicGeometry.RingedSpace
