/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.Compact

/-! # Actual mapping-path lifting from HELP on a single pair

Implementation provenance:
`Quillen/Topology/HELP/PairLifting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.MappingPath

/-- Full prescribed-boundary HELP on this fixed pair gives genuine right
lifting of the original mapping-path endpoint on the same pair. -/
theorem endpoint_hasLiftingProperty_of_pairHELP
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {A B : TopCat.{u}} (i : A ⟶ B)
    (hf : ∀ (a : C(A, X)) (b : C(B, Y)) (H : (f.comp a).Homotopy (b.comp i.hom)),
      ∃ c : C(B, X), c.comp i.hom = a ∧ ∃ K : (f.comp c).Homotopy b,
        ∀ t x, K (t, i x) = H (t, x)) :
    HasLiftingProperty i (TopCat.ofHom (endpoint f)) where
  sq_hasLift {a b} sq := by
    let H : (f.comp ((source f).comp a.hom)).Homotopy (b.hom.comp i.hom) := {
      toFun z := (a z.2).1.2 z.1
      continuous_toFun := by fun_prop
      map_zero_left x := (a x).2
      map_one_left x := ConcreteCategory.congr_hom sq.w x }
    obtain ⟨c, hc, K, hK⟩ := hf ((source f).comp a.hom) b.hom H
    let l : C(B, MappingPath f) := {
      toFun x := ⟨(c x, ⟨fun t ↦ K (t, x), by fun_prop⟩), K.map_zero_left x⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.prodMk c.continuous
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact K.continuous.comp continuous_swap }
    refine ⟨TopCat.ofHom l, ?_, ?_⟩
    · ext x
      apply Subtype.ext
      apply Prod.ext
      · exact ContinuousMap.congr_fun hc x
      · apply ContinuousMap.ext
        intro t
        exact hK t x
    · ext x
      exact K.map_one_left x

end Topology.MappingPath
