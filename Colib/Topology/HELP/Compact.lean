/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingPath.Basic
public import Colib.Topology.Homotopy.Extension
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Compact homotopy extension and lifting

The prescribed boundary homotopy is part of the data and must be retained
exactly. This property gives genuine right lifting of the mapping-path
endpoint projection against compact cofibrations.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HELP/Compact.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, homotopies,
hypotheses and universes are retained; imports use native lower owners. -/
@[expose] public section

noncomputable section
open TopCat Topology CategoryTheory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology

/-- Homotopy extension and lifting on compact pairs. The lift is exact on
the included subspace and its comparison homotopy extends the entire given
boundary homotopy, rather than merely agreeing at the endpoints. -/
def CompactHomotopyExtensionLiftingProperty {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : Prop :=
  ∀ (A B : TopCat.{u}) [CompactSpace A] [CompactSpace B] (i : A ⟶ B),
    TopCat.HomotopyExtensionProperty i →
    ∀ (a : C(A, X)) (b : C(B, Y)) (H : (f.comp a).Homotopy (b.comp i.hom)),
      ∃ c : C(B, X), c.comp i.hom = a ∧
        ∃ K : (f.comp c).Homotopy b, ∀ t x, K (t, i x) = H (t, x)

namespace MappingPath
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (hf : CompactHomotopyExtensionLiftingProperty f)
include hf

/-- Compact HELP gives literal right lifting of the genuine mapping-path
endpoint projection against every compact cofibration. -/
theorem endpoint_hasLiftingProperty_of_compactHELP
    {A B : TopCat.{u}} [CompactSpace A] [CompactSpace B]
    (i : A ⟶ B) (hi : TopCat.HomotopyExtensionProperty i) :
    HasLiftingProperty i (TopCat.ofHom (endpoint f)) where
  sq_hasLift {a b} sq := by
    let H : (f.comp ((source f).comp a.hom)).Homotopy (b.hom.comp i.hom) := {
      toFun z := (a z.2).1.2 z.1
      continuous_toFun := by fun_prop
      map_zero_left x := (a x).2
      map_one_left x := ConcreteCategory.congr_hom sq.w x }
    obtain ⟨c, hc, K, hK⟩ := hf A B i hi ((source f).comp a.hom) b.hom H
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

end MappingPath
end Topology
