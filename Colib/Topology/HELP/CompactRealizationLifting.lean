/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.Compact
public import Colib.Topology.Homotopy.Extension
public import Colib.Topology.Realization.MonomorphismLifting
public import Colib.Topology.Realization.MonomorphismHEP
public import Colib.Topology.Realization.FiniteHausdorff

/-!
# Compact HELP supplies lifting against all realized simplicial inclusions

Actual compact simplex-boundary cofibrations are the generators. The
mapping-path endpoint then lifts over every realized simplicial mono by
the proved relative skeletal construction.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HELP/CompactRealizationLifting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, homotopies,
hypotheses and universes are retained; imports use native lower owners. -/
@[expose] public section

open Convexity

open Topology

noncomputable section
open TopCat Topology SSet StdSimplex CategoryTheory Limits MonoidalCategory
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.MappingPath
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (hf : CompactHomotopyExtensionLiftingProperty f)
include hf

/-- Compact HELP implies right lifting of the actual mapping-path endpoint
against every realized simplicial monomorphism. -/
theorem endpoint_hasLiftingProperty_realization_mono
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i) (TopCat.ofHom (endpoint f)) := by
  apply hasLiftingProperty_realization_mono
  intro n
  exact endpoint_hasLiftingProperty_of_compactHELP f hf _
    (SSet.homotopyExtensionProperty_realization_mono _)

end Topology.MappingPath
