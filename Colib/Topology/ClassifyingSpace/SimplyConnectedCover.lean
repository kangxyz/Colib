/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.LocalConnectorTransfer
public import Colib.Topology.MetricOrderComplex.RealizationHomotopyEquiv
public import Colib.Topology.MetricOrderComplex.LocalEquiconnection
public import Colib.CategoryTheory.RankedChain.Resolution
public import Colib.Topology.ClassifyingSpace.AsSmall

/-!
# Constructed covers of original categorical realizations

The actual poset-resolution equivalence and the weak-to-metric realization
equivalence construct the parameter map for the path-class pullback cover.
Object and morphism universes remain independent. No cover-existence or
local-topology premise on the original realization is assumed.

Implementation source: `Quillen/Topology/ClassifyingSpace/SimplyConnectedCover.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Only the unbased part of the
poset-resolution equivalence is needed; the based-loop construction is not imported.
-/
@[expose] public noncomputable section
open CategoryTheory Topology
open scoped Topology
universe u v

namespace CategoryTheory

/-- The original classifying space has a constructed simply connected surjective cover. -/
theorem exists_simplyConnected_classifying_cover
    (C : Type u) [Category.{v} C] [PathConnectedSpace (ClassifyingSpace C)] (c : C) :
    ∃ T : Type (max u v), ∃ t : TopologicalSpace T,
      letI := t
      ∃ q : C(T, ClassifyingSpace C),
        IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace T :=
  Covering.exists_simplyConnected_cover_of_localEquiconnection
    ((asSmallClassifyingHomeomorph C).toHomotopyEquiv.trans
      ((RankedChainOrder.resolutionHomotopyEquiv (AsSmall.{0} C)).symm.trans
        (MetricOrderComplex.realizationHomotopyEquiv
          (P := RankedChainOrder.ResolutionPoset (AsSmall.{0} C)))))
    MetricOrderComplex.localEquiconnection (classifyingSpacePoint c)

end CategoryTheory
