/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.LocalConnectorTransfer
public import Colib.Topology.MetricOrderComplex.RealizationHomotopyEquiv
public import Colib.Topology.MetricOrderComplex.LocalEquiconnection

/-!
# Actual covers of the original weak order-complex realization

Pull back the constructed metric-order path-class
cover along the exact original barycentric coordinate map. The base remains
the original weak realization topology, without any inferred local property.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/RealizationCover.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The cover is constructed by the actual
path-class prebundle and pulled back along the native barycentric coordinate map. -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology Simplicial
universe u
namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P] [PathConnectedSpace |nerve P|]

/-- An actual simply connected surjective cover of the original weak order realization. -/
theorem exists_simplyConnected_realization_cover (p : P) :
    ∃ T : Type u, ∃ t : TopologicalSpace T,
      letI := t
      ∃ q : C(T, |nerve P|), IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace T :=
  Covering.exists_simplyConnected_cover_of_localEquiconnection
    realizationHomotopyEquiv localEquiconnection (classifyingSpacePoint p)

end Topology.MetricOrderComplex
