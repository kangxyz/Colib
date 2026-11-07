/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.Equiconnection
public import Colib.Topology.LocalEquiconnection

/-!
# The local equiconnection on a metric order complex

The common-support connector is defined on the open set of pairs whose L1 distance is
less than two. Its endpoint equations and its restriction to the diagonal are exact.

Implementation source: the base-space construction in
`Quillen/Topology/MetricOrderComplex/LoopEquiconnection.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No based-loop construction is imported.
-/
@[expose] public noncomputable section

universe u
namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- The common-support geometry gives a diagonal-fixed local connector. -/
def localEquiconnection : LocalEquiconnection (MetricOrderComplex P) where
  domain := {z | 0 < commonMass z.1 z.2}
  isOpen_domain := isOpen_commonMass_pos
  diagonal_mem x := by simp
  connector := connector
  connector_zero := connector_zero
  connector_one := connector_one
  connector_diagonal := connector_diagonal

/-- Every open vertex star is convex for the actual local connector. -/
theorem vertexStar_isConvex (v : P) :
    (localEquiconnection (P := P)).IsConvex (vertexStar v) where
  pair_mem {_x _y} hx hy := commonMass_pos_of_mem_vertexStar hx hy
  connector_mem {_x _y} hx hy t := connector_mem_vertexStar hx hy t

end Topology.MetricOrderComplex
