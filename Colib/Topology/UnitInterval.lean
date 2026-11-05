/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.UnitInterval

/-!
# Continuity of multiplication on the unit interval

The ordinary product of two unit-interval parameters is continuous in their
product topology. The shared `fun_prop` rule supports path reparametrizations.
-/
/-! Implementation source: `Quillen/Topology/UnitInterval.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space models,
basepoint tracks, maps and universe parameters are retained. -/
@[expose] public section

namespace Topology

/-- Multiplication of unit-interval parameters is continuous. -/
@[fun_prop] theorem continuous_intervalMul :
    Continuous (fun z : unitInterval × unitInterval ↦ z.1 * z.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

end Topology
