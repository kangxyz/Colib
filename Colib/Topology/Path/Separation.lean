/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Path
public import Mathlib.Topology.Separation.Basic

/-!
# T1 separation of path spaces

The original compact-open path space in a T1 space is T1, because its continuous
map to the pointwise function space is injective.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/Path/Separation.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original objects, maps,
point hypotheses, whole stored cylinder paths and universe parameters are
retained. Native namespace and lower-import ownership are used. -/
@[expose] public section

namespace Path

instance instT1Space {X : Type*} [TopologicalSpace X] [T1Space X] (x y : X) :
    T1Space (Path x y) :=
  t1Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun

end Path
