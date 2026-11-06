/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.Topology.Subpath

/-!
# Paths in an actual subset

Extracted unchanged from `Colib.Topology.Homotopy.OpenCoverFull`, whose implementation
provenance is Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
variable {X : Type*} [TopologicalSpace X]

/-- A path whose endpoints and image lie in a subset, regarded as a path in
that subset with its actual subspace topology. -/
def Path.inSubset {U : Set X} {x y : U} (p : Path x.1 y.1)
    (hp : Set.range p ⊆ U) : Path x y where
  toFun t := ⟨p t, hp (Set.mem_range_self t)⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] theorem Path.inSubset_map {U : Set X} {x y : U} (p : Path x.1 y.1)
    (hp : Set.range p ⊆ U) :
    (Path.inSubset p hp).map continuous_subtype_val = p := by
  ext t
  rfl
