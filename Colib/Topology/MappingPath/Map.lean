/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingPath.Basic
public import Colib.Topology.HomotopyPullback.Basic
public import Colib.Topology.Pushout.HomotopyEquivalence

/-! Functorial mapping-path replacement preserves homotopy-cartesian edges
as actual homotopy equivalences to the strict pullbacks of fibrations. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/MappingPath/Map.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
universe u
open scoped Topology unitInterval
namespace Topology.MappingPath
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]
  {p : C(X, A)} {q : C(Y, B)} (u : C(X, Y)) (v : C(A, B))
  (w : q.comp u = v.comp p)

/-- The map between mapping-path replacements induced by a commuting square `q ∘ u = v ∘ p`,
applying `u` to the source point and `v` to the entire path. -/
def map : C(MappingPath p, MappingPath q) where
  toFun z := ⟨(u z.1.1, v.comp z.1.2), by
    change v (z.1.2 0) = q (u z.1.1)
    rw [z.2]
    exact (ContinuousMap.congr_fun w z.1.1).symm⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : MappingPath p × unitInterval ↦ v (z.1.1.2 z.2))
      fun_prop

@[simp] theorem map_inclusion : (map u v w).comp (inclusion p) = (inclusion q).comp u := by
  ext x
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    exact (ContinuousMap.congr_fun w x).symm

@[simp] theorem endpoint_map : (endpoint q).comp (map u v w) = v.comp (endpoint p) := rfl
@[simp] theorem source_map : (source q).comp (map u v w) = u.comp (source p) := rfl

/-- The canonical comparison to the strict pullback of the target endpoint projection along `v`,
pairing the original path endpoint with its mapped path. -/
def strictComparison : C(MappingPath p, {z : A × MappingPath q // endpoint q z.2 = v z.1}) where
  toFun z := ⟨(endpoint p z, map u v w z), rfl⟩
  continuous_toFun := by fun_prop

/-- Unpacking the compact-open path is a genuine homeomorphism. -/
def strictPullbackHomeomorph :
    {z : A × MappingPath q // endpoint q z.2 = v z.1} ≃ₜ HomotopyPullback q v where
  toFun z := ⟨(z.1.1, z.1.2.1), z.1.2.2, z.2⟩
  invFun z := ⟨(z.1.1, ⟨z.1.2, z.2.1⟩), z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem strictComparison_inclusion :
    (strictPullbackHomeomorph (q := q) v : C(_, _)).comp
      ((strictComparison u v w).comp (inclusion p)) =
        HomotopyPullback.comparison q v p u w := by
  ext x
  rfl

/-- A genuine cartesian edge becomes a canonical HE to the strict pullback
of mapping-path endpoint fibrations, retaining the exact comparison map. -/
def strictComparisonHomotopyEquiv
    (e : ContinuousMap.HomotopyEquiv X (HomotopyPullback q v))
    (he : e.toFun = HomotopyPullback.comparison q v p u w) :
    ContinuousMap.HomotopyEquiv (MappingPath p)
      {z : A × MappingPath q // endpoint q z.2 = v z.1} :=
  TopCat.homotopyEquivCancelLeft (A := TopCat.of X) (B := TopCat.of (MappingPath p))
    (C := TopCat.of {z : A × MappingPath q // endpoint q z.2 = v z.1})
    (a := TopCat.ofHom (inclusion p)) (b := TopCat.ofHom (strictComparison u v w))
    (inclusionHomotopyEquiv p) rfl
    (e.trans (strictPullbackHomeomorph (q := q) v).symm.toHomotopyEquiv) (by
      change ((strictPullbackHomeomorph (q := q) v).symm : C(_, _)).comp e.toFun =
        (strictComparison u v w).comp (inclusion p)
      rw [he]
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext; rfl)

@[simp] theorem strictComparisonHomotopyEquiv_toFun
    (e : ContinuousMap.HomotopyEquiv X (HomotopyPullback q v))
    (he : e.toFun = HomotopyPullback.comparison q v p u w) :
    (strictComparisonHomotopyEquiv u v w e he).toFun = strictComparison u v w := rfl

@[simp] theorem map_id (p : C(X, A)) :
    map (p := p) (q := p) (ContinuousMap.id X) (ContinuousMap.id A) rfl =
      ContinuousMap.id (MappingPath p) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  rfl

/-- Replacement is strictly functorial, not only homotopy functorial. -/
theorem map_comp {Z T : Type u} [TopologicalSpace Z] [TopologicalSpace T]
    {r : C(Z, T)} (u' : C(Y, Z)) (v' : C(B, T)) (w' : r.comp u' = v'.comp q)
    (ww : r.comp (u'.comp u) = (v'.comp v).comp p) :
    (map u' v' w').comp (map u v w) = map (u'.comp u) (v'.comp v) ww := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  rfl

end Topology.MappingPath
