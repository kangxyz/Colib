/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.UnitInterval
public import Colib.Topology.Homotopy.BoundaryCorrection
public import Colib.Topology.HomotopyFiber.Equivalence

/-! # Removing a backtracking boundary homotopy

The two opposite traversals shrink together through actual prefixes of the
reversed path. The deformation fixes both path endpoints throughout.


Implementation provenance:
`Quillen/Topology/HELP/RetraceBoundary.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped Topology unitInterval
open unitInterval
universe u v

namespace Topology

/-- The continuous family of shrinking backtracking paths, in uncurried form. -/
def retracePathFamily {A : Type u} {Z : Type v}
    [TopologicalSpace A] [TopologicalSpace Z] {f g : C(A, Z)}
    (L : f.Homotopy g) : C((I × A) × I, Z) where
  toFun z :=
    ((HomotopyFiber.homotopyPrefix L.symm z.1.2 (σ z.1.1)).trans
      (HomotopyFiber.homotopyPrefix L.symm z.1.2 (σ z.1.1)).symm) z.2
  continuous_toFun := Path.trans_continuous_family
    (fun z : I × A ↦ HomotopyFiber.homotopyPrefix L.symm z.2 (σ z.1))
    (by
      change Continuous (fun z : (I × A) × I ↦ L (σ (σ z.1.1 * z.2), z.1.2))
      fun_prop)
    (fun z : I × A ↦ (HomotopyFiber.homotopyPrefix L.symm z.2 (σ z.1)).symm)
    (by
      change Continuous (fun z : (I × A) × I ↦ L (σ (σ z.1.1 * σ z.2), z.1.2))
      fun_prop)

/-- Continuously contract a reversed homotopy followed by the original one,
relative to both interval endpoints and uniformly in the parameter space. -/
def retraceHomotopy {A : Type u} {Z : Type v}
    [TopologicalSpace A] [TopologicalSpace Z] {f g : C(A, Z)}
    (L : f.Homotopy g) :
    (L.symm.trans L).toContinuousMap.HomotopyRel
      (ContinuousMap.Homotopy.refl g).toContinuousMap
      {z : I × A | z.1 = 0 ∨ z.1 = 1} where
  toContinuousMap := (retracePathFamily L).comp
    ⟨fun z : I × (I × A) ↦ ((z.1, z.2.2), z.2.1), by fun_prop⟩
  map_zero_left z := by
    change ((HomotopyFiber.homotopyPrefix L.symm z.2 (σ 0)).trans
      (HomotopyFiber.homotopyPrefix L.symm z.2 (σ 0)).symm) z.1 = (L.symm.trans L) z
    simp only [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs
    · change L (σ (σ 0 * _), z.2) = L (σ _, z.2)
      simp
    · change L (σ (σ 0 * σ _), z.2) = L (_, z.2)
      simp
  map_one_left z := by
    change ((HomotopyFiber.homotopyPrefix L.symm z.2 (σ 1)).trans
      (HomotopyFiber.homotopyPrefix L.symm z.2 (σ 1)).symm) z.1 = g z.2
    simp only [Path.trans_apply]
    split_ifs <;> change L (σ (σ 1 * _), z.2) = g z.2 <;> simp
  prop' s z hz := by
    rcases hz with h | h
    · rcases z with ⟨t, a⟩
      change t = 0 at h
      subst t
      exact (Path.source ((HomotopyFiber.homotopyPrefix L.symm a (σ s)).trans
        (HomotopyFiber.homotopyPrefix L.symm a (σ s)).symm)).trans
          ((L.symm.trans L).map_zero_left a).symm
    · rcases z with ⟨t, a⟩
      change t = 1 at h
      subst t
      exact (Path.target ((HomotopyFiber.homotopyPrefix L.symm a (σ s)).trans
        (HomotopyFiber.homotopyPrefix L.symm a (σ s)).symm)).trans
          ((L.symm.trans L).map_one_left a).symm

end Topology
