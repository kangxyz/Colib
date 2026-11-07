/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.FilteredRealization.Homotopy

/-!
Adapted from `Quillen/Topology/FilteredRealization/PathComponents.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining original transition maps.


# Finite-stage detection of path components

Compact relative-homotopy factorization detects an entire finite family of
paths at one later stage. Consequently any finite set of points can be moved
to a stage where exactly its eventual component identifications already hold.
-/

@[expose] public section

open Topology
noncomputable section
open CategoryTheory Limits
open scoped Simplicial unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.FilteredRealization
variable {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
include hc

/-- Finitely many paths in the target are simultaneously witnessed after one
original transition, with precisely the prescribed endpoints. -/
theorem joined_finite_eventually (j : J) {ι : Type v} [Finite ι]
    (a b : ι → |F.obj j|)
    (h : ∀ i, Joined (SSet.toTop.map (c.ι.app j) (a i))
      (SSet.toTop.map (c.ι.app j) (b i))) :
    ∃ (k : J) (f : j ⟶ k), ∀ i, Joined
      (SSet.toTop.map (F.map f) (a i)) (SSet.toTop.map (F.map f) (b i)) := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  let a' : C(ι, |F.obj j|) := ⟨a, continuous_of_discreteTopology⟩
  let b' : C(ι, |F.obj j|) := ⟨b, continuous_of_discreteTopology⟩
  let H : ((SSet.toTop.map (c.ι.app j)).hom.comp a').HomotopyRel
      ((SSet.toTop.map (c.ι.app j)).hom.comp b') ∅ :=
    { toFun := fun t ↦ (h t.2).somePath t.1
      continuous_toFun := continuous_prod_of_discrete_right.mpr
        (fun i ↦ (h i).somePath.continuous)
      map_zero_left := fun i ↦ (h i).somePath.source
      map_one_left := fun i ↦ (h i).somePath.target
      prop' := fun _ _ hx ↦ False.elim hx }
  obtain ⟨k, f, ⟨Hk⟩⟩ := homotopyRel_factors F c hc j ∅ isCompact_empty H
  exact ⟨k, f, fun i ↦ ⟨Hk.toHomotopy.evalAt i⟩⟩

/-- A single target path is detected at a later stage. -/
theorem joined_eventually (j : J) {x y : |F.obj j|}
    (h : Joined (SSet.toTop.map (c.ι.app j) x) (SSet.toTop.map (c.ι.app j) y)) :
    ∃ (k : J) (f : j ⟶ k),
      Joined (SSet.toTop.map (F.map f) x) (SSet.toTop.map (F.map f) y) := by
  obtain ⟨k, f, hf⟩ := joined_finite_eventually F c hc j
    (fun _ : Unit ↦ x) (fun _ : Unit ↦ y) (fun _ ↦ h)
  exact ⟨k, f, hf Unit.unit⟩

/-- A finite support can be moved so that its stage components inject into
the target components. No transition is assumed injective on points or components. -/
theorem finite_component_relations_stabilize (j : J) (s : Finset |F.obj j|) :
    ∃ (k : J) (f : j ⟶ k), ∀ x ∈ s, ∀ y ∈ s,
      Joined (SSet.toTop.map (F.map f) x) (SSet.toTop.map (F.map f) y) ↔
        Joined (SSet.toTop.map (c.ι.app j) x) (SSet.toTop.map (c.ι.app j) y) := by
  classical
  let Pairs := {p : s × s // Joined (SSet.toTop.map (c.ι.app j) p.1.1)
    (SSet.toTop.map (c.ι.app j) p.2.1)}
  obtain ⟨k, f, hf⟩ := joined_finite_eventually F c hc j
    (fun i : Pairs ↦ i.1.1.1) (fun i : Pairs ↦ i.1.2.1) (fun i ↦ i.2)
  refine ⟨k, f, fun x hx y hy ↦ ⟨fun h ↦ ?_, fun h ↦ hf ⟨(⟨x, hx⟩, ⟨y, hy⟩), h⟩⟩⟩
  have he (z : |F.obj j|) :
      SSet.toTop.map (c.ι.app k) (SSet.toTop.map (F.map f) z) =
        SSet.toTop.map (c.ι.app j) z := by
    change (SSet.toTop.map (F.map f) ≫ SSet.toTop.map (c.ι.app k)) z = _
    rw [← Functor.map_comp, c.w]
    rfl
  simpa only [he] using h.map (SSet.toTop.map (c.ι.app k)).hom.continuous

end Topology.FilteredRealization
