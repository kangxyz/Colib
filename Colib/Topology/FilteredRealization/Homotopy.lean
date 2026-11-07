/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FilteredRealization.Compact
public import Mathlib.Topology.Homotopy.Basic

/-!
# Relative compact homotopy lifting in filtered realization colimits

Compact maps, their cube-boundary constraints, and endpoint-fixed homotopies
are represented exactly at one later stage. This does not assume that any
stage-to-colimit map is injective.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/FilteredRealization/Homotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The arbitrary filtered category,
actual cocone maps, exact factorization and universe parameters are retained. -/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits SSet
open scoped Simplicial unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.FilteredRealization
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
include hc

/-- Compact-source factorization can be chosen at a stage receiving an
arrow from any prescribed original stage. -/
theorem compact_factors_above {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (j : J) (f : C(T, |c.pt|)) :
    ∃ k, ∃ _ : j ⟶ k, ∃ g : C(T, |F.obj k|), (SSet.toTop.map (c.ι.app k)).hom.comp g = f := by
  obtain ⟨l, a, ha⟩ := compact_factors F c hc f
  let k := IsFiltered.max j l
  let v : l ⟶ k := IsFiltered.rightToMax j l
  refine ⟨k, IsFiltered.leftToMax j l, (SSet.toTop.map (F.map v)).hom.comp a, ?_⟩
  rw [← ContinuousMap.comp_assoc, ← TopCat.hom_comp, ← Functor.map_comp, c.w]
  exact ha

/-- A homotopy relative to a compact subset of a compact source is realized
at one later stage, with both endpoint maps and the fixed subset retained
exactly after the same transition. -/
theorem homotopyRel_factors {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (j : J) {a b : C(T, |F.obj j|)} (S : Set T) (hS : IsCompact S)
    (H : ((SSet.toTop.map (c.ι.app j)).hom.comp a).HomotopyRel
      ((SSet.toTop.map (c.ι.app j)).hom.comp b) S) :
    ∃ k, ∃ u : j ⟶ k,
      Nonempty (((SSet.toTop.map (F.map u)).hom.comp a).HomotopyRel
        ((SSet.toTop.map (F.map u)).hom.comp b) S) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨k, u, g, hg⟩ := compact_factors_above F c hc j H.toContinuousMap
  let a' := (SSet.toTop.map (F.map u)).hom.comp a
  let b' := (SSet.toTop.map (F.map u)).hom.comp b
  let g₀ : C(T, |F.obj k|) := ⟨fun x ↦ g (0, x), by fun_prop⟩
  let g₁ : C(T, |F.obj k|) := ⟨fun x ↦ g (1, x), by fun_prop⟩
  let gS : C(unitInterval × S, |F.obj k|) := ⟨fun z ↦ g (z.1, z.2.1), by fun_prop⟩
  let aS : C(unitInterval × S, |F.obj k|) := ⟨fun z ↦ a' z.2.1, by fun_prop⟩
  let left : C(T ⊕ (T ⊕ (unitInterval × S)), |F.obj k|) :=
    ⟨Sum.elim g₀ (Sum.elim g₁ gS), g₀.continuous.sumElim (g₁.continuous.sumElim gS.continuous)⟩
  let right : C(T ⊕ (T ⊕ (unitInterval × S)), |F.obj k|) :=
    ⟨Sum.elim a' (Sum.elim b' aS), a'.continuous.sumElim (b'.continuous.sumElim aS.continuous)⟩
  have hga (t : unitInterval) (x : T) : SSet.toTop.map (c.ι.app k) (g (t, x)) = H (t, x) :=
    ContinuousMap.congr_fun hg (t, x)
  have hua (x : T) : SSet.toTop.map (c.ι.app k) (a' x) = SSet.toTop.map (c.ι.app j) (a x) := by
    change (SSet.toTop.map (F.map u) ≫ SSet.toTop.map (c.ι.app k)) (a x) = _
    rw [← Functor.map_comp, c.w]
    rfl
  have hub (x : T) : SSet.toTop.map (c.ι.app k) (b' x) = SSet.toTop.map (c.ι.app j) (b x) := by
    change (SSet.toTop.map (F.map u) ≫ SSet.toTop.map (c.ι.app k)) (b x) = _
    rw [← Functor.map_comp, c.w]
    rfl
  have he : (SSet.toTop.map (c.ι.app k)).hom.comp left =
      (SSet.toTop.map (c.ι.app k)).hom.comp right := by
    ext z
    rcases z with x | (x | ⟨t, x⟩)
    · exact (hga 0 x).trans ((H.map_zero_left x).trans (hua x).symm)
    · exact (hga 1 x).trans ((H.map_one_left x).trans (hub x).symm)
    · exact (hga t x.1).trans ((H.prop t x.1 x.2).trans (hua x.1).symm)
  obtain ⟨l, v, hv⟩ := compact_eq_eventually F c hc k left right he
  refine ⟨l, u ≫ v, ⟨{
    toContinuousMap := (SSet.toTop.map (F.map v)).hom.comp g
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro x
    have h := ContinuousMap.congr_fun hv (Sum.inl x)
    change SSet.toTop.map (F.map v) (g (0, x)) = SSet.toTop.map (F.map (u ≫ v)) (a x)
    rw [F.map_comp, Functor.map_comp]
    exact h
  · intro x
    have h := ContinuousMap.congr_fun hv (Sum.inr (Sum.inl x))
    change SSet.toTop.map (F.map v) (g (1, x)) = SSet.toTop.map (F.map (u ≫ v)) (b x)
    rw [F.map_comp, Functor.map_comp]
    exact h
  · intro t x hx
    have h := ContinuousMap.congr_fun hv (Sum.inr (Sum.inr (t, ⟨x, hx⟩)))
    change SSet.toTop.map (F.map v) (g (t, x)) = SSet.toTop.map (F.map (u ≫ v)) (a x)
    rw [F.map_comp, Functor.map_comp]
    exact h

end Topology.FilteredRealization
