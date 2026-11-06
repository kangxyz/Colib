/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FilteredRealization.Homotopy

/-!
# Exact compact homotopy-square factorization for filtered realization

The map of a compact pair and its full comparison homotopy are represented
at one later stage. Both endpoint equations are detected simultaneously;
the lifted homotopy retains its exact image in the colimit. This supplies
the finite-stage input for homotopy extension and lifting arguments.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/FilteredRealization/HELP.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The arbitrary filtered category,
actual cocone maps, exact factorization and universe parameters are retained. -/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits SSet
open scoped Simplicial unitInterval
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.FilteredRealization
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
include hc

/-- Simultaneously factor a compact homotopy-commuting square through a
later original stage. The original stage map is retained through one arrow,
and the entire comparison homotopy is preserved exactly under the cocone. -/
theorem compact_square_homotopy_factors
    {A : Type v} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    [CompactSpace A] [CompactSpace B]
    (j : J) (i : C(A, B)) (a : C(A, |F.obj j|)) (b : C(B, |c.pt|))
    (H : ((SSet.toTop.map (c.ι.app j)).hom.comp a).Homotopy (b.comp i)) :
    ∃ k, ∃ u : j ⟶ k, ∃ b' : C(B, |F.obj k|),
      ∃ K : ((SSet.toTop.map (F.map u)).hom.comp a).Homotopy (b'.comp i),
        (SSet.toTop.map (c.ι.app k)).hom.comp b' = b ∧
          ∀ t x, SSet.toTop.map (c.ι.app k) (K (t, x)) = H (t, x) := by
  let joint : C(B ⊕ (unitInterval × A), |c.pt|) :=
    ⟨Sum.elim b H.toContinuousMap, b.continuous.sumElim H.continuous⟩
  obtain ⟨k, u, g, hg⟩ := compact_factors_above F c hc j joint
  let b₀ : C(B, |F.obj k|) := ⟨fun x ↦ g (Sum.inl x), by fun_prop⟩
  let L : C(unitInterval × A, |F.obj k|) := ⟨fun z ↦ g (Sum.inr z), by fun_prop⟩
  let L₀ : C(A, |F.obj k|) := ⟨fun x ↦ L (0, x), by fun_prop⟩
  let L₁ : C(A, |F.obj k|) := ⟨fun x ↦ L (1, x), by fun_prop⟩
  let a₀ := (SSet.toTop.map (F.map u)).hom.comp a
  let left : C(A ⊕ A, |F.obj k|) := ⟨Sum.elim L₀ L₁, L₀.continuous.sumElim L₁.continuous⟩
  let right : C(A ⊕ A, |F.obj k|) :=
    ⟨Sum.elim a₀ (b₀.comp i), a₀.continuous.sumElim (b₀.comp i).continuous⟩
  have hb (x : B) : SSet.toTop.map (c.ι.app k) (b₀ x) = b x := ContinuousMap.congr_fun hg
    (Sum.inl x)
  have hL (t : unitInterval) (x : A) : SSet.toTop.map (c.ι.app k) (L (t, x)) = H (t, x) :=
    ContinuousMap.congr_fun hg (Sum.inr (t, x))
  have ha (x : A) : SSet.toTop.map (c.ι.app k) (a₀ x) = SSet.toTop.map (c.ι.app j) (a x) := by
    change (SSet.toTop.map (F.map u) ≫ SSet.toTop.map (c.ι.app k)) (a x) = _
    rw [← Functor.map_comp, c.w]
    rfl
  have he : (SSet.toTop.map (c.ι.app k)).hom.comp left =
      (SSet.toTop.map (c.ι.app k)).hom.comp right := by
    ext x
    cases x with
    | inl x => exact (hL 0 x).trans ((H.map_zero_left x).trans (ha x).symm)
    | inr x => exact (hL 1 x).trans ((H.map_one_left x).trans (hb (i x)).symm)
  obtain ⟨l, v, hv⟩ := compact_eq_eventually F c hc k left right he
  let b' := (SSet.toTop.map (F.map v)).hom.comp b₀
  let K : ((SSet.toTop.map (F.map (u ≫ v))).hom.comp a).Homotopy (b'.comp i) := {
    toContinuousMap := (SSet.toTop.map (F.map v)).hom.comp L
    map_zero_left := by
      intro x
      have h := ContinuousMap.congr_fun hv (Sum.inl x)
      change SSet.toTop.map (F.map v) (L (0, x)) = SSet.toTop.map (F.map (u ≫ v)) (a x)
      rw [F.map_comp, Functor.map_comp]
      exact h
    map_one_left := fun x ↦ ContinuousMap.congr_fun hv (Sum.inr x) }
  refine ⟨l, u ≫ v, b', K, ContinuousMap.ext (fun x ↦ ?_), fun t x ↦ ?_⟩
  · change (SSet.toTop.map (F.map v) ≫ SSet.toTop.map (c.ι.app l)) (b₀ x) = b x
    rw [← Functor.map_comp, c.w]
    exact hb x
  · change (SSet.toTop.map (F.map v) ≫ SSet.toTop.map (c.ι.app l)) (L (t, x)) = H (t, x)
    rw [← Functor.map_comp, c.w]
    exact hL t x

end Topology.FilteredRealization
