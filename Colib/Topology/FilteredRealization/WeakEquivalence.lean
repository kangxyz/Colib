/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FilteredRealization.Homotopy
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence
public import Colib.Topology.Homotopy.CubeBoundary

/-!
# Canonical weak invariance of filtered simplicial colimits

If every realized transition is an actual homotopy equivalence, each
canonical stage-to-colimit map is bijective on every finite homotopy set,
including π₀. The proof retains the actual induced maps and relies on proved
finite-subcomplex support and eventual equality, not on a Whitehead theorem.


Implementation provenance:
`Quillen/Topology/FilteredRealization/WeakEquivalence.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open Topology

noncomputable section
open Topology
open CategoryTheory Limits
open scoped Simplicial unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.FilteredRealization
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
include hc

/-- A based finite-dimensional cube in the colimit lifts to a later stage
with its entire boundary equal to the transported original basepoint. -/
theorem genLoop_factors (j : J) (x : |F.obj j|) (n : ℕ)
    (p : GenLoop (Fin n) |c.pt| (SSet.toTop.map (c.ι.app j) x)) :
    ∃ k, ∃ u : j ⟶ k,
      ∃ q : GenLoop (Fin n) |F.obj k| (SSet.toTop.map (F.map u) x),
        ∀ t, SSet.toTop.map (c.ι.app k) (q t) = p t := by
  obtain ⟨k, u, g, hg⟩ := compact_factors_above F c hc j p.val
  let S := Cube.boundary (Fin n)
  let : CompactSpace S := isCompact_iff_compactSpace.mp (Cube.isClosed_boundary (Fin n)).isCompact
  let gS : C(S, |F.obj k|) := ⟨fun t ↦ g t.1, by fun_prop⟩
  let bS : C(S, |F.obj k|) := ContinuousMap.const _ (SSet.toTop.map (F.map u) x)
  have hu : SSet.toTop.map (c.ι.app k) (SSet.toTop.map (F.map u) x) =
      SSet.toTop.map (c.ι.app j) x := by
    change (SSet.toTop.map (F.map u) ≫ SSet.toTop.map (c.ι.app k)) x = _
    rw [← Functor.map_comp, c.w]
    rfl
  have he : (SSet.toTop.map (c.ι.app k)).hom.comp gS =
      (SSet.toTop.map (c.ι.app k)).hom.comp bS := by
    ext t
    exact (ContinuousMap.congr_fun hg t.1).trans ((GenLoop.boundary p t.1 t.2).trans hu.symm)
  obtain ⟨l, v, hv⟩ := compact_eq_eventually F c hc k gS bS he
  let q : GenLoop (Fin n) |F.obj l| (SSet.toTop.map (F.map (u ≫ v)) x) :=
    ⟨(SSet.toTop.map (F.map v)).hom.comp g, by
      intro t ht
      have h := ContinuousMap.congr_fun hv ⟨t, ht⟩
      change SSet.toTop.map (F.map v) (g t) = SSet.toTop.map (F.map (u ≫ v)) x
      rw [F.map_comp, Functor.map_comp]
      exact h⟩
  refine ⟨l, u ≫ v, q, fun t ↦ ?_⟩
  change (SSet.toTop.map (F.map v) ≫ SSet.toTop.map (c.ι.app l)) (g t) = p t
  rw [← Functor.map_comp, c.w]
  exact ContinuousMap.congr_fun hg t

/-- Filtered colimits of actual realized homotopy equivalences preserve all
canonical finite-dimensional homotopy sets, at every stage point. This is
the weak theorem; no actual inverse of the colimit map is claimed here. -/
theorem stage_homotopyGroupMap_bijective
    (e : ∀ {j k : J} (_u : j ⟶ k), ContinuousMap.HomotopyEquiv |F.obj j| |F.obj k|)
    (he : ∀ {j k : J} (u : j ⟶ k), (e u).toFun = (SSet.toTop.map (F.map u)).hom)
    (j : J) (x : |F.obj j|) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (SSet.toTop.map (c.ι.app j)).hom (x := x) rfl) := by
  have hstep {k : J} (u : j ⟶ k) : Function.Bijective
      (HomotopyGroup.map (N := Fin n) (SSet.toTop.map (F.map u)).hom (x := x) rfl) := by
    let E : ContinuousMap.HomotopyEquiv |F.obj j| |F.obj k| := {
      e u with
      toFun := (SSet.toTop.map (F.map u)).hom
      left_inv := by simpa only [he u] using (e u).left_inv
      right_inv := by simpa only [he u] using (e u).right_inv }
    exact homotopyGroupMap_bijective_of_homotopyEquiv E rfl n
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        obtain ⟨H⟩ := Quotient.exact hab
        obtain ⟨k, u, Hk⟩ := homotopyRel_factors F c hc j (Cube.boundary (Fin n))
          (Cube.isClosed_boundary (Fin n)).isCompact H
        exact (hstep u).1 (Quotient.sound Hk)
  · intro a
    induction a using Quotient.inductionOn with | h p =>
      obtain ⟨k, u, q, hq⟩ := genLoop_factors F c hc j x n p
      obtain ⟨a, ha⟩ := (hstep u).2 (Quotient.mk' q)
      have hw : (SSet.toTop.map (c.ι.app k)).hom.comp (SSet.toTop.map (F.map u)).hom =
          (SSet.toTop.map (c.ι.app j)).hom := by
        rw [← TopCat.hom_comp, ← Functor.map_comp, c.w]
      have hp := ContinuousMap.congr_fun hw x
      have hmap : HomotopyGroup.map (SSet.toTop.map (c.ι.app k)).hom hp (Quotient.mk' q) =
          Quotient.mk' p := by
        apply congrArg Quotient.mk'
        exact GenLoop.ext _ _ hq
      have hcomp := HomotopyGroup.map_comp (N := Fin n)
        (SSet.toTop.map (F.map u)).hom rfl (SSet.toTop.map (c.ι.app k)).hom hp a
      have hcongr := homotopyGroupMap_congr (N := Fin n) hw
        (x := x) hp rfl
      refine ⟨a, ?_⟩
      exact (congrFun hcongr a).symm.trans
        (hcomp.trans ((congrArg (HomotopyGroup.map (SSet.toTop.map (c.ι.app k)).hom hp) ha).trans
          hmap))

/-- The canonical positive-dimensional group isomorphism has the actual
cocone leg as its forward homomorphism. -/
def stagePiEquiv
    (e : ∀ {j k : J} (_u : j ⟶ k), ContinuousMap.HomotopyEquiv |F.obj j| |F.obj k|)
    (he : ∀ {j k : J} (u : j ⟶ k), (e u).toFun = (SSet.toTop.map (F.map u)).hom)
    (j : J) (x : |F.obj j|) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) |F.obj j| x ≃*
      HomotopyGroup.Pi (n + 1) |c.pt| (SSet.toTop.map (c.ι.app j) x) :=
  MulEquiv.ofBijective (HomotopyGroup.piMap n (SSet.toTop.map (c.ι.app j)).hom rfl)
    (stage_homotopyGroupMap_bijective F c hc e he j x (n + 1))

/-- The forward homomorphism is induced by the prescribed cocone leg. -/
@[simp] theorem stagePiEquiv_coe
    (e : ∀ {j k : J} (_u : j ⟶ k), ContinuousMap.HomotopyEquiv |F.obj j| |F.obj k|)
    (he : ∀ {j k : J} (u : j ⟶ k), (e u).toFun = (SSet.toTop.map (F.map u)).hom)
    (j : J) (x : |F.obj j|) (n : ℕ) :
    (stagePiEquiv F c hc e he j x n : HomotopyGroup.Pi (n + 1) |F.obj j| x →*
      HomotopyGroup.Pi (n + 1) |c.pt| (SSet.toTop.map (c.ι.app j) x)) =
      HomotopyGroup.piMap n (SSet.toTop.map (c.ι.app j)).hom rfl := rfl

end Topology.FilteredRealization
