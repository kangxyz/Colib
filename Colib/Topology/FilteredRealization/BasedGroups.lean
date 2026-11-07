/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FilteredRealization.WeakEquivalence

/-! # Actual based homotopy groups of filtered simplicial colimits

With a strictly compatible family of actual realization points, every finite
homotopy class has a stage representative, and equality of stage classes is
detected at a later stage. No transition equivalence or realization-map
injectivity is assumed. Cube boundaries are retained by the proved compact
factorization and relative-homotopy lifting theorems.


Implementation provenance:
`Quillen/Topology/FilteredRealization/BasedGroups.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open Topology

noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Simplicial
universe u
namespace Topology.FilteredRealization
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
  (x : ∀ j, |F.obj j|) (z : |c.pt|)
  (hx : ∀ {j k} (f : j ⟶ k), SSet.toTop.map (F.map f) (x j) = x k)
  (hz : ∀ j, SSet.toTop.map (c.ι.app j) (x j) = z)
include hc hx hz

/-- Every actual finite-dimensional based homotopy class comes from one stage. -/
theorem homotopyGroupMap_jointlySurjective (n : ℕ) (a : HomotopyGroup.Pi n |c.pt| z) :
    ∃ j, ∃ b : HomotopyGroup.Pi n |F.obj j| (x j),
      HomotopyGroup.map (SSet.toTop.map (c.ι.app j)).hom (hz j) b = a := by
  induction a using Quotient.inductionOn with | h p =>
    let j : J := Classical.choice (IsFiltered.nonempty (C := J))
    let p' : GenLoop (Fin n) |c.pt| (SSet.toTop.map (c.ι.app j) (x j)) :=
      ⟨p.val, fun t ht ↦ (GenLoop.boundary p t ht).trans (hz j).symm⟩
    obtain ⟨k, f, q, hq⟩ := genLoop_factors F c hc j (x j) n p'
    let q' : GenLoop (Fin n) |F.obj k| (x k) :=
      ⟨q.val, fun t ht ↦ (GenLoop.boundary q t ht).trans (hx f)⟩
    refine ⟨k, Quotient.mk' q', ?_⟩
    apply congrArg Quotient.mk'
    exact GenLoop.ext _ _ hq

/-- Equality of original based stage classes is witnessed at a later stage. -/
theorem homotopyGroupMap_eq_eventually (j : J) (n : ℕ)
    (a b : HomotopyGroup.Pi n |F.obj j| (x j))
    (h : HomotopyGroup.map (SSet.toTop.map (c.ι.app j)).hom (hz j) a =
      HomotopyGroup.map (SSet.toTop.map (c.ι.app j)).hom (hz j) b) :
    ∃ k, ∃ f : j ⟶ k,
      HomotopyGroup.map (SSet.toTop.map (F.map f)).hom (hx f) a =
        HomotopyGroup.map (SSet.toTop.map (F.map f)).hom (hx f) b := by
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      obtain ⟨H⟩ := Quotient.exact h
      obtain ⟨k, f, Hk⟩ := homotopyRel_factors F c hc j (Cube.boundary (Fin n))
        (Cube.isClosed_boundary (Fin n)).isCompact H
      exact ⟨k, f, Quotient.sound Hk⟩

/-- The original induced positive-dimensional group maps are jointly surjective. -/
theorem piMap_jointlySurjective (n : ℕ) (a : HomotopyGroup.Pi (n + 1) |c.pt| z) :
    ∃ j, ∃ b : HomotopyGroup.Pi (n + 1) |F.obj j| (x j),
      HomotopyGroup.piMap n (SSet.toTop.map (c.ι.app j)).hom (hz j) b = a :=
  homotopyGroupMap_jointlySurjective F c hc x z hx hz (n + 1) a

/-- The original induced group maps detect equality at a genuine later stage. -/
theorem piMap_eq_eventually (j : J) (n : ℕ)
    (a b : HomotopyGroup.Pi (n + 1) |F.obj j| (x j))
    (h : HomotopyGroup.piMap n (SSet.toTop.map (c.ι.app j)).hom (hz j) a =
      HomotopyGroup.piMap n (SSet.toTop.map (c.ι.app j)).hom (hz j) b) :
    ∃ k, ∃ f : j ⟶ k,
      HomotopyGroup.piMap n (SSet.toTop.map (F.map f)).hom (hx f) a =
        HomotopyGroup.piMap n (SSet.toTop.map (F.map f)).hom (hx f) b :=
  homotopyGroupMap_eq_eventually F c hc x z hx hz j (n + 1) a b h

/-- In particular a stage class mapping to one becomes one at a later stage. -/
theorem piMap_eq_one_eventually (j : J) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) |F.obj j| (x j))
    (h : HomotopyGroup.piMap n (SSet.toTop.map (c.ι.app j)).hom (hz j) a = 1) :
    ∃ k, ∃ f : j ⟶ k, HomotopyGroup.piMap n (SSet.toTop.map (F.map f)).hom (hx f) a = 1 := by
  have h' : HomotopyGroup.piMap n (SSet.toTop.map (c.ι.app j)).hom (hz j) a =
      HomotopyGroup.piMap n (SSet.toTop.map (c.ι.app j)).hom (hz j) 1 := h.trans (map_one _).symm
  obtain ⟨k, f, hf⟩ := piMap_eq_eventually F c hc x z hx hz j n a 1 h'
  exact ⟨k, f, hf.trans (map_one _)⟩

end Topology.FilteredRealization
