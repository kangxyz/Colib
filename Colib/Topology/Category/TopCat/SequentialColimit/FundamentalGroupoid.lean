/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Category.TopCat.SequentialColimit.Compact
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Fullness through a sequential colimit

Compact path factorization proves that a tail of closed-embedding attachments
which add no fundamental-groupoid generators also adds no generators at its
actual colimit.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/Realization/CompactFundamentalGroupoid.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Only namespace and dependency
ownership change. The actual cocone maps, endpoints, universe parameters and
hypotheses are retained. This is a generic sequential-colimit theorem, with
no realization or Theorem A/B assumption.
-/
@[expose] public section

open Topology


noncomputable section

open CategoryTheory Limits

universe u

namespace TopCat.SequentialColimit

variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F}

/-- Fullness on fundamental groupoids propagates through any finite composite
of transitions beyond the prescribed starting stage. -/
theorem transition_fundamentalGroupoid_full (k : ℕ)
    (hfull : ∀ n, k ≤ n →
      (FundamentalGroupoid.map (F.map (homOfLE (Nat.le_succ n))).hom).Full)
    {n : ℕ} (h : k ≤ n) :
    (FundamentalGroupoid.map (F.map (homOfLE h)).hom).Full := by
  induction n, h using Nat.le_induction with
  | base =>
      simp only [homOfLE_refl, CategoryTheory.Functor.map_id, TopCat.hom_id,
        FundamentalGroupoid.map_id]
      infer_instance
  | succ n h ih =>
    let := ih
    let := hfull n h
    have heq : (homOfLE (Nat.le.step h) : k ⟶ n + 1) =
        homOfLE h ≫ homOfLE (Nat.le_succ n) := Subsingleton.elim _ _
    rw [heq, F.map_comp]
    change (FundamentalGroupoid.map
      ((F.map (homOfLE (Nat.le_succ n))).hom.comp (F.map (homOfLE h)).hom)).Full
    rw [FundamentalGroupoid.map_comp]
    infer_instance

/-- Every path in a closed-embedding sequential colimit between points of
stage `k` is homotopic to a path from that stage, provided all subsequent
attachments are full on fundamental groupoids. -/
theorem path_homotopic_from_stage (hc : IsColimit c)
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (k : ℕ)
    (hfull : ∀ n, k ≤ n →
      (FundamentalGroupoid.map (F.map (homOfLE (Nat.le_succ n))).hom).Full)
    {x y : F.obj k} (p : Path (c.ι.app k x) (c.ι.app k y)) :
    ∃ r : Path x y, (r.map (c.ι.app k).hom.continuous).Homotopic p := by
  obtain ⟨n, h, q, hq⟩ := path_factors hc hF k p
  let := transition_fundamentalGroupoid_full k hfull h
  let G := FundamentalGroupoid.map (F.map (homOfLE h)).hom
  obtain ⟨r, hr⟩ := G.map_surjective
    (X := FundamentalGroupoid.mk x) (Y := FundamentalGroupoid.mk y)
    (Path.Homotopic.Quotient.mk q)
  obtain ⟨r, rfl⟩ := Path.Homotopic.Quotient.mk_surjective r
  have hrq : (r.map (F.map (homOfLE h)).hom.continuous).Homotopic q :=
    Path.Homotopic.Quotient.eq.mp hr
  have hx : c.ι.app k x = c.ι.app n (F.map (homOfLE h) x) :=
    (ConcreteCategory.congr_hom (c.w (homOfLE h)) x).symm
  have hy : c.ι.app k y = c.ι.app n (F.map (homOfLE h) y) :=
    (ConcreteCategory.congr_hom (c.w (homOfLE h)) y).symm
  have hh := (hrq.map (c.ι.app n).hom).pathCast hx hy
  have heq₁ : (((r.map (F.map (homOfLE h)).hom.continuous).map
      (c.ι.app n).hom.continuous).cast hx hy) = r.map (c.ι.app k).hom.continuous := by
    ext t
    exact ConcreteCategory.congr_hom (c.w (homOfLE h)) (r t)
  have heq₂ : ((q.map (c.ι.app n).hom.continuous).cast hx hy) = p := by
    ext t
    exact hq t
  exact ⟨r, heq₁ ▸ heq₂ ▸ hh⟩

/-- Fullness on fundamental groupoids passes from all transitions in a tail
to the tail's inclusion into the actual sequential colimit. -/
theorem stage_fundamentalGroupoid_full (hc : IsColimit c)
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (k : ℕ)
    (hfull : ∀ n, k ≤ n →
      (FundamentalGroupoid.map (F.map (homOfLE (Nat.le_succ n))).hom).Full) :
    (FundamentalGroupoid.map (c.ι.app k).hom).Full where
  map_surjective := by
    intro x y p
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
    obtain ⟨r, hr⟩ := path_homotopic_from_stage hc hF k hfull p
    exact ⟨Path.Homotopic.Quotient.mk r, Path.Homotopic.Quotient.eq.mpr hr⟩

end TopCat.SequentialColimit

attribute [colib_tag "COL-0089",
  colib_ref "DuggerIsaksenHypercovers" "Appendix A, Lemma A.3, pages 17-18"
    "ingredient"
    "Compact path factorization for fullness of a tail inclusion, not faithfulness"]
  TopCat.SequentialColimit.path_homotopic_from_stage
  TopCat.SequentialColimit.stage_fundamentalGroupoid_full
