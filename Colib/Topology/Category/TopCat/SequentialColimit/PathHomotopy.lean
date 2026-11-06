/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Category.TopCat.SequentialColimit.Compact
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Path Homotopy

An actual homotopy between two paths from one stage lifts, with exactly those
transported boundary paths and fixed endpoints, to a common later stage.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopCat Topology
open scoped unitInterval
universe u
namespace TopCat.SequentialColimit
variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F}

/-- An actual homotopy between two paths from one stage lifts, with exactly those
transported boundary paths and fixed endpoints, to a common later stage. -/
theorem path_homotopy_factors (hc : IsColimit c) [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (k : ℕ) {x y : F.obj k} (p q : Path x y)
    (H : (p.map (c.ι.app k).hom.continuous).Homotopy
      (q.map (c.ι.app k).hom.continuous)) :
    ∃ n, ∃ h : k ≤ n,
      (p.map (F.map (homOfLE h)).hom.continuous).Homotopic
        (q.map (F.map (homOfLE h)).hom.continuous) := by
  obtain ⟨n, h, g, hg⟩ := continuousMap_factors_above hc hF
    (⟨H, H.continuous⟩ : C(I × I, c.pt)) k
  have hinj := (stage_isClosedEmbedding hc hF n).injective
  have hw (z : F.obj k) : c.ι.app n (F.map (homOfLE h) z) = c.ι.app k z :=
    ConcreteCategory.congr_hom (c.w (homOfLE h)) z
  refine ⟨n, h, ⟨{
    toFun := g
    continuous_toFun := g.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro t
    apply hinj
    exact (hg (0, t)).trans ((H.map_zero_left t).trans (hw (p t)).symm)
  · intro t
    apply hinj
    exact (hg (1, t)).trans ((H.map_one_left t).trans (hw (q t)).symm)
  · intro t z hz
    apply hinj
    exact (hg (t, z)).trans ((H.prop' t z hz).trans (hw (p z)).symm)

/-- Equality of actual path classes in the colimit is already equality in one
later stage, without any assumption that a functor out of the colimit exists. -/
theorem path_homotopic_factors (hc : IsColimit c) [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (k : ℕ) {x y : F.obj k} (p q : Path x y)
    (H : (p.map (c.ι.app k).hom.continuous).Homotopic
      (q.map (c.ι.app k).hom.continuous)) :
    ∃ n, ∃ h : k ≤ n,
      (p.map (F.map (homOfLE h)).hom.continuous).Homotopic
        (q.map (F.map (homOfLE h)).hom.continuous) := by
  obtain ⟨H⟩ := H
  exact path_homotopy_factors hc hF k p q H

end TopCat.SequentialColimit
