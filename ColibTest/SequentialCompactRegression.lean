/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Category.TopCat.SequentialColimit.FundamentalGroupoid

/-! Actual-stage-map regression tests. Fullness is not an equivalence assertion. -/
@[expose] public noncomputable section

open CategoryTheory Limits Topology
universe u v
namespace TopCat.SequentialColimit
variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F} (hc : IsColimit c)
  [∀ n, T1Space (F.obj n)]
  (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))

example (n : ℕ) : IsClosedEmbedding (c.ι.app n) := stage_isClosedEmbedding hc hF n
example : T1Space c.pt := t1Space_colimit hc hF

example {X : Type v} [TopologicalSpace X] [CompactSpace X] (f : C(X, c.pt))
    (k : ℕ) : ∃ n, k ≤ n ∧ ∃ g : C(X, F.obj n), ∀ x, c.ι.app n (g x) = f x :=
  continuousMap_factors_above hc hF f k

example {X : TopCat.{u}} [CompactSpace X] (f : X ⟶ c.pt) :
    ∃ n, ∃ g : X ⟶ F.obj n, g ≫ c.ι.app n = f := hom_factors hc hF f

example (k : ℕ) {x y : F.obj k} (p : Path (c.ι.app k x) (c.ι.app k y)) :
    ∃ n, ∃ h : k ≤ n,
      ∃ q : Path (F.map (homOfLE h) x) (F.map (homOfLE h) y),
        ∀ t, c.ι.app n (q t) = p t := path_factors hc hF k p

example (k : ℕ)
    (hfull : ∀ n, k ≤ n →
      (FundamentalGroupoid.map (F.map (homOfLE (Nat.le_succ n))).hom).Full) :
    (FundamentalGroupoid.map (c.ι.app k).hom).Full :=
  stage_fundamentalGroupoid_full hc hF k hfull

example {K : Set c.pt} (hK : IsCompact K) :
    ∃ n, K ⊆ Set.range (c.ι.app n) :=
  isCompact_subset_stageRange_of_closedEmbeddings hc hF hK

example {X : Type v} [TopologicalSpace X] [CompactSpace X] (f : C(X, c.pt)) :
    ∃ n, ∃ g : C(X, F.obj n), ∀ x, c.ι.app n (g x) = f x :=
  continuousMap_factors hc hF f

example (k : ℕ)
    (hfull : ∀ n, k ≤ n →
      (FundamentalGroupoid.map (F.map (homOfLE (Nat.le_succ n))).hom).Full)
    {x y : F.obj k} (p : Path (c.ι.app k x) (c.ι.app k y)) :
    ∃ r : Path x y, (r.map (c.ι.app k).hom.continuous).Homotopic p :=
  path_homotopic_from_stage hc hF k hfull p

end TopCat.SequentialColimit

