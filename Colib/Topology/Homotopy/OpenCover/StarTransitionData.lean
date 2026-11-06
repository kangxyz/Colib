/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.TransitionData
public import Colib.Topology.Homotopy.OpenCover.CollarOverlap

/-!
# Star Transition Data

A collar chart and a family of disjoint cell charts.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable {C : Type w} [Category.{z} C]

/-- A collar chart and a family of disjoint cell charts. -/
def starSet (U : Set X) (V : ι → Set X) : Option ι → Set X
  | none => U
  | some i => V i

/-- The actual collar functor and the specified constant interior functors. -/
def starFunctor (U : Set X) (V : ι → Set X) (F : FundamentalGroupoid U ⥤ C)
    (obj : ι → C) (i : Option ι) : FundamentalGroupoid (starSet U V i) ⥤ C :=
  match i with
  | none => F
  | some i => (Functor.const (FundamentalGroupoid (V i))).obj (obj i)

variable (U : Set X) (V : ι → Set X)
  (hdis : ∀ a b x, x ∈ V a → x ∈ V b → a = b)
  (F : FundamentalGroupoid U ⥤ C) (obj : ι → C)
  (η : ∀ i, FundamentalGroupoid.map ((ContinuousMap.inclusion (s := U ∩ (V i))
      Set.inter_subset_left)) ⋙ F ≅
    (Functor.const (FundamentalGroupoid ↥(U ∩ V i))).obj (obj i))

/-- Actual overlap transition isos, with inverse orientation on cell-to-collar overlaps. -/
def starTransition (i j : Option ι) (x : X)
    (hi : x ∈ starSet U V i) (hj : x ∈ starSet U V j) :
    (starFunctor U V F obj i).obj (FundamentalGroupoid.mk ⟨x, hi⟩) ≅
      (starFunctor U V F obj j).obj (FundamentalGroupoid.mk ⟨x, hj⟩) := by
  cases i with
  | none =>
    cases j with
    | none => exact Iso.refl _
    | some j => exact (η j).app (FundamentalGroupoid.mk ⟨x, hi, hj⟩)
  | some i =>
    cases j with
    | none => exact ((η i).app (FundamentalGroupoid.mk ⟨x, hj, hi⟩)).symm
    | some j =>
      have he := hdis i j x hi hj
      subst j
      exact Iso.refl _

/-- Pairwise disjointness makes the actual transition cocycle automatic. -/
theorem starTransition_cocycle (i j k : Option ι) (x : X)
    (hi : x ∈ starSet U V i) (hj : x ∈ starSet U V j) (hk : x ∈ starSet U V k) :
    starTransition U V hdis F obj η i j x hi hj ≪≫
      starTransition U V hdis F obj η j k x hj hk =
        starTransition U V hdis F obj η i k x hi hk := by
  rcases i with _ | i <;> rcases j with _ | j <;> rcases k with _ | k
  all_goals try (have he := hdis i j x hi hj; subst j)
  all_goals try (have he := hdis i k x hi hk; subst k)
  all_goals try (have he := hdis j k x hj hk; subst k)
  all_goals simp [starTransition]

end FundamentalGroupoid.OpenCover
