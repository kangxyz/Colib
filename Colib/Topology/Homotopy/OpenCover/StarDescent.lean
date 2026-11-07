/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.StarTransitionData

/-!
# Star Descent

Genuine local transition data for a collar and disjoint interiors. Mixed
compatibility is the supplied natural isomorphism on the actual overlap; all
other comparisons are identities or are excluded by disjointness.
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
variable (U : Set X) (V : ι → Set X)
  (hdis : ∀ a b x, x ∈ V a → x ∈ V b → a = b)
  (F : FundamentalGroupoid U ⥤ C) (obj : ι → C)
  (η : ∀ i, FundamentalGroupoid.map ((ContinuousMap.inclusion (s := U ∩ (V i))
      Set.inter_subset_left)) ⋙ F ≅
    (Functor.const (FundamentalGroupoid ↥(U ∩ V i))).obj (obj i))

/-- Genuine local transition data for a collar and disjoint interiors. Mixed
compatibility is the supplied natural isomorphism on the actual overlap; all
other comparisons are identities or are excluded by disjointness. -/
def starData : TransitionData (C := C) (starSet U V) where
  chart := starFunctor U V F obj
  transition := starTransition U V hdis F obj η
  cocycle := starTransition_cocycle U V hdis F obj η
  naturality := by
    intro i j x y p hi hj
    cases i with
    | none =>
      cases j with
      | none => simp [starTransition, starFunctor]
      | some j =>
        have hp : Set.range p ⊆ U ∩ V j := fun _ hx => ⟨hi hx, hj hx⟩
        exact (η j).hom.naturality (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hp
            (p).source_mem_range⟩) (y := ⟨_, hp (p).target_mem_range⟩) p hp)))
    | some i =>
      cases j with
      | none =>
        have hp : Set.range p ⊆ U ∩ V i := fun _ hx => ⟨hj hx, hi hx⟩
        exact (η i).inv.naturality (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hp
            (p).source_mem_range⟩) (y := ⟨_, hp (p).target_mem_range⟩) p hp)))
      | some j =>
        have he := hdis i j x (hi p.source_mem_range) (hj p.source_mem_range)
        subst j
        simp [starTransition, starFunctor]

/-- The actual global descent from one collar chart and disjoint cell charts. -/
def starDescent (cover : CoverData (starSet U V)) : FundamentalGroupoid X ⥤ C :=
  (starData U V hdis F obj η).descent cover

end FundamentalGroupoid.OpenCover
