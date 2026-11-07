/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.HomologySupport
public import Colib.Topology.LocalCoefficients.TelescopeTransitions
public import Colib.Topology.ClassifyingSpace.TelescopeComponents

/-!
Adapted from `Quillen/Topology/LocalCoefficients/TelescopeHomologySupport.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining original transition maps.

 # Genuine stabilized finite support for original telescope homology classes -/

@[expose] public section

open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory
universe u
namespace CategoryTheory.Grothendieck.Telescope
open FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (F : ℕ ⥤ Cat.{u, u})

/-- Move an actual class by one original transition so its controlling finite
point support has exactly the infinite telescope's component relations. -/
theorem localHomology_stage_finite_support_stabilizes (n : ℕ)
    (A : System.{u, u} (ClassifyingSpace (Model F))) (d : ℕ)
    (x : homology (pullback (classifyingSpaceMap (Grothendieck.ι F n)).hom A) d) :
    ∃ (m : ℕ) (h : n ≤ m) (s : Finset (ClassifyingSpace (F.obj m))),
      (∀ a ∈ s, ∀ b ∈ s,
        Joined (classifyingSpaceMap (Grothendieck.ι F m) a)
          (classifyingSpaceMap (Grothendieck.ι F m) b) → Joined a b) ∧
      (∀ (B : System.{u, u} (ClassifyingSpace (F.obj m)))
        (η θ : pullback (classifyingSpaceMap (Grothendieck.ι F m)).hom A ⟶ B),
        (∀ p ∈ s, η.app (FundamentalGroupoid.mk p) = θ.app (FundamentalGroupoid.mk p)) →
        coefficientHomologyMap η d (stageHomologyTransition F h A d x) =
          coefficientHomologyMap θ d (stageHomologyTransition F h A d x)) := by
  classical
  obtain ⟨s, hs⟩ := homology_exists_finite_pushforward_test_set _ d x
  obtain ⟨m, h, hm⟩ := stage_finite_component_relations_stabilize F n s
  let t := (classifyingSpaceMap (F.map (homOfLE h)).toFunctor).hom
  refine ⟨m, h, s.image t, ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    apply (hm a' ha' b' hb').mpr
    exact (show Joined _ _ from ⟨(stageTransitionClassifyingHomotopy F h).evalAt a'⟩).trans
      (hab.trans ⟨((stageTransitionClassifyingHomotopy F h).evalAt b').symm⟩)
  · intro B η θ hηθ
    exact hs t _ B (stagePullbackIso F h A).hom η θ
      (fun p hp ↦ hηθ (t p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

end CategoryTheory.Grothendieck.Telescope
