/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.TelescopeTranslation
public import Colib.Topology.LocalCoefficients.TelescopeHomologySupport
public import Colib.Topology.LocalCoefficients.TelescopeHomologyElements

/-!
Adapted from `Quillen/Topology/LocalCoefficients/TelescopeTranslationKernel.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual original
stage arrows, finite support and coefficient corrections.
 # Original finite-stage kernel representatives for telescope translations -/

@[expose] public section

open CategoryTheory.Grothendieck.Telescope
open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
open FundamentalGroupoid.LocalCoefficients Grothendieck.Telescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e P : C)
  (A : System.{max u v, max u v} (ClassifyingSpace (Model e))) (d : ℕ)

/-- A kernel class is represented at an original stage where the actual finite
left-action homology map already kills it. -/
theorem translation_kernel_exists_stage
    (x : homology (pullback (classifyingSpaceMap (leftTranslation e P)).hom A) d)
    (hx : pushforwardHomologyMap (classifyingSpaceMap (leftTranslation e P)).hom A d x = 0) :
    ∃ (n : ℕ) (y : homology (pullback (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom
      (pullback (classifyingSpaceMap (leftTranslation e P)).hom A)) d),
      pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom
        (pullback (classifyingSpaceMap (leftTranslation e P)).hom A) d y = x ∧
      stageTranslationHomology e P A d n y = 0 := by
  let U := (classifyingSpaceMap (leftTranslation e P)).hom
  obtain ⟨n, y, hy⟩ := localHomology_exists_stage (diagram e) (pullback U A) d x
  have hz : pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom A d
      (stageTranslationHomology e P A d n y) = 0 := by
    change (stageTranslationHomology e P A d n ≫
      pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom A d) y = 0
    rw [stageTranslationHomology, squareHomologyMap_to_target]
    change pushforwardHomologyMap U A d
      (pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom
        (pullback U A) d y) = 0
    rw [hy]
    exact hx
  obtain ⟨m, h, hm⟩ := (localHomology_stage_eq_zero_iff (diagram e) n A d _).mp hz
  refine ⟨m, stageHomologyTransition (diagram e) h (pullback U A) d y, ?_, ?_⟩
  · have he := congrArg (fun f ↦ f y)
      (stageHomologyTransition_to_infinite (diagram e) h (pullback U A) d)
    exact he.trans hy
  · have he := congrArg (fun f ↦ f y) (stageTranslationHomology_transition e P A d h)
    exact he.symm.trans hm

/-- The same kernel class can be represented with a finite coefficient-testing
support whose components inject into those of the actual infinite telescope. -/
theorem translation_kernel_exists_stable_support
    (x : homology (pullback (classifyingSpaceMap (leftTranslation e P)).hom A) d)
    (hx : pushforwardHomologyMap (classifyingSpaceMap (leftTranslation e P)).hom A d x = 0) :
    ∃ (n : ℕ) (y : homology (pullback (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom
      (pullback (classifyingSpaceMap (leftTranslation e P)).hom A)) d)
      (s : Finset (ClassifyingSpace ((diagram e).obj n))),
      pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom
        (pullback (classifyingSpaceMap (leftTranslation e P)).hom A) d y = x ∧
      stageTranslationHomology e P A d n y = 0 ∧
      (∀ a ∈ s, ∀ b ∈ s,
        Joined (classifyingSpaceMap (Grothendieck.ι (diagram e) n) a)
          (classifyingSpaceMap (Grothendieck.ι (diagram e) n) b) → Joined a b) ∧
      (∀ (B : System.{max u v, max u v} (ClassifyingSpace ((diagram e).obj n)))
        (η θ : pullback (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom
          (pullback (classifyingSpaceMap (leftTranslation e P)).hom A) ⟶ B),
        (∀ p ∈ s, η.app (FundamentalGroupoid.mk p) = θ.app (FundamentalGroupoid.mk p)) →
        coefficientHomologyMap η d y = coefficientHomologyMap θ d y) := by
  let U := (classifyingSpaceMap (leftTranslation e P)).hom
  obtain ⟨n, y, hy, hz⟩ := translation_kernel_exists_stage e P A d x hx
  obtain ⟨m, h, s, hs, ht⟩ := localHomology_stage_finite_support_stabilizes
    (diagram e) n (pullback U A) d y
  refine ⟨m, stageHomologyTransition (diagram e) h (pullback U A) d y, s, ?_, ?_, hs, ht⟩
  · have he := congrArg (fun f ↦ f y)
      (stageHomologyTransition_to_infinite (diagram e) h (pullback U A) d)
    exact he.trans hy
  · have he := congrArg (fun f ↦ f y) (stageTranslationHomology_transition e P A d h)
    change stageHomologyTransition (diagram e) h A d
      (stageTranslationHomology e P A d n y) = _ at he
    rw [hz, map_zero] at he
    exact he.symm

end CategoryTheory.MonoidalCategory.TranslationTelescope
