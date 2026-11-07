/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.ProductFiberHELP
public import Colib.Topology.HomotopyFiber.CartesianDetection
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceCancellation

/-! # Original cartesian transition squares from genuine split row comparisons

A genuine row comparison to a simplicial product, and a strictly natural
split section, prove the complete weak property of the original transition
on actual homotopy fibers. Connectedness then detects the original canonical
constant-path comparison of the row square. No global realization gluing or
fiber-equivalence conclusion is supplied as a hypothesis.


Implementation provenance:
`Quillen/Topology/Realization/SplitFiberCartesian.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
namespace SSet.SplitRealizationFiber
variable {A B E B' E' : SSet.{u}}
  (χ : E ⟶ A ⊗ B) (χ' : E' ⟶ A ⊗ B')
  (s : A ⟶ E) (s' : A ⟶ E') (y : B _⦋0⦌) (y' : B' _⦋0⦌)
  (hs : s ≫ χ = ProductRealization.vertexSection A B y)
  (hs' : s' ≫ χ' = ProductRealization.vertexSection A B' y')
  (a : E ⟶ E') (b : B ⟶ B')
  (sq : a ≫ χ' ≫ snd A B' = χ ≫ snd A B ≫ b)
  (ha : s ≫ a = s')

include sq

/-- The actual realized row square retains the complete original projections. -/
theorem transitionSquare :
    (projection χ').comp (SSet.toTop.map a).hom =
      (SSet.toTop.map b).hom.comp (projection χ) := by
  simpa only [projection, Functor.map_comp, TopCat.hom_comp, ContinuousMap.comp_assoc] using
    congrArg (fun f ↦ (SSet.toTop.map f).hom) sq

include hs hs' ha

/-- The actual first projection of the target fiber cancels the original
transition and original split inclusion, as an equality of continuous maps.
The target fiber is taken over the literal image of the source basepoint. -/
theorem firstProjection_transition_inclusion :
    (firstProjection χ' (SSet.toTop.map b (SSet.realizationPoint y))).comp
      ((HomotopyPullback.transitionFiber (projection χ) (projection χ')
        (SSet.toTop.map a).hom (SSet.toTop.map b).hom
        (transitionSquare χ χ' a b sq) (SSet.realizationPoint y)).comp (inclusion χ s y hs)) =
      ContinuousMap.id |A| := by
  apply ContinuousMap.ext
  intro x
  rw [ContinuousMap.comp_apply, firstProjection_apply]
  change SSet.toTop.map (χ' ≫ fst A B')
    (SSet.toTop.map a (SSet.toTop.map s x)) = x
  have hmap : s ≫ a ≫ χ' ≫ fst A B' = 𝟙 A := by
    calc
      s ≫ a ≫ χ' ≫ fst A B' = (s ≫ a) ≫ χ' ≫ fst A B' := by simp only [Category.assoc]
      _ = s' ≫ χ' ≫ fst A B' := by rw [ha]
      _ = (s' ≫ χ') ≫ fst A B' := by simp only [Category.assoc]
      _ = 𝟙 A := by rw [hs']; simp [ProductRealization.vertexSection]
  have hR : SSet.toTop.map (s ≫ a ≫ χ' ≫ fst A B') = 𝟙 _ := by
    rw [hmap, SSet.toTop.map_id]
  simpa only [Functor.map_comp, TopCat.comp_app, TopCat.id_app] using
    congrArg (fun f ↦ f x) hR

/-- The original transition on actual row fibers is a complete weak
homotopy equivalence, derived from genuine product comparison equivalences. -/
theorem transition_isWeakHomotopyEquivalence
    (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
    (he : e.toFun = (SSet.toTop.map χ).hom)
    (e' : ContinuousMap.HomotopyEquiv |E'| |A ⊗ B'|)
    (he' : e'.toFun = (SSet.toTop.map χ').hom) (x : |A|) :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.transitionFiber (projection χ) (projection χ')
        (SSet.toTop.map a).hom (SSet.toTop.map b).hom
        (transitionSquare χ χ' a b sq) (SSet.realizationPoint y)) := by
  let t := HomotopyPullback.transitionFiber (projection χ) (projection χ')
    (SSet.toTop.map a).hom (SSet.toTop.map b).hom
    (transitionSquare χ χ' a b sq) (SSet.realizationPoint y)
  let i := inclusion χ s y hs
  let p := firstProjection χ' (SSet.toTop.map b (SSet.realizationPoint y))
  have hi : IsWeakHomotopyEquivalence i := isWeakHomotopyEquivalence_of_point i x
    (inclusion_bijective χ s y hs e he)
  have hp : IsWeakHomotopyEquivalence p := isWeakHomotopyEquivalence_of_point p (t (i x))
    (firstProjection_bijective χ' e' he' _)
  have hpti : IsWeakHomotopyEquivalence (p.comp (t.comp i)) := by
    rw [firstProjection_transition_inclusion χ χ' s s' y y' hs hs' a b sq ha]
    exact isWeakHomotopyEquivalence_id |A|
  exact (hpti.of_comp_right hp).of_comp_left hi

/-- With genuinely connected original source/base rows and first factor,
the original constant-path row comparison is weakly homotopy cartesian.
This establishes a transition-square input, not a global gluing theorem. -/
theorem comparison_isWeakHomotopyEquivalence
    [PathConnectedSpace |A|] [PathConnectedSpace |E|] [PathConnectedSpace |B|]
    (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
    (he : e.toFun = (SSet.toTop.map χ).hom)
    (e' : ContinuousMap.HomotopyEquiv |E'| |A ⊗ B'|)
    (he' : e'.toFun = (SSet.toTop.map χ').hom) (x : |A|) :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison (projection χ') (SSet.toTop.map b).hom
        (projection χ) (SSet.toTop.map a).hom (transitionSquare χ χ' a b sq)) := by
  let t := HomotopyPullback.transitionFiber (projection χ) (projection χ')
    (SSet.toTop.map a).hom (SSet.toTop.map b).hom
    (transitionSquare χ χ' a b sq) (SSet.realizationPoint y)
  let i := inclusion χ s y hs
  let := fiber_pathConnected χ' e' he' (SSet.toTop.map b (SSet.realizationPoint y)) (t (i x))
  apply isWeakHomotopyEquivalence_of_point _ (SSet.toTop.map s x)
  apply HomotopyPullback.comparison_bijective_of_fiberMap (projection χ) (projection χ')
    (SSet.toTop.map a).hom (SSet.toTop.map b).hom (transitionSquare χ χ' a b sq)
    (SSet.realizationPoint y) (SSet.toTop.map s x) (projection_section χ s y hs x)
  intro n
  exact (transition_isWeakHomotopyEquivalence χ χ' s s' y y' hs hs' a b sq ha e he e' he'
    x).homotopy_bijective
    (i x) n

end SSet.SplitRealizationFiber
