/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.WeakCalculus
public import Colib.Topology.HomotopyPullback.WeakCoproduct

/-!
# Weak canonical comparison assembly over genuine topological coproducts

Original weak fixed-target comparisons assemble over arbitrary coproducts,
including empty index types and empty summands. The existing genuine cofan
homeomorphisms supply all coordinates, with the source and complete path
retained. No discrete summand topology or homotopy inverse is imposed.


Implementation provenance:
`Quillen/Topology/Realization/Cartesian/WeakCoproducts.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology

noncomputable section
open Topology TopCat
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.HomotopyPullback

/-- The original sigma fixed-target comparison is weak whenever every
original summand comparison is weak, with no finiteness or nonemptiness input. -/
theorem weakCartesianSigmaFixedTarget
    {ι : Type u} {X A : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (A i)]
    {E T : Type u} [TopologicalSpace E] [TopologicalSpace T]
    (q : C(E, T)) (s : ∀ i, C(A i, T)) (p : ∀ i, C(X i, A i)) (t : ∀ i, C(X i, E))
    (w : ∀ i, q.comp (t i) = (s i).comp (p i))
    (h : ∀ i, WeakCartesian (p i) q (t i) (s i) (w i)) :
    WeakCartesian (sigmaMap p) q (ContinuousMap.sigma t) (ContinuousMap.sigma s)
      (sigmaFixedSquare q s p t w) :=
  HomotopyPullback.comparison_sigma_isWeakHomotopyEquivalence q s p t w h

section Colimits
variable {ι : Type u} (W A : ι → TopCat.{u}) (cW : Cofan W) (cA : Cofan A)
  (hW : IsColimit cW) (hA : IsColimit cA)
  {E T : TopCat.{u}} (q : E ⟶ T)
  (p : cW.pt ⟶ cA.pt) (t : cW.pt ⟶ E) (s : cA.pt ⟶ T)
  (wtotal : t ≫ q = p ≫ s)
  (ps : ∀ i, W i ⟶ A i) (ts : ∀ i, W i ⟶ E) (ss : ∀ i, A i ⟶ T)
  (ws : ∀ i, ts i ≫ q = ps i ≫ ss i)
  (wp : ∀ i, cW.inj i ≫ p = ps i ≫ cA.inj i)
  (wt : ∀ i, cW.inj i ≫ t = ts i)
  (wb : ∀ i, cA.inj i ≫ s = ss i)

include hW hA wp wt wb in
/-- Genuine arbitrary coproduct cocones assemble the original weak
fixed-target comparisons through their unchanged cofan coordinates. -/
theorem weakCartesianCofanFixedTarget
    (h : ∀ i, WeakCartesian (ps i).hom q.hom (ts i).hom (ss i).hom
      (congrArg TopCat.Hom.hom (ws i))) :
    WeakCartesian p.hom q.hom t.hom s.hom (congrArg TopCat.Hom.hom wtotal) := by
  let eW := cofanHomeomorph W cW hW
  let eA := cofanHomeomorph A cA hA
  apply weakCartesianOfCoordinates p.hom q.hom t.hom s.hom (congrArg TopCat.Hom.hom wtotal)
    (sigmaMap (fun i ↦ (ps i).hom)) q.hom (ContinuousMap.sigma (fun i ↦ (ts i).hom))
    (ContinuousMap.sigma (fun i ↦ (ss i).hom))
    (sigmaFixedSquare q.hom (fun i ↦ (ss i).hom) (fun i ↦ (ps i).hom) (fun i ↦ (ts i).hom)
      (fun i ↦ congrArg TopCat.Hom.hom (ws i)))
    eW.symm (Homeomorph.refl E) eA.symm (Homeomorph.refl T)
  · exact cofanMap_coordinates W A cW cA hW hA p ps wp
  · rfl
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i,x⟩,rfl⟩ := eW.surjective z
    change (ContinuousMap.sigma (fun i ↦ (ts i).hom)) (eW.symm (eW ⟨i,x⟩)) = t (eW ⟨i,x⟩)
    rw [Homeomorph.symm_apply_apply]
    change ts i x = t (eW ⟨i,x⟩)
    rw [cofanHomeomorph_apply]
    exact (ConcreteCategory.congr_hom (wt i) x).symm
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i,x⟩,rfl⟩ := eA.surjective z
    change (ContinuousMap.sigma (fun i ↦ (ss i).hom)) (eA.symm (eA ⟨i,x⟩)) = s (eA ⟨i,x⟩)
    rw [Homeomorph.symm_apply_apply]
    change ss i x = s (eA ⟨i,x⟩)
    rw [cofanHomeomorph_apply]
    exact (ConcreteCategory.congr_hom (wb i) x).symm
  · exact weakCartesianSigmaFixedTarget q.hom (fun i ↦ (ss i).hom) (fun i ↦ (ps i).hom)
      (fun i ↦ (ts i).hom) (fun i ↦ congrArg TopCat.Hom.hom (ws i)) h

include hW hA in
/-- The same weak assembly when summand maps are the original restrictions
of the two displayed coproduct maps. -/
theorem weakCartesianCofanFixedTargetOfInclusions
    (hp : ∀ i, ps i ≫ cA.inj i = cW.inj i ≫ p)
    (h : ∀ i, WeakCartesian (ps i).hom q.hom (cW.inj i ≫ t).hom (cA.inj i ≫ s).hom
      (congrArg TopCat.Hom.hom (cofanFixedSquare W A cW cA q p t s wtotal ps i (hp i)))) :
    WeakCartesian p.hom q.hom t.hom s.hom (congrArg TopCat.Hom.hom wtotal) :=
  weakCartesianCofanFixedTarget W A cW cA hW hA q p t s wtotal ps
    (fun i ↦ cW.inj i ≫ t) (fun i ↦ cA.inj i ≫ s)
    (fun i ↦ cofanFixedSquare W A cW cA q p t s wtotal ps i (hp i))
    (fun i ↦ (hp i).symm) (fun _ ↦ rfl) (fun _ ↦ rfl) h

end Colimits
end Topology.HomotopyPullback
