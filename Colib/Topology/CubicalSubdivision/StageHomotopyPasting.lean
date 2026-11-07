/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CubicalSubdivision.StagePasting
public import Colib.Topology.MappingPath.Basic

/-!
# Pasting original source maps and whole homotopies across a grid stage

The ordinary closed-face quotient pastes values in the actual mapping-path space. Thus a
source point and its entire supplied continuous path are pasted together. This retains the
literal path on the preceding skeleton and every new face, without quotient-product or
separation hypotheses on either target space.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/CubicalSubdivision/StageHomotopyPasting.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u

namespace Topology.CubicalSubdivision

/-- Inclusion of the preceding closed skeleton into the current one, with unchanged points. -/
def stageInclusion (n m r : ℕ) : C(skeletonBelow n m r, skeleton n m r) where
  toFun x := ⟨x.val, skeletonBelow_subset n m r x.property⟩
  continuous_toFun := by fun_prop

/-- The original face parametrization with codomain the current closed skeleton. -/
def stageFaceMap {n m r : ℕ} (F : StageFace n m r) :
    C((Active F.val → unitInterval), skeleton n m r) where
  toFun t := ⟨face F.val t, Set.mem_iUnion.mpr ⟨⟨F.val, F.property.le⟩, ⟨t, rfl⟩⟩⟩
  continuous_toFun := by fun_prop

/-- Matching original source maps and matching whole boundary tracks paste to a global
homotopy. Both restrictions, to the old skeleton and to every new face, are literal. -/
theorem exists_stage_homotopy_paste (n m r : ℕ)
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (a : C(skeletonBelow n m r, X)) (b : C(skeleton n m r, Y))
    (H : (f.comp a).Homotopy (b.comp (stageInclusion n m r)))
    (c : ∀ F : StageFace n m r, C((Active F.val → unitInterval), X))
    (hc : ∀ F (z : {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)}),
      c F z.val = a (stageBoundary F z))
    (K : ∀ F : StageFace n m r, (f.comp (c F)).Homotopy (b.comp (stageFaceMap F)))
    (hK : ∀ F (t : unitInterval)
      (z : {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)}),
      K F (t, z.val) = H (t, stageBoundary F z)) :
    ∃ g : C(skeleton n m r, X),
      (∀ x, g (stageInclusion n m r x) = a x) ∧
      (∀ F t, g (stageFaceMap F t) = c F t) ∧
      ∃ L : (f.comp g).Homotopy b,
        (∀ t x, L (t, stageInclusion n m r x) = H (t, x)) ∧
        ∀ F t z, L (t, stageFaceMap F z) = K F (t, z) := by
  let a' : C(skeletonBelow n m r, MappingPath f) := {
    toFun x := ⟨(a x, ⟨fun t ↦ H (t, x), by fun_prop⟩), H.map_zero_left x⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk a.continuous
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact H.continuous.comp continuous_swap }
  let c' (F : StageFace n m r) : C((Active F.val → unitInterval), MappingPath f) := {
    toFun x := ⟨(c F x, ⟨fun t ↦ K F (t, x), by fun_prop⟩), (K F).map_zero_left x⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk (c F).continuous
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (K F).continuous.comp continuous_swap }
  have hc' (F : StageFace n m r)
      (z : {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)}) :
      c' F z.val = a' (stageBoundary F z) := by
    apply Subtype.ext
    apply Prod.ext (hc F z)
    exact ContinuousMap.ext (fun t ↦ hK F t z)
  obtain ⟨g', hga, hgc⟩ := exists_stage_paste n m r a' c' hc'
  have hend (x : skeleton n m r) : MappingPath.endpoint f (g' x) = b x := by
    obtain ⟨z, rfl⟩ := stageProjection_surjective n m r x
    rcases z with x | ⟨F, z⟩
    · change MappingPath.endpoint f (g' (stageInclusion n m r x)) = _
      exact (congrArg (MappingPath.endpoint f) (hga x)).trans (H.map_one_left x)
    · change MappingPath.endpoint f (g' (stageFaceMap F z)) = _
      exact (congrArg (MappingPath.endpoint f) (hgc F z)).trans ((K F).map_one_left z)
  let g := (MappingPath.source f).comp g'
  let L : (f.comp g).Homotopy b := {
    toFun z := (g' z.2).val.2 z.1
    continuous_toFun := by fun_prop
    map_zero_left x := (g' x).property
    map_one_left x := hend x }
  refine ⟨g, ?_, ?_, L, ?_, ?_⟩
  · intro x
    exact congrArg (fun z : MappingPath f ↦ z.val.1) (hga x)
  · intro F t
    exact congrArg (fun z : MappingPath f ↦ z.val.1) (hgc F t)
  · intro t x
    exact congrArg (fun z : MappingPath f ↦ z.val.2 t) (hga x)
  · intro F t z
    exact congrArg (fun z : MappingPath f ↦ z.val.2 t) (hgc F z)

end Topology.CubicalSubdivision
