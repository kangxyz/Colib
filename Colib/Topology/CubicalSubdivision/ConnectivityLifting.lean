/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HELP.Connectivity
public import Colib.Topology.CubicalSubdivision.FaceBoundaryTopology
public import Colib.Topology.CubicalSubdivision.StageHomotopyPasting

/-!
# Finite-connectivity HELP on the actual grid skeleton

Full finite-range HELP is applied in each face's original coordinates. Both source maps and
whole paths are pasted through the actual skeleton quotient. Thus an already supplied path
on a lower-dimensional face is retained at every time, including at all face intersections.
The only bound is the displayed attaching dimension; no connectivity growth is inferred.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/CubicalSubdivision/ConnectivityLifting.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Topology.CubicalSubdivision

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} {q : ℕ} (hf : IsHomotopyConnectedMap f q)
include hf

/-- Finite full HELP retains the original face coordinates and its entire specified
boundary homotopy. The face may have dimension zero. -/
theorem face_fullHELP {n m : ℕ} (F : FaceIndex n m) (hF : faceDimension F ≤ q)
    (a : C({t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)}, X))
    (b : C((Active F → unitInterval), Y))
    (H : (f.comp a).Homotopy (b.comp ⟨Subtype.val, continuous_subtype_val⟩)) :
    ∃ c : C((Active F → unitInterval), X),
      (∀ z : {t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)},
        c z.val = a z) ∧
      ∃ K : (f.comp c).Homotopy b,
        ∀ (t : unitInterval)
          (z : {t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)}),
          K (t, z.val) = H (t, z) := by
  let e := (Homeomorph.ulift.{u, 0} (X := Active F → unitInterval)).symm.trans
    (faceCubeHomeomorph.{u} F)
  let d := (faceBoundaryUnliftedHomeomorph.{u} F).symm.trans
    (faceCubeBoundaryHomeomorph.{u} F)
  let a' := a.comp d.symm.toHomotopyEquiv.toFun
  let b' := b.comp e.symm.toHomotopyEquiv.toFun
  let H' : (f.comp a').Homotopy
      (b'.comp (CubicalTests.boundaryInclusion (faceDimension F)).hom) := {
    toFun z := H (z.1, d.symm z.2)
    continuous_toFun := by fun_prop
    map_zero_left z := H.map_zero_left (d.symm z)
    map_one_left z := H.map_one_left (d.symm z) }
  obtain ⟨c, hc, K, hK⟩ := hf.cube_fullHELP (faceDimension F) hF a' b' H'
  let c' := c.comp e.toHomotopyEquiv.toFun
  let K' : (f.comp c').Homotopy b := {
    toFun z := K (z.1, e z.2)
    continuous_toFun := by fun_prop
    map_zero_left z := K.map_zero_left (e z)
    map_one_left z := (K.map_one_left (e z)).trans (congrArg b (e.symm_apply_apply z)) }
  refine ⟨c', ?_, K', ?_⟩
  · intro z
    have h := ContinuousMap.congr_fun hc (d z)
    change c (e z.val) = a (d.symm (d z)) at h
    exact h.trans (congrArg a (d.symm_apply_apply z))
  · intro t z
    have h := hK t (d z)
    change K (t, e z.val) = H (t, d.symm (d z)) at h
    exact h.trans (congrArg (fun z ↦ H (t, z)) (d.symm_apply_apply z))

/-- Attaching all faces in one finite-dimensional grid stage preserves the already supplied
source map and the exact whole homotopy on the preceding skeleton. -/
theorem stage_fullHELP (n m r : ℕ) (hr : r ≤ q)
    (a : C(skeletonBelow n m r, X)) (b : C(skeleton n m r, Y))
    (H : (f.comp a).Homotopy (b.comp (stageInclusion n m r))) :
    ∃ g : C(skeleton n m r, X), g.comp (stageInclusion n m r) = a ∧
      ∃ L : (f.comp g).Homotopy b,
        ∀ t x, L (t, stageInclusion n m r x) = H (t, x) := by
  have hfaces (F : StageFace n m r) :
      ∃ c : C((Active F.val → unitInterval), X),
        (∀ z : {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)},
          c z.val = a (stageBoundary F z)) ∧
        ∃ K : (f.comp c).Homotopy (b.comp (stageFaceMap F)),
          ∀ (t : unitInterval)
            (z : {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)}),
            K (t, z.val) = H (t, stageBoundary F z) := by
    let a' := a.comp (stageBoundary F)
    let b' := b.comp (stageFaceMap F)
    let H' : (f.comp a').Homotopy (b'.comp ⟨Subtype.val, continuous_subtype_val⟩) := {
      toFun z := H (z.1, stageBoundary F z.2)
      continuous_toFun := by fun_prop
      map_zero_left z := H.map_zero_left (stageBoundary F z)
      map_one_left z := H.map_one_left (stageBoundary F z) }
    exact face_fullHELP hf F.val (F.property.trans_le hr) a' b' H'
  choose c hc K hK using hfaces
  obtain ⟨g, hga, _, L, hLa, _⟩ := exists_stage_homotopy_paste n m r f a b H c hc K hK
  exact ⟨g, ContinuousMap.ext hga, L, hLa⟩

/-- A strict original grid-stage square has a lift whose comparison homotopy fixes the
entire old skeleton at every time, through the displayed finite connectivity bound. -/
theorem stage_strictHELP (n m r : ℕ) (hr : r ≤ q)
    (a : C(skeletonBelow n m r, X)) (b : C(skeleton n m r, Y))
    (w : f.comp a = b.comp (stageInclusion n m r)) :
    ∃ g : C(skeleton n m r, X), g.comp (stageInclusion n m r) = a ∧
      Nonempty ((f.comp g).HomotopyRel b (Set.range (stageInclusion n m r))) := by
  let H : (f.comp a).Homotopy (b.comp (stageInclusion n m r)) :=
    (ContinuousMap.Homotopy.refl (f.comp a)).cast rfl w
  obtain ⟨g, hg, L, hL⟩ := stage_fullHELP hf n m r hr a b H
  refine ⟨g, hg, ⟨{ toHomotopy := L, prop' := ?_ }⟩⟩
  rintro t z ⟨x, rfl⟩
  exact (hL t x).trans (congrArg f (ContinuousMap.congr_fun hg x)).symm

end Topology.CubicalSubdivision
