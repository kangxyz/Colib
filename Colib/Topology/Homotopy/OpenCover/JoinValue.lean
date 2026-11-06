/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.CategoryTheory.ComposableArrows.Split
public import Colib.Topology.Homotopy.OpenCover.JoinedSubdivision

/-!
# Join Value

The joined actual subdivision has the composite of its two original values.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
variable {C : Type w} [Category.{z} C]

/-- The joined actual subdivision has the composite of its two original values. -/
theorem PathSubdivision.join_value {x y z : X} {p : Path x y} {q : Path y z}
    (s : PathSubdivision (U := U) p) (t : PathSubdivision (U := U) q)
    (d : ChartData (C := C) U) (hc : d.Compatible) :
    (s.join t).value d = s.value d ≫ t.value d := by
  let r := s.join t
  let a := fun i => (p.trans q) (r.times (leftIndex s.n t.n i))
  let b := fun i => (p.trans q) (r.times (rightIndex s.n t.n i))
  have ea (i : Fin (s.n + 1)) : a i = p (s.times i) := by
    change (p.trans q) (s.joinTimes t (leftIndex s.n t.n i)) = _
    dsimp only [leftIndex]
    rw [s.joinTimes_left t i, trans_leftHalf]
  have eb (i : Fin (t.n + 1)) : b i = q (t.times i) := by
    change (p.trans q) (s.joinTimes t (rightIndex s.n t.n i)) = _
    dsimp only [rightIndex]
    rw [s.joinTimes_right t i, trans_rightHalf]
  let pa := fun i : Fin s.n => (p.trans q).subpath
    (r.times (leftIndex s.n t.n i.castSucc)) (r.times (leftIndex s.n t.n i.succ))
  let pb := fun i : Fin t.n => (p.trans q).subpath
    (r.times (rightIndex s.n t.n i.castSucc)) (r.times (rightIndex s.n t.n i.succ))
  have hpa (i : Fin s.n) (u : unitInterval) :
      pa i u = p.subpath (s.times i.castSucc) (s.times i.succ) u := by
    change (p.trans q) (Icc.convexComb (s.joinTimes t (leftIndex s.n t.n i.castSucc))
      (s.joinTimes t (leftIndex s.n t.n i.succ)) u) = _
    dsimp only [leftIndex]
    rw [s.joinTimes_left t i.castSucc, s.joinTimes_left t i.succ, leftHalf_convexComb,
      trans_leftHalf]
    rfl
  have hpb (i : Fin t.n) (u : unitInterval) :
      pb i u = q.subpath (t.times i.castSucc) (t.times i.succ) u := by
    change (p.trans q) (Icc.convexComb (s.joinTimes t (rightIndex s.n t.n i.castSucc))
      (s.joinTimes t (rightIndex s.n t.n i.succ)) u) = _
    dsimp only [rightIndex]
    rw [s.joinTimes_right t i.castSucc, s.joinTimes_right t i.succ, rightHalf_convexComb,
      trans_rightHalf]
    rfl
  have hl := d.finitePathValue_transport hc a (fun i => p (s.times i)) ea pa
    (fun i => p.subpath (s.times i.castSucc) (s.times i.succ)) hpa
    (fun i => r.chart ⟨i.val, by change _ < s.n + t.n; omega⟩) s.chart
    (fun i => r.contained ⟨i.val, by change _ < s.n + t.n; omega⟩) s.contained
  have hr := d.finitePathValue_transport hc b (fun i => q (t.times i)) eb pb
    (fun i => q.subpath (t.times i.castSucc) (t.times i.succ)) hpb
    (fun i => r.chart ⟨s.n + i.val, by change _ < s.n + t.n; omega⟩) t.chart
    (fun i => r.contained ⟨s.n + i.val, by change _ < s.n + t.n; omega⟩) t.contained
  have hs := finiteChainComp_split (m := s.n) (n := t.n)
    (fun i => d.obj ((p.trans q) (r.times i)))
    (fun i => d.localValue (r.chart i) ((p.trans q).subpath (r.times i.castSucc) (r.times
      i.succ)) (r.contained i))
  change r.value d = _
  unfold PathSubdivision.value
  erw [hs, hl, hr]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

end FundamentalGroupoid.OpenCover
