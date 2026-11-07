/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LoopPrefixHomotopy

/-!
Implementation provenance:
`Quillen/Topology/HomotopyFiber/LoopPrefixUnitCoherence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Actual path-associator and unit-removal coherence -/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u
namespace Topology.HomotopyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {Y : Type u} [TopologicalSpace Y] {a b c : Y}

/-- The original unit removal, viewed as a path in the original path space. -/
def pathUnitRemoval (p : Path a b) : Path (p.trans (Path.refl b)) p where
  toFun t := Path.delayReflRight t p
  continuous_toFun := Path.continuous_delayReflRight.comp
    (continuous_id.prodMk continuous_const)
  source' := Path.delayReflRight_zero p
  target' := Path.delayReflRight_one p

/-- The explicit associator route followed by removal of the constant final path. -/
def pathAssociatorUnitRoute (p : Path a b) (q : Path b c) :
    Path ((p.trans q).trans (Path.refl c)) (p.trans q) :=
  ((pathPrefixAssociator p q).evalAt (Path.refl c)).trans
    ((pathUnitRemoval q).map (pathPrefix p).continuous)

/-- Any two tracks in the space of endpoint-fixed interval paths have a displayed
endpoint-fixed homotopy, obtained by pointwise convex interpolation. -/
def intervalPathTrackHomotopy {r s : Path (0 : unitInterval) 1}
    (p q : Path r s) : p.Homotopy q where
  toFun z :=
    { toFun t := Set.Icc.convexComb (p z.2 t) (q z.2 t) z.1
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval × unitInterval) × unitInterval ↦
      Set.Icc.convexComb (p z.1.2 z.2) (q z.1.2 z.2) z.1.1)
    fun_prop
  map_zero_left t := by ext u; simp
  map_one_left t := by ext u; simp
  prop' t u hu := by
    rcases hu with hu | hu
    · subst u
      ext v
      simp
    · have hu' : u = 1 := Set.mem_singleton_iff.mp hu
      subst u
      ext v
      simp

/-- The midpoint of the actual interval. -/
def intervalHalf : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The first half of the interval as an actual path. -/
def intervalFirstHalf : Path (0 : unitInterval) intervalHalf where
  toFun t := ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  continuous_toFun := by fun_prop
  source' := by ext; norm_num
  target' := by ext; norm_num [intervalHalf]

/-- The second half of the interval as an actual path. -/
def intervalSecondHalf : Path intervalHalf (1 : unitInterval) where
  toFun t := ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  continuous_toFun := by fun_prop
  source' := by ext; norm_num [intervalHalf]
  target' := by ext; norm_num

/-- Restricting the original concatenation to its first half recovers its original first path. -/
lemma concat_firstHalf (p : Path a b) (q : Path b c) (t : unitInterval) :
    (p.trans q) (intervalFirstHalf t) = p t := by
  rw [Path.trans_apply, dite_eq_left (by change (t : ℝ) / 2 ≤ 1 / 2; linarith [t.2.2])]
  congr 1
  ext
  change 2 * ((t : ℝ) / 2) = t
  ring

/-- Restricting the original concatenation to its second half recovers its original second path. -/
lemma concat_secondHalf (p : Path a b) (q : Path b c) (t : unitInterval) :
    (p.trans q) (intervalSecondHalf t) = q t := by
  have h := Path.extend_trans_of_half_le p q
    (show (1 / 2 : ℝ) ≤ (1 + (t : ℝ)) / 2 by linarith [t.2.1])
  rw [show (1 + (t : ℝ)) / 2 = (intervalSecondHalf t : ℝ) from rfl,
    Path.extend_apply _ (intervalSecondHalf t).property] at h
  have he : 2 * ((1 + (t : ℝ)) / 2) - 1 = t := by ring
  change (p.trans q) (intervalSecondHalf t) = q.extend (2 * ((1 + (t : ℝ)) / 2) - 1) at h
  rw [he, Path.extend_apply q t.property] at h
  exact h

/-- The two half-interval paths concatenate to the unchanged interval parameter. -/
lemma interval_halves_apply (t : unitInterval) :
    (intervalFirstHalf.trans intervalSecondHalf) t = t := by
  rw [Path.trans_apply]
  split_ifs <;> apply Subtype.ext
  · change (2 * (t : ℝ)) / 2 = t
    ring
  · change (1 + (2 * (t : ℝ) - 1)) / 2 = t
    ring

/-- Postcomposition by the original concatenation recovers its exact unit track. -/
lemma unitRemoval_halves (p : Path a b) (q : Path b c) (t u : unitInterval) :
    (p.trans q) (pathUnitRemoval (intervalFirstHalf.trans intervalSecondHalf) t u) =
      pathUnitRemoval (p.trans q) t u := by
  change (p.trans q) ((intervalFirstHalf.trans intervalSecondHalf) _) = _
  rw [interval_halves_apply]
  rfl

/-- The right-parenthesized interval route retains the original concatenated path. -/
lemma nested_halves (p : Path a b) (q : Path b c) (u : unitInterval) :
    (p.trans q) ((intervalFirstHalf.trans
      (intervalSecondHalf.trans (Path.refl 1))) u) =
        (p.trans (q.trans (Path.refl c))) u := by
  rw [Path.trans_apply intervalFirstHalf (intervalSecondHalf.trans (Path.refl 1)) u,
    Path.trans_apply p (q.trans (Path.refl c)) u]
  split_ifs
  · exact concat_firstHalf p q _
  · rw [Path.trans_apply intervalSecondHalf (Path.refl 1),
      Path.trans_apply q (Path.refl c)]
    split_ifs
    · exact concat_secondHalf p q _
    · exact (p.trans q).target

/-- The complete original associator track is the image of its interval track. -/
lemma associator_halves (p : Path a b) (q : Path b c) (t u : unitInterval) :
    (p.trans q) (pathPrefixAssociator intervalFirstHalf intervalSecondHalf
      (t, Path.refl 1) u) =
        pathPrefixAssociator p q (t, Path.refl c) u := by
  change (p.trans q) ((intervalFirstHalf.trans
    (intervalSecondHalf.trans (Path.refl 1))) _) =
      (p.trans (q.trans (Path.refl c))) _
  exact nested_halves p q _

/-- Prefixing the unit-removal track commutes with the interval realization. -/
lemma prefix_unitRemoval_halves (p : Path a b) (q : Path b c) (t u : unitInterval) :
    (p.trans q) ((intervalFirstHalf.trans (pathUnitRemoval intervalSecondHalf t)) u) =
      (p.trans (pathUnitRemoval q t)) u := by
  rw [Path.trans_apply intervalFirstHalf (pathUnitRemoval intervalSecondHalf t) u,
    Path.trans_apply p (pathUnitRemoval q t) u]
  split_ifs
  · exact concat_firstHalf p q _
  · exact concat_secondHalf p q _

/-- The complete associator-followed-by-unit route has the displayed interval lift. -/
lemma associatorUnitRoute_halves (p : Path a b) (q : Path b c) (t u : unitInterval) :
    (p.trans q) (pathAssociatorUnitRoute intervalFirstHalf intervalSecondHalf t u) =
      pathAssociatorUnitRoute p q t u := by
  unfold pathAssociatorUnitRoute
  rw [Path.trans_apply
    ((pathPrefixAssociator intervalFirstHalf intervalSecondHalf).evalAt (Path.refl 1)) _,
    Path.trans_apply ((pathPrefixAssociator p q).evalAt (Path.refl c)) _]
  split_ifs
  · exact associator_halves p q _ u
  · exact prefix_unitRemoval_halves p q _ u

/-- The original unit-removal track agrees up to endpoint-fixed homotopy with the
original associator followed by removal of the final unit. -/
def pathUnitAssociatorHomotopy (p : Path a b) (q : Path b c) :
    (pathUnitRemoval (p.trans q)).Homotopy (pathAssociatorUnitRoute p q) := by
  let H := intervalPathTrackHomotopy
    (pathUnitRemoval (intervalFirstHalf.trans intervalSecondHalf))
    (pathAssociatorUnitRoute intervalFirstHalf intervalSecondHalf)
  exact {
    toFun := fun z ↦ {
      toFun := fun t ↦ (p.trans q) (H z t)
      continuous_toFun := by fun_prop
      source' := by rw [(H z).source]; exact (p.trans q).source
      target' := by rw [(H z).target]; exact (p.trans q).target }
    continuous_toFun := by
      apply Path.continuous_uncurry_iff.mp
      change Continuous (fun z : (unitInterval × unitInterval) × unitInterval ↦
        (p.trans q) (H z.1 z.2))
      fun_prop
    map_zero_left := fun t ↦ by
      ext u
      change (p.trans q) (H (0, t) u) = _
      rw [H.apply_zero]
      exact unitRemoval_halves p q t u
    map_one_left := fun t ↦ by
      ext u
      change (p.trans q) (H (1, t) u) = _
      rw [H.apply_one]
      exact associatorUnitRoute_halves p q t u
    prop' := fun t u hu ↦ by
      rcases hu with hu | hu
      · subst u
        ext v
        change (p.trans q) (H (t, 0) v) = _
        rw [H.source]
        change _ = Path.delayReflRight 0 (p.trans q) v
        rw [Path.delayReflRight_zero]
        simpa only [pathUnitRemoval, Path.coe_mk_mk, Path.delayReflRight_zero] using
          unitRemoval_halves p q 0 v
      · have hu' : u = 1 := Set.mem_singleton_iff.mp hu
        subst u
        ext v
        change (p.trans q) (H (t, 1) v) = _
        rw [H.target]
        change _ = Path.delayReflRight 1 (p.trans q) v
        rw [Path.delayReflRight_one]
        simpa only [pathUnitRemoval, Path.coe_mk_mk, Path.delayReflRight_one] using
          unitRemoval_halves p q 1 v }

/-- The original fiber points with one fixed source coordinate. -/
def pathInclusion {X : Type*} [TopologicalSpace X]
    (f : C(X, Y)) (x : X) (y : Y) : C(Path (f x) y, HomotopyFiber f y) where
  toFun γ := pointWithPath f x y γ
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk continuous_induced_dom

/-- The actual homotopy-square unit track satisfies the endpoint-fixed coherence
with both original unit-removal paths. -/
def loopPrefixHomotopySquareUnitCoherence
    {X X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y']
    {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (x : X) (y : Y) (γ : Path (f x) y) :
    (loopPrefixUnitPath f' (u x) (v y)
      ((H.evalAt x).symm.trans (γ.map v.continuous))).Homotopy
        (((loopPrefixHomotopySquare u v H x y γ).evalAt (Path.refl y)).trans
          ((loopPrefixUnitPath f x y γ).map (homotopySquareMap u v H y).continuous)) := by
  let K := (pathUnitAssociatorHomotopy (H.evalAt x).symm (γ.map v.continuous)).map
    (pathInclusion f' (u x) (v y))
  refine K.cast ?_ ?_
  · ext t
    rfl
  · ext t
    apply Subtype.ext
    apply Prod.ext
    · rw [Path.trans_apply]
      split_ifs <;> rfl
    apply ContinuousMap.ext
    intro s
    change (pathAssociatorUnitRoute (H.evalAt x).symm (γ.map v.continuous) t) s = _
    unfold pathAssociatorUnitRoute
    rw [Path.trans_apply]
    rw [Path.trans_apply]
    split_ifs <;> rfl

end Topology.HomotopyFiber
