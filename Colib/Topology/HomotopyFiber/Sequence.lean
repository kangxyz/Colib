/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.UnitInterval
public import Colib.Topology.HomotopyFiber.Exactness
public import Mathlib.Topology.Homotopy.HSpaces
public import Mathlib.Topology.Homotopy.Equiv

/-!
# The iterated homotopy fiber and the loop space

Explicit path-space constructions underlying the next positions of the
homotopy-fiber sequence.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/Sequence.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space models,
basepoint tracks, maps and universe parameters are retained. -/
@[expose] public section


noncomputable section
open scoped Topology unitInterval
open unitInterval

universe u v

namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y : Y) (x : X) (h : f x = y)

/-- The path carried by a point of the concrete homotopy fiber. -/
def toPath (z : HomotopyFiber f y) : Path (f (projection f y z)) y where
  toContinuousMap := z.1.2
  source' := z.2.1
  target' := z.2.2

/-- The homotopy fiber of the homotopy-fiber projection. -/
abbrev IteratedFiber := HomotopyFiber (projection f y) x

/-- Its distinguished point, with both constituent paths constant. -/
def iteratedBasepoint : IteratedFiber f y x :=
  basepoint (projection f y) x (basepoint f y x h) rfl

/-- A point `((x', γ), δ)` is sent to the loop `(f δ)⁻¹ · γ`. -/
def iteratedToLoops : C(IteratedFiber f y x, Path y y) where
  toFun z := (((toPath (projection f y) x z).map f.continuous).symm.cast h.symm rfl).trans
    (toPath f y z.1.1)
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    apply Path.trans_continuous_family
    · change Continuous (fun z : IteratedFiber f y x × I => f (z.1.1.2 (σ z.2)))
      fun_prop
    · change Continuous (fun z : IteratedFiber f y x × I => z.1.1.1.1.2 z.2)
      fun_prop

/-- A loop is included by keeping the source point and its return path constant. -/
def loopsToIterated : C(Path y y, IteratedFiber f y x) where
  toFun γ := ⟨(loopInclusion f y x h γ, ContinuousMap.const I x), rfl, rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (loopInclusion f y x h).continuous.prodMk continuous_const

@[simp]
theorem loopsToIterated_refl : loopsToIterated f y x h (Path.refl y) =
    iteratedBasepoint f y x h := rfl

@[simp]
theorem iteratedToLoops_basepoint : iteratedToLoops f y x h (iteratedBasepoint f y x h) =
    Path.refl y := by
  subst y
  change (Path.refl (f x)).trans (Path.refl (f x)) = _
  exact Path.refl_trans_refl

@[simp]
theorem iteratedToLoops_loopsToIterated (γ : Path y y) :
    iteratedToLoops f y x h (loopsToIterated f y x h γ) = (Path.refl y).trans γ := by
  subst y
  rfl

/-- Removing the constant initial segment supplies a continuous right-inverse
homotopy, fixed at the constant loop. -/
def loopsRightInverseHomotopy :
    ((iteratedToLoops f y x h).comp (loopsToIterated f y x h)).Homotopy
      (ContinuousMap.id (Path y y)) where
  toFun z := Path.delayReflLeft z.1 z.2
  continuous_toFun := Path.continuous_delayReflLeft
  map_zero_left γ := by
    rw [Path.delayReflLeft_zero]
    exact (iteratedToLoops_loopsToIterated f y x h γ).symm
  map_one_left γ := Path.delayReflLeft_one γ

@[simp]
theorem loopsRightInverseHomotopy_based (t : I) :
    loopsRightInverseHomotopy f y x h (t, Path.refl y) = Path.refl y := by
  ext s
  rfl

/-- The initial part of the return path, traversed backwards. -/
def returnPrefix (z : IteratedFiber f y x) (s : I) :
    Path (z.1.2 s) (projection f y z.1.1) where
  toFun t := z.1.2 (s * σ t)
  continuous_toFun := z.1.2.continuous.comp (by fun_prop)
  source' := by simp
  target' := by simpa using z.2.1

/-- The remaining part of the return path after moving its source to time `s`. -/
def returnTail (z : IteratedFiber f y x) (s : I) : Path (z.1.2 s) x where
  toFun t := z.1.2 (σ (σ s * σ t))
  continuous_toFun := z.1.2.continuous.comp (by fun_prop)
  source' := by simp
  target' := by simpa using z.2.2

/-- Slide a fiber point along its return path, prepending the corresponding
reversed image path to its path in the target. -/
def slideFirst : C(I × IteratedFiber f y x, HomotopyFiber f y) where
  toFun z := ⟨(z.2.1.2 z.1,
    (((returnPrefix f y x z.2 z.1).map f.continuous).trans
      (toPath f y z.2.1.1)).toContinuousMap),
    Path.source _, Path.target _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      refine Path.trans_continuous_family
        (fun z : I × IteratedFiber f y x => (returnPrefix f y x z.2 z.1).map f.continuous) ?_
        (fun z : I × IteratedFiber f y x => toPath f y z.2.1.1) ?_
      · change Continuous (fun z : (I × IteratedFiber f y x) × I =>
          f (z.1.2.1.2 (z.1.1 * σ z.2)))
        exact f.continuous.comp ((show Continuous
          (fun z : (I × IteratedFiber f y x) × I => z.1.2.1.2) by fun_prop).eval (by fun_prop))
      · change Continuous (fun z : (I × IteratedFiber f y x) × I =>
          z.1.2.1.1.1.2 z.2)
        fun_prop

/-- The full slide, including the shrinking return path in the source. -/
def slide : C(I × IteratedFiber f y x, IteratedFiber f y x) where
  toFun z := ⟨(slideFirst f y x z, (returnTail f y x z.2 z.1).toContinuousMap),
    Path.source _, Path.target _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (slideFirst f y x).continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (I × IteratedFiber f y x) × I =>
      z.1.2.1.2 (σ (σ z.1.1 * σ z.2)))
    exact (show Continuous (fun z : (I × IteratedFiber f y x) × I => z.1.2.1.2) by
      fun_prop).eval (by fun_prop)

/-- Remove a constant prefix in the target path while leaving the return path
unchanged. This is a continuous family even though the path endpoints vary. -/
def unpad : C(I × IteratedFiber f y x, IteratedFiber f y x) where
  toFun z := ⟨(⟨(projection f y z.2.1.1,
    (Path.delayReflLeft z.1 (toPath f y z.2.1.1)).toContinuousMap),
    Path.source _, Path.target _⟩, z.2.1.2), z.2.2.1, z.2.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply Continuous.prodMk
      · fun_prop
      · apply ContinuousMap.continuous_of_continuous_uncurry
        change Continuous (fun z : (I × IteratedFiber f y x) × I =>
          z.1.2.1.1.1.2 (σ (qRight (σ z.2, z.1.1))))
        fun_prop
    · fun_prop

@[simp]
theorem unpad_one (z : IteratedFiber f y x) : unpad f y x (1, z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Path.toContinuousMap (Path.delayReflLeft_one (toPath f y z.1.1))
  · rfl

@[simp]
theorem slide_zero (z : IteratedFiber f y x) :
    slide f y x (0, z) = unpad f y x (0, z) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · exact z.2.1
    · apply ContinuousMap.ext
      intro t
      change (((returnPrefix f y x z 0).map f.continuous).trans (toPath f y z.1.1)) t =
        (Path.delayReflLeft 0 (toPath f y z.1.1)) t
      rw [Path.delayReflLeft_zero]
      simp only [Path.trans_apply]
      split_ifs
      · change f (z.1.2 (0 * σ _)) = _
        simp only [zero_mul]
        exact congrArg f z.2.1
      · rfl
  · apply ContinuousMap.ext
    intro t
    change z.1.2 (σ (σ 0 * σ t)) = z.1.2 t
    simp

@[simp]
theorem slide_one (z : IteratedFiber f y x) :
    slide f y x (1, z) = loopsToIterated f y x h (iteratedToLoops f y x h z) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · exact z.2.2
    · apply ContinuousMap.ext
      intro t
      change (((returnPrefix f y x z 1).map f.continuous).trans (toPath f y z.1.1)) t =
        ((((toPath (projection f y) x z).map f.continuous).symm.cast h.symm rfl).trans
          (toPath f y z.1.1)) t
      simp only [Path.trans, Path.coe_mk_mk, Function.comp_apply]
      split_ifs
      · change f (z.1.2 (1 * σ _)) = f (z.1.2 (σ _))
        simp
      · rfl
  · apply ContinuousMap.ext
    intro t
    change z.1.2 (σ (σ 1 * σ t)) = x
    simpa using z.2.2

/-- The common start of the sliding and unpadding homotopies. -/
def padded : C(IteratedFiber f y x, IteratedFiber f y x) where
  toFun z := unpad f y x (0, z)
  continuous_toFun := (unpad f y x).continuous.comp (by fun_prop)

@[simp]
theorem slide_based (t : I) :
    slide f y x (t, iteratedBasepoint f y x h) = iteratedBasepoint f y x h := by
  subst y
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro s
      change ((Path.refl (f x)).trans (Path.refl (f x))) s = f x
      rw [Path.refl_trans_refl]
      rfl
  · rfl

@[simp]
theorem unpad_based (t : I) :
    unpad f y x (t, iteratedBasepoint f y x h) = iteratedBasepoint f y x h := rfl

/-- The sliding deformation, with its chosen basepoint held fixed. -/
def slideHomotopy :
    (padded f y x).HomotopyRel
      ((loopsToIterated f y x h).comp (iteratedToLoops f y x h))
      {iteratedBasepoint f y x h} where
  toHomotopy :=
    { toContinuousMap := slide f y x
      map_zero_left := slide_zero f y x
      map_one_left := slide_one f y x h }
  prop' t z hz := by
    obtain rfl := hz
    exact slide_based f y x h t

/-- The unpadding deformation, with its chosen basepoint held fixed. -/
def unpadHomotopy :
    (padded f y x).HomotopyRel (ContinuousMap.id (IteratedFiber f y x))
      {iteratedBasepoint f y x h} where
  toHomotopy :=
    { toContinuousMap := unpad f y x
      map_zero_left := fun _ => rfl
      map_one_left := unpad_one f y x }
  prop' t z hz := by
    obtain rfl := hz
    rfl

/-- The other composite is homotopic to the identity, through based maps. -/
def iteratedLeftInverseHomotopy :
    ((loopsToIterated f y x h).comp (iteratedToLoops f y x h)).HomotopyRel
      (ContinuousMap.id (IteratedFiber f y x)) {iteratedBasepoint f y x h} :=
  (slideHomotopy f y x h).symm.trans (unpadHomotopy f y x h)

@[simp]
theorem iteratedLeftInverseHomotopy_based (t : I) :
    iteratedLeftInverseHomotopy f y x h (t, iteratedBasepoint f y x h) =
      iteratedBasepoint f y x h :=
  (iteratedLeftInverseHomotopy f y x h).eq_snd t rfl

/-- The homotopy fiber of the homotopy-fiber projection is genuinely homotopy
equivalent to the target loop space, via the explicit path constructions above.
Both maps and the two inverse homotopies preserve the distinguished basepoints. -/
def iteratedFiberEquivLoops : ContinuousMap.HomotopyEquiv (IteratedFiber f y x) (Path y y) where
  toFun := iteratedToLoops f y x h
  invFun := loopsToIterated f y x h
  left_inv := ⟨(iteratedLeftInverseHomotopy f y x h).toHomotopy⟩
  right_inv := ⟨loopsRightInverseHomotopy f y x h⟩

section HomotopyGroups
variable {N : Type*} [DecidableEq N] [Nonempty N]

/-- The two path-space constructions induce mutually inverse homomorphisms. -/
theorem homotopyGroupMapHom_iterated_leftInverse :
    (HomotopyGroup.mapHom (N := N) (loopsToIterated f y x h) (loopsToIterated_refl f y x h)).comp
      (HomotopyGroup.mapHom (iteratedToLoops f y x h) (iteratedToLoops_basepoint f y x h)) =
        MonoidHom.id (HomotopyGroup N (IteratedFiber f y x) (iteratedBasepoint f y x h)) := by
  rw [← HomotopyGroup.mapHom_comp]
  exact (HomotopyGroup.mapHom_eq_of_based_homotopy _ rfl
    (iteratedLeftInverseHomotopy f y x h).toHomotopy
    (iteratedLeftInverseHomotopy_based f y x h)).trans HomotopyGroup.mapHom_id

/-- The right inverse on homotopy groups comes from deleting the constant prefix. -/
theorem homotopyGroupMapHom_iterated_rightInverse :
    (HomotopyGroup.mapHom (N := N) (iteratedToLoops f y x h) (iteratedToLoops_basepoint f y x
      h)).comp
      (HomotopyGroup.mapHom (loopsToIterated f y x h) (loopsToIterated_refl f y x h)) =
        MonoidHom.id (HomotopyGroup N (Path y y) (Path.refl y)) := by
  rw [← HomotopyGroup.mapHom_comp]
  exact (HomotopyGroup.mapHom_eq_of_based_homotopy _ rfl
    (loopsRightInverseHomotopy f y x h)
    (loopsRightInverseHomotopy_based f y x h)).trans HomotopyGroup.mapHom_id

/-- The based equivalence induces an actual group isomorphism. -/
def iteratedFiberHomotopyGroupEquiv :
    HomotopyGroup N (IteratedFiber f y x) (iteratedBasepoint f y x h) ≃*
      HomotopyGroup N (Path y y) (Path.refl y) where
  toFun := HomotopyGroup.mapHom (iteratedToLoops f y x h) (iteratedToLoops_basepoint f y x h)
  invFun := HomotopyGroup.mapHom (loopsToIterated f y x h) (loopsToIterated_refl f y x h)
  left_inv a := congrArg (fun k : HomotopyGroup N (IteratedFiber f y x)
      (iteratedBasepoint f y x h) →* _ => k a)
    (homotopyGroupMapHom_iterated_leftInverse f y x h)
  right_inv a := congrArg (fun k : HomotopyGroup N (Path y y) (Path.refl y) →* _ => k a)
    (homotopyGroupMapHom_iterated_rightInverse f y x h)
  map_mul' := map_mul _

@[simp]
theorem loopInclusion_refl : loopInclusion f y x h (Path.refl y) = basepoint f y x h := rfl

@[simp]
theorem projection_loopsToIterated :
    (projection (projection f y) x).comp (loopsToIterated f y x h) = loopInclusion f y x h := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The map from loops to the fiber is the iterated projection after the inverse
equivalence. This identifies the relevant map, not just the abstract groups. -/
theorem homotopyGroupMapHom_loopInclusion :
    HomotopyGroup.mapHom (N := N) (loopInclusion f y x h) (loopInclusion_refl f y x h) =
      (HomotopyGroup.mapHom (projection (projection f y) x)
        (projection_basepoint (projection f y) x (basepoint f y x h) rfl)).comp
      (HomotopyGroup.mapHom (loopsToIterated f y x h) (loopsToIterated_refl f y x h)) := by
  rw [← HomotopyGroup.mapHom_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Genuine exactness at the homotopy groups of the homotopy fiber: the kernel
of the projection is the image of the loop-to-fiber map. -/
theorem range_loopInclusion_eq_ker_projection :
    (HomotopyGroup.mapHom (N := N) (loopInclusion f y x h) (loopInclusion_refl f y x h)).range =
      (HomotopyGroup.mapHom (projection f y) (projection_basepoint f y x h)).ker := by
  rw [← range_projection_eq_ker (projection f y) x (basepoint f y x h) rfl,
    homotopyGroupMapHom_loopInclusion]
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨b, rfl⟩
    refine ⟨iteratedFiberHomotopyGroupEquiv f y x h b, ?_⟩
    change HomotopyGroup.mapHom (projection (projection f y) x) _
      ((iteratedFiberHomotopyGroupEquiv f y x h).symm
        (iteratedFiberHomotopyGroupEquiv f y x h b)) = _
    rw [MulEquiv.symm_apply_apply]
    rfl

end HomotopyGroups

/-- Exactness at `π_(n+1)` of the homotopy fiber, for every nonnegative `n`. -/
theorem piMap_range_loopInclusion_eq_ker_projection (n : ℕ) :
    (HomotopyGroup.piMap n (loopInclusion f y x h) (loopInclusion_refl f y x h)).range =
      (HomotopyGroup.piMap n (projection f y) (projection_basepoint f y x h)).ker :=
  range_loopInclusion_eq_ker_projection f y x h

end Topology.HomotopyFiber
