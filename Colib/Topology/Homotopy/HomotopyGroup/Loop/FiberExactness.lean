/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.UnitInterval
public import Colib.Topology.HomotopyFiber.Sequence
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift

/-!
# Exactness at the loop space of the target

A relative nullhomotopy of a cube in the homotopy fiber contains a cube of
loops in the source. Its carried square of target paths proves that applying
the original map recovers the original loop-space cube up to a relative
homotopy. This supplies the remaining recurring exactness position.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/Loop/FiberExactness.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space models,
basepoint tracks, maps and universe parameters are retained. -/
@[expose] public section


noncomputable section
open scoped Topology unitInterval
open unitInterval

universe w u v
namespace Topology.HomotopyFiber
variable {N : Type w} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y : Y) (x : X) (h : f x = y)

/-- Moving along a source loop contracts its image in the homotopy fiber. -/
def loopMapInclusionNullhomotopy :
    ((loopInclusion f y x h).comp (basedLoopMap f h)).Homotopy
      (ContinuousMap.const (Path x x) (basepoint f y x h)) where
  toFun z := ⟨(z.2 z.1, ⟨fun t => f (z.2 (σ (σ z.1 * σ t))), by fun_prop⟩),
    by simp, by simpa using (congrArg f z.2.target).trans h⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (I × Path x x) × I => f (z.1.2 (σ (σ z.1.1 * σ z.2))))
      fun_prop
  map_zero_left γ := by
    apply Subtype.ext
    apply Prod.ext
    · exact γ.source
    · apply ContinuousMap.ext
      intro t
      change f (γ (σ (σ 0 * σ t))) = f (γ t)
      simp
  map_one_left γ := by
    apply Subtype.ext
    apply Prod.ext
    · exact γ.target
    · apply ContinuousMap.ext
      intro t
      change f (γ (σ (σ 1 * σ t))) = y
      simpa using (congrArg f γ.target).trans h

@[simp]
theorem loopMapInclusionNullhomotopy_based (t : I) :
    loopMapInclusionNullhomotopy f y x h (t, Path.refl x) = basepoint f y x h := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro s
    exact h

/-- Project a nullhomotopy in the fiber to obtain loops in the source. -/
def sourceLoopsOfNullhomotopy (p : GenLoop N (Path y y) (Path.refl y))
    (H : (GenLoop.postcomp (loopInclusion f y x h) (loopInclusion_refl f y x h) p).val.HomotopyRel
      (GenLoop.const : GenLoop N (HomotopyFiber f y) (basepoint f y x h)).val (Cube.boundary N)) :
    GenLoop N (Path x x) (Path.refl x) :=
  ⟨⟨fun z =>
    { toFun t := projection f y (H (t, z))
      continuous_toFun := (projection f y).continuous.comp (H.continuous.comp (by fun_prop))
      source' := by rw [H.apply_zero]; rfl
      target' := by rw [H.apply_one]; rfl }, by
    apply Path.continuous_uncurry_iff.mp
    exact (projection f y).continuous.comp (H.continuous.comp continuous_swap)⟩, by
    intro z hz
    ext t
    change projection f y (H (t, z)) = x
    rw [H.eq_snd t hz]
    rfl⟩

/-- At least one coordinate of this path across the square lies on its far edge. -/
private theorem qRight_far_edge (s : I) : qRight (s, 0) = 1 ∨ qRight (σ s, 0) = 1 := by
  have hs (t : I) (ht : (1 : ℝ) / 2 ≤ t) : qRight (t, 0) = 1 := by
    apply Subtype.ext
    change (qRight (t, 0) : ℝ) = 1
    rw [qRight_zero_right]
    split_ifs <;> linarith
  rcases le_total ((1 : ℝ) / 2) s with hh | hh
  · exact Or.inl (hs s hh)
  · apply Or.inr
    apply hs
    change (1 : ℝ) / 2 ≤ 1 - s
    linarith

/-- Deform the left edge of the carried square into its bottom edge. The other
two edges are constant, so this stays a based loop throughout the deformation. -/
def squareLoopHomotopy (p : GenLoop N (Path y y) (Path.refl y))
    (H : (GenLoop.postcomp (loopInclusion f y x h) (loopInclusion_refl f y x h) p).val.HomotopyRel
      (GenLoop.const : GenLoop N (HomotopyFiber f y) (basepoint f y x h)).val (Cube.boundary N)) :
    p.val.HomotopyRel
      (GenLoop.postcomp (basedLoopMap f h) (basedLoopMap_refl f h)
        (sourceLoopsOfNullhomotopy f y x h p H)).val (Cube.boundary N) where
  toFun z :=
    { toFun t := (H (qRight (z.1, 0) * t, z.2)).1.2 (qRight (σ z.1, 0) * t)
      continuous_toFun := by
        apply Continuous.eval
        · exact (continuous_snd.comp continuous_subtype_val).comp (H.continuous.comp (by fun_prop))
        · fun_prop
      source' := by
        simp only [mul_zero]
        rw [H.apply_zero]
        exact (p z.2).source
      target' := by
        simp only [mul_one]
        rcases qRight_far_edge z.1 with hs | hs
        · rw [hs, H.apply_one]
          rfl
        · rw [hs]
          exact (H (qRight (z.1, 0), z.2)).2.2 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    have hH : Continuous (fun z : (I × (N → I)) × I =>
        H (qRight (z.1.1, 0) * z.2, z.1.2)) := H.continuous.comp (by fun_prop)
    exact ((continuous_snd.comp continuous_subtype_val).comp hH).eval (by fun_prop)
  map_zero_left z := by
    ext t
    change (H (qRight (0, 0) * t, z)).1.2 (qRight (σ 0, 0) * t) = p z t
    simp only [qRight_zero_left, symm_zero, qRight_one_left, zero_mul, one_mul]
    rw [H.apply_zero]
    rfl
  map_one_left z := by
    ext t
    change (H (qRight (1, 0) * t, z)).1.2 (qRight (σ 1, 0) * t) = f (projection f y (H (t, z)))
    simp only [qRight_one_left, symm_one, qRight_zero_left, one_mul, zero_mul]
    exact (H (t, z)).2.1
  prop' s z hz := by
    ext t
    change (H (qRight (s, 0) * t, z)).1.2 (qRight (σ s, 0) * t) = p z t
    rw [H.eq_snd _ hz]
    have hp : p z = Path.refl y := p.property z hz
    rw [hp]
    rfl

section HomotopyGroups
variable [DecidableEq N] [Nonempty N]

/-- The source loop map followed by the loop-to-fiber map induces zero. -/
theorem homotopyGroupMapHom_loopMap_inclusion_comp :
    (HomotopyGroup.mapHom (N := N) (loopInclusion f y x h) (loopInclusion_refl f y x h)).comp
      (HomotopyGroup.mapHom (basedLoopMap f h) (basedLoopMap_refl f h)) = 1 := by
  rw [← HomotopyGroup.mapHom_comp]
  exact (HomotopyGroup.mapHom_eq_of_based_homotopy _ rfl
    (loopMapInclusionNullhomotopy f y x h)
    (loopMapInclusionNullhomotopy_based f y x h)).trans HomotopyGroup.mapHom_const

/-- The third recurring exactness position: a loop-space homotopy class vanishes
in the fiber if and only if it comes from the source loop space. -/
theorem range_loopMap_eq_ker_loopInclusion :
    (HomotopyGroup.mapHom (N := N) (basedLoopMap f h) (basedLoopMap_refl f h)).range =
      (HomotopyGroup.mapHom (loopInclusion f y x h) (loopInclusion_refl f y x h)).ker := by
  ext a
  change a ∈ (HomotopyGroup.mapHom (basedLoopMap f h) (basedLoopMap_refl f h)).range ↔
    HomotopyGroup.mapHom (loopInclusion f y x h) (loopInclusion_refl f y x h) a = 1
  constructor
  · rintro ⟨b, rfl⟩
    exact congrArg (fun k : HomotopyGroup N (Path x x) (Path.refl x) →*
      HomotopyGroup N (HomotopyFiber f y) (basepoint f y x h) => k b)
        (homotopyGroupMapHom_loopMap_inclusion_comp f y x h)
  · refine Quotient.inductionOn a (fun p hp => ?_)
    change Quotient.mk' (GenLoop.postcomp (loopInclusion f y x h)
      (loopInclusion_refl f y x h) p) = Quotient.mk' GenLoop.const at hp
    obtain ⟨H⟩ := Quotient.exact hp
    refine ⟨Quotient.mk' (sourceLoopsOfNullhomotopy f y x h p H), ?_⟩
    exact Quotient.sound ⟨(squareLoopHomotopy f y x h p H).symm⟩

end HomotopyGroups

/-- The same exactness statement on positive-dimensional homotopy groups. -/
theorem piMap_range_loopMap_eq_ker_loopInclusion (n : ℕ) :
    (HomotopyGroup.piMap n (basedLoopMap f h) (basedLoopMap_refl f h)).range =
      (HomotopyGroup.piMap n (loopInclusion f y x h) (loopInclusion_refl f y x h)).ker :=
  range_loopMap_eq_ker_loopInclusion f y x h

end Topology.HomotopyFiber
