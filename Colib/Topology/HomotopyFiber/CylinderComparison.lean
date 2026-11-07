/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.UnitInterval
public import Colib.Topology.HomotopyFiber.Basic

/-!
# A displayed cylinder and its original homotopy-fiber comparison

A cylinder from a displayed source point to a genuine strict-fiber map gives an actual
projected loop. An explicit homotopy moves along that cylinder while retaining its remaining
projected path. It identifies loop inclusion composed with this specific loop map with the
original constant-path strict-fiber comparison. No contractibility hypothesis is needed.
-/
/-! Implementation provenance: `Quillen/Topology/HomotopyFiber/CylinderComparison.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
path coordinates and universe parameters are retained. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
open unitInterval
universe u v w
namespace Topology.HomotopyFiber
variable {X : Type u} {E : Type v} {B : Type w} [TopologicalSpace X] [TopologicalSpace E]
    [TopologicalSpace B]
  (p : C(E, B)) (b : B) (e : E) (he : p e = b) (g : C(X, E)) (hg : ∀ x, p (g x) = b)
  (H : (ContinuousMap.const X e).Homotopy g)

/-- The actual projected loop traced by a displayed cylinder from the zero point to a strict
    fiber. -/
def cylinderLoop : C(X, Path b b) where
  toFun x := {
    toFun t := p (H (t,x))
    continuous_toFun := p.continuous.comp (H.continuous.comp (continuous_id.prodMk
      continuous_const))
    source' := (congrArg p (H.apply_zero x)).trans he
    target' := (congrArg p (H.apply_one x)).trans (hg x) }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact p.continuous.comp (H.continuous.comp continuous_swap)

/-- The literal constant-path lift of the original strict fiber map. -/
def cylinderStrictLift : C(X, HomotopyFiber p b) where
  toFun x := basepoint p b (g x) (hg x)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact g.continuous.prodMk continuous_const

/-- Move along the displayed original cylinder and retain its entire remaining
projected path. At one endpoint this is loop inclusion; at the other it is
the original constant-path strict-fiber comparison. -/
def cylinderFiberHomotopy :
    ((loopInclusion p b e he).comp (cylinderLoop p b e he g hg H)).Homotopy
      (cylinderStrictLift p b g hg) where
  toFun z := ⟨(H z, ⟨fun t ↦ p (H (σ (σ z.1 * σ t), z.2)), by fun_prop⟩),
    by simp, by simpa using hg z.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk H.continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × X) × unitInterval ↦
      p (H (σ (σ z.1.1 * σ z.2), z.1.2)))
    fun_prop
  map_zero_left x := by
    apply Subtype.ext
    apply Prod.ext
    · exact H.apply_zero x
    · ext t
      change p (H (σ (σ (0 : unitInterval) * σ t), x)) = p (H (t,x))
      simp
  map_one_left x := by
    apply Subtype.ext
    apply Prod.ext
    · exact H.apply_one x
    · ext t
      change p (H (σ (σ (1 : unitInterval) * σ t), x)) = b
      simpa using hg x

end Topology.HomotopyFiber
