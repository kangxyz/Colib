/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.Nullhomotopy
public import Mathlib.Topology.Homotopy.Contractible

/-!
# The actual topological homotopy fiber

The homotopy fiber of `f : X → Y` over `y` consists of pairs `(x, γ)` with
`γ(0)=f(x)` and `γ(1)=y`, using the compact-open topology on paths.
This is infrastructure for localization; no fiber-sequence or long-exact-sequence
theorem is asserted merely by defining this space.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/Basic.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space models,
basepoint tracks, maps and universe parameters are retained. -/
@[expose] public section


noncomputable section
universe u v
open unitInterval

namespace Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A concrete path-space model of the topological homotopy fiber. -/
def HomotopyFiber (f : C(X, Y)) (y : Y) :=
  {z : X × C(I, Y) // z.2 0 = f z.1 ∧ z.2 1 = y}

namespace HomotopyFiber
variable (f : C(X, Y)) (y : Y)

instance : TopologicalSpace (HomotopyFiber f y) := inferInstanceAs (TopologicalSpace
  {z : X × C(I, Y) // z.2 0 = f z.1 ∧ z.2 1 = y})

/-- Projection of a homotopy-fiber point to its underlying source point. -/
def projection : C(HomotopyFiber f y, X) where
  toFun z := z.1.1
  continuous_toFun := by fun_prop

/-- The path witnessing membership supplies the canonical nullhomotopy of
`f` composed with the homotopy-fiber projection. -/
def projectionNullhomotopy :
    ContinuousMap.Homotopy (f.comp (projection f y)) (ContinuousMap.const _ y) where
  toFun z := z.2.1.2 z.1
  continuous_toFun := by fun_prop
  map_zero_left z := z.2.1
  map_one_left z := z.2.2

/-- A genuinely based map provides a distinguished fiber point by the constant path. -/
def basepoint (x : X) (h : f x = y) : HomotopyFiber f y :=
  ⟨(x, ContinuousMap.const I y), h.symm, rfl⟩

@[simp]
lemma projection_basepoint (x : X) (h : f x = y) :
    projection f y (basepoint f y x h) = x := rfl

/-- Ordinary strict-fiber points embed using constant paths. -/
def strictFiberInclusion : C({x : X // f x = y}, HomotopyFiber f y) where
  toFun x := basepoint f y x.1 x.2
  continuous_toFun := by
    unfold basepoint
    fun_prop

/-- The homotopy-fiber projection followed by f is nullhomotopic. -/
theorem projection_nullhomotopic : (f.comp (projection f y)).Nullhomotopic :=
  ⟨y, ⟨projectionNullhomotopy f y⟩⟩

/-- The loop-to-fiber map at a specified source basepoint. -/
def loopInclusion (x : X) (h : f x = y) : C(Path y y, HomotopyFiber f y) where
  toFun γ := ⟨(x, γ.toContinuousMap), γ.source.trans h.symm, γ.target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk continuous_induced_dom

/-- The loop-to-fiber map lies over the fixed source basepoint. -/
@[simp]
lemma projection_loopInclusion (x : X) (h : f x = y) :
    (projection f y).comp (loopInclusion f y x h) = ContinuousMap.const _ x := by
  ext γ
  rfl

/-- The canonical nullhomotopy stays fixed at the chosen basepoint. -/
@[simp]
lemma projectionNullhomotopy_basepoint (x : X) (h : f x = y) (t : I) :
    projectionNullhomotopy f y (t, basepoint f y x h) = y := rfl

/-- A map equipped with a specified nullhomotopy lifts continuously to the
homotopy fiber. This is the actual path-valued lift, not an assumed universal property. -/
def lift {Z : Type*} [TopologicalSpace Z] (g : C(Z, X))
    (H : (f.comp g).Homotopy (ContinuousMap.const Z y)) : C(Z, HomotopyFiber f y) where
  toFun z := ⟨(g z, ⟨fun t => H (t, z), by fun_prop⟩),
    H.map_zero_left z, H.map_one_left z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk g.continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact H.continuous.comp continuous_swap

@[simp]
lemma projection_lift {Z : Type*} [TopologicalSpace Z] (g : C(Z, X))
    (H : (f.comp g).Homotopy (ContinuousMap.const Z y)) :
    (projection f y).comp (lift f y g H) = g := by
  ext z
  rfl

/-- The two consecutive induced homotopy-group maps compose to the trivial
homomorphism. This is one direction of exactness, not a full long exact sequence. -/
theorem piMap_projection_comp (x : X) (h : f x = y) (n : ℕ) :
    (HomotopyGroup.piMap n f h).comp
      (HomotopyGroup.piMap n (projection f y) (projection_basepoint f y x h)) = 1 := by
  rw [← HomotopyGroup.mapHom_comp]
  exact HomotopyGroup.piMap_eq_one_of_based_nullhomotopy n _ (projectionNullhomotopy f y)
    (projectionNullhomotopy_basepoint f y x h)

end HomotopyFiber
end Topology
