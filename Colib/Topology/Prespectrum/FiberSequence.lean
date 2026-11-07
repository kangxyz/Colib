/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.StableShift
public import Colib.Topology.Prespectrum.HomotopyFiber
public import Colib.Topology.Prespectrum.ParameterLooping
public import Colib.Topology.Prespectrum.StableExactness
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.FiberExactness

/-!
The actual stable homotopy-fiber long exact sequence for every integer degree and arbitrary loop
prespectra. The connecting homomorphism uses the proved signed loop shift and original loop-to-fiber
inclusion. All three recurring exactness positions are proved from actual levelwise fiber exactness
and genuine stable colimits. No Omega hypothesis, stable mapping-cone comparison, or negative scheme
K-theory theorem is assumed.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiberSequence.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual fiber coordinates, strict
structure maps, specified whole nullhomotopies, integer grading and connecting signs
are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The literal loop-to-fiber inclusion is a strict map with parameter-correct
loop structure. No homotopy class or chosen inverse replaces its level map. -/
def homotopyFiberLoopInclusion : parameterLooping F ⟶ homotopyFiber f where
  map n := HomotopyFiber.loopInclusion (f.map n) (F.point n) (E.point n) (f.map_point n)
  map_point n := HomotopyFiber.loopInclusion_refl _ _ _ _
  comm n γ := by
    apply Path.ext
    funext t
    apply Subtype.ext
    apply Prod.ext
    · change E.point (n+1) = E.structureMap n (E.point n) t
      rw [E.map_point]
      rfl
    · apply ContinuousMap.ext
      intro s
      rfl

/-- Exactness at the stable groups of the original source spectrum. -/
theorem stableHomotopyFiber_exact_source (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor d).map (homotopyFiberProjection f))
      ((stableHomotopyFunctor d).map f) := by
  apply stableHomotopyMap_exact_of_levelwise
  intro n k
  exact MonoidHom.mulExact_iff.mpr
    (HomotopyFiber.piMap_range_projection_eq_ker (f.map n) (F.point n)
      (E.point n) (f.map_point n) k).symm

/-- Exactness at the stable groups of the actual path-space fiber spectrum. -/
theorem stableHomotopyFiber_exact_fiber (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor d).map (homotopyFiberLoopInclusion f))
      ((stableHomotopyFunctor d).map (homotopyFiberProjection f)) := by
  apply stableHomotopyMap_exact_of_levelwise
  intro n k
  exact MonoidHom.mulExact_iff.mpr
    (HomotopyFiber.piMap_range_loopInclusion_eq_ker_projection (f.map n) (F.point n)
      (E.point n) (f.map_point n) k).symm

/-- Exactness at the stable groups of the parameter-correct target loops. -/
theorem stableHomotopyFiber_exact_loops (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor d).map (parameterLoopingMap f))
      ((stableHomotopyFunctor d).map (homotopyFiberLoopInclusion f)) := by
  apply stableHomotopyMap_exact_of_levelwise
  intro n k
  exact MonoidHom.mulExact_iff.mpr
    (HomotopyFiber.piMap_range_loopMap_eq_ker_loopInclusion (f.map n) (F.point n)
      (E.point n) (f.map_point n) k).symm

/-- All three recurring exactness positions, with actual spectrum maps and
actual stable groups. A separate signed shift theorem identifies the loop term
with degree d+1; no stable mapping-cone theorem is assumed here. -/
theorem stableHomotopyFiber_fiveTerm (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor d).map (parameterLoopingMap f))
      ((stableHomotopyFunctor d).map (homotopyFiberLoopInclusion f)) ∧
    Function.Exact ((stableHomotopyFunctor d).map (homotopyFiberLoopInclusion f))
      ((stableHomotopyFunctor d).map (homotopyFiberProjection f)) ∧
    Function.Exact ((stableHomotopyFunctor d).map (homotopyFiberProjection f))
      ((stableHomotopyFunctor d).map f) :=
  ⟨stableHomotopyFiber_exact_loops f d, stableHomotopyFiber_exact_fiber f d,
    stableHomotopyFiber_exact_source f d⟩

end Topology.LoopPrespectrum

end


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The genuine stable connecting homomorphism uses the proved signed loop
shift and the original loop-to-fiber inclusion. -/
def stableFiberConnecting (d : ℤ) :
    stableHomotopyGroup F (d+1) ⟶ stableHomotopyGroup (homotopyFiber f) d :=
  (parameterStableHomotopyIso F d).inv ≫
    (stableHomotopyFunctor d).map (homotopyFiberLoopInclusion f)

/-- Exactness at the original stable groups of the path-space fiber. -/
theorem stableFiberConnecting_exact_fiber (d : ℤ) :
    Function.Exact (stableFiberConnecting f d)
      ((stableHomotopyFunctor d).map (homotopyFiberProjection f)) := by
  intro a
  constructor
  · intro ha
    obtain ⟨b,hb⟩ := (stableHomotopyFiber_exact_fiber f d a).mp ha
    refine ⟨(parameterStableHomotopyIso F d).hom b, ?_⟩
    change ((stableHomotopyFunctor d).map (homotopyFiberLoopInclusion f))
      ((parameterStableHomotopyIso F d).inv ((parameterStableHomotopyIso F d).hom b)) = a
    simpa using hb
  · rintro ⟨b,rfl⟩
    apply (stableHomotopyFiber_exact_fiber f d _).mpr
    exact ⟨(parameterStableHomotopyIso F d).inv b,rfl⟩

/-- Exactness at the original target stable group in shifted degree. -/
theorem stableFiberConnecting_exact_target (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d+1)).map f) (stableFiberConnecting f d) := by
  intro a
  constructor
  · intro ha
    obtain ⟨b,hb⟩ := (stableHomotopyFiber_exact_loops f d
      ((parameterStableHomotopyIso F d).inv a)).mp ha
    refine ⟨(parameterStableHomotopyIso E d).hom b, ?_⟩
    have hn := ConcreteCategory.congr_hom (parameterStableHomotopyIso_naturality f d) b
    simp only [ConcreteCategory.comp_apply] at hn
    rw [hb] at hn
    exact hn.symm.trans (ConcreteCategory.congr_hom (parameterStableHomotopyIso F d).inv_hom_id a)
  · rintro ⟨b,rfl⟩
    apply (stableHomotopyFiber_exact_loops f d _).mpr
    refine ⟨(parameterStableHomotopyIso E d).inv b, ?_⟩
    exact ConcreteCategory.congr_hom (parameterStableHomotopyIso_inv_naturality f d) b

/-- The original path-space fiber has the actual stable long exact sequence in
every integer degree, with the signed connecting map and no Omega hypothesis. -/
theorem stableFiberLongExactSequence (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d+1)).map f) (stableFiberConnecting f d) ∧
    Function.Exact (stableFiberConnecting f d)
      ((stableHomotopyFunctor d).map (homotopyFiberProjection f)) ∧
    Function.Exact ((stableHomotopyFunctor d).map (homotopyFiberProjection f))
      ((stableHomotopyFunctor d).map f) :=
  ⟨stableFiberConnecting_exact_target f d, stableFiberConnecting_exact_fiber f d,
    stableHomotopyFiber_exact_source f d⟩

end Topology.LoopPrespectrum
