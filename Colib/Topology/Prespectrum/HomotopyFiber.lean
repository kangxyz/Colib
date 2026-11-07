/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.Homotopy
public import Colib.Topology.HomotopyFiber.Basic

/-!
The actual path-space fiber prespectrum, its literal projection and coherent based nullhomotopy.
Specified coherent nullhomotopies lift with both the original source coordinate and the entire path
retained. No Omega or cofiber comparison is assumed.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/HomotopyFiber.lean` at Quillen commit
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

/-- The original structure maps send a fiber point to a based loop in the next
actual homotopy fiber; the fiber path parameter remains independent. -/
def homotopyFiberStructureMap (n : ℕ) :
    C(HomotopyFiber (f.map n) (F.point n),
      Path (HomotopyFiber.basepoint (f.map (n+1)) (F.point (n+1))
        (E.point (n+1)) (f.map_point (n+1)))
        (HomotopyFiber.basepoint (f.map (n+1)) (F.point (n+1))
        (E.point (n+1)) (f.map_point (n+1)))) where
  toFun z :=
    { toFun t := ⟨(E.structureMap n z.1.1 t,
        ⟨fun s ↦ F.structureMap n (z.1.2 s) t, by fun_prop⟩),
        by
          change F.structureMap n (z.1.2 0) t = f.map (n+1) (E.structureMap n z.1.1 t)
          rw [z.2.1]
          exact (congrArg (fun p ↦ p t) (f.comm n z.1.1)).symm,
        by
          change F.structureMap n (z.1.2 1) t = F.point (n+1)
          rw [z.2.2, F.map_point]
          rfl⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.prodMk
        · fun_prop
        · apply ContinuousMap.continuous_of_continuous_uncurry
          change Continuous (fun q : unitInterval × unitInterval ↦
            F.structureMap n (z.1.2 q.2) q.1)
          fun_prop
      source' := by
        apply Subtype.ext
        apply Prod.ext
        · exact (E.structureMap n z.1.1).source
        · apply ContinuousMap.ext
          intro s
          exact (F.structureMap n (z.1.2 s)).source
      target' := by
        apply Subtype.ext
        apply Prod.ext
        · exact (E.structureMap n z.1.1).target
        · apply ContinuousMap.ext
          intro s
          exact (F.structureMap n (z.1.2 s)).target }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun q :
        (HomotopyFiber (f.map n) (F.point n) × unitInterval) × unitInterval ↦
          F.structureMap n (q.1.1.1.2 q.2) q.1.2)
      fun_prop

lemma homotopyFiberStructureMap_point (n : ℕ) :
    homotopyFiberStructureMap f n
      (HomotopyFiber.basepoint (f.map n) (F.point n) (E.point n) (f.map_point n)) =
      Path.refl (HomotopyFiber.basepoint (f.map (n+1)) (F.point (n+1))
        (E.point (n+1)) (f.map_point (n+1))) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  apply Prod.ext
  · change E.structureMap n (E.point n) t = E.point (n+1)
    rw [E.map_point]
    rfl
  · apply ContinuousMap.ext
    intro s
    change F.structureMap n (F.point n) t = F.point (n+1)
    rw [F.map_point]
    rfl

/-- Actual path-space homotopy fibers form a genuine loop prespectrum. -/
def homotopyFiber : LoopPrespectrum.{u} where
  space n := TopCat.of (HomotopyFiber (f.map n) (F.point n))
  point n := HomotopyFiber.basepoint (f.map n) (F.point n) (E.point n) (f.map_point n)
  structureMap n := homotopyFiberStructureMap f n
  map_point n := homotopyFiberStructureMap_point f n

/-- The literal source-coordinate projection is a map of original prespectra. -/
def homotopyFiberProjection : homotopyFiber f ⟶ E where
  map n := HomotopyFiber.projection (f.map n) (F.point n)
  map_point _n := rfl
  comm _n _z := by ext t; rfl

/-- The entire original fiber path gives a coherent based nullhomotopy. -/
def homotopyFiberNullHomotopy :
    Homotopy (homotopyFiberProjection f ≫ f) (zeroHom (homotopyFiber f) F) where
  level n := (HomotopyFiber.projectionNullhomotopy (f.map n) (F.point n)).toContinuousMap
  at_zero _n z := z.2.1
  at_one _n z := z.2.2
  at_point _n _s := rfl
  comm _n _s _z _t := rfl

end Topology.LoopPrespectrum

end


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {A E F : LoopPrespectrum.{u}} (f : E ⟶ F) (g : A ⟶ E)

/-- A specified coherent based nullhomotopy gives the actual lift into the
path-space fiber, with its original source coordinate and full path. -/
def homotopyFiberLift (H : Homotopy (g ≫ f) (zeroHom A F)) : A ⟶ homotopyFiber f where
  map n := HomotopyFiber.lift (f.map n) (F.point n) (g.map n)
    (H.levelHomotopy n).toHomotopy
  map_point n := by
    apply Subtype.ext
    apply Prod.ext
    · exact g.map_point n
    · apply ContinuousMap.ext
      intro s
      exact H.at_point n s
  comm n x := by
    apply Path.ext
    funext t
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun p ↦ p t) (g.comm n x)
    · apply ContinuousMap.ext
      intro s
      exact H.comm n s x t

@[simp] theorem homotopyFiberLift_source
    (H : Homotopy (g ≫ f) (zeroHom A F)) (n : ℕ) (x : A.space n) :
    ((homotopyFiberLift f g H).map n x).1.1 = g.map n x := rfl

@[simp] theorem homotopyFiberLift_path
    (H : Homotopy (g ≫ f) (zeroHom A F)) (n : ℕ) (x : A.space n) (s : unitInterval) :
    ((homotopyFiberLift f g H).map n x).1.2 s = H.level n (s,x) := rfl

@[simp] theorem homotopyFiberLift_projection
    (H : Homotopy (g ≫ f) (zeroHom A F)) :
    homotopyFiberLift f g H ≫ homotopyFiberProjection f = g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  rfl

end Topology.LoopPrespectrum
