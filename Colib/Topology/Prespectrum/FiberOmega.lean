/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Loop
public import Colib.Topology.HomotopyFiber.BasedSquareMap
public import Colib.Topology.Prespectrum.HomotopyFiber
public import Colib.Topology.Prespectrum.Omega

/-!
Actual path-space fibers of Omega-spectra retain the complete Omega property, including every
component condition.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiberOmega.lean` at Quillen commit
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

/-- The actual structure square defines a map into the fiber of the next loop map. -/
def homotopyFiberStructureComparison (n : ℕ) :
    C(HomotopyFiber (f.map n) (F.point n),
      HomotopyFiber (basedLoopMap (f.map (n+1)) (f.map_point (n+1)))
        (Path.refl (F.point (n+1)))) :=
  HomotopyFiber.mapAt (E.structureMap n) (F.structureMap n)
    (by ext x t; exact (congrArg (fun p ↦ p t) (f.comm n x)).symm)
    (F.point n) (Path.refl (F.point (n+1))) (F.map_point n)

/-- The original fiber structure is literally the structure-square map followed
by transposition of its two independent path parameters. -/
theorem homotopyFiberStructureMap_eq (n : ℕ) :
    homotopyFiberStructureMap f n =
      (HomotopyFiber.loopFiberHomeomorph (f.map (n+1)) (f.map_point
        (n+1))).toHomotopyEquiv.toFun.comp
        (homotopyFiberStructureComparison f n) := by
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

/-- Path-space fibers of maps of genuine Omega-spectra are genuine Omega-spectra,
including the component condition at every actual structure map. -/
theorem homotopyFiber_isOmega (hE : E.IsOmega) (hF : F.IsOmega) :
    (homotopyFiber f).IsOmega := by
  intro n
  change IsWeakHomotopyEquivalence (homotopyFiberStructureMap f n)
  rw [homotopyFiberStructureMap_eq]
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv
    (HomotopyFiber.loopFiberHomeomorph (f.map (n+1))
      (f.map_point (n+1))).toHomotopyEquiv).comp
    (HomotopyFiber.mapAt_weak _ _ _ (hE n) (hF n) _ _ _)

end Topology.LoopPrespectrum
