/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Prespectrum.Omega
import Colib.Topology.HomotopyFiber.CylinderComparison
import Colib.Topology.Realization.BisimplicialContractibility

/-! Regression checks for full Omega equivalences, literal cylinder coordinates,
original prespectrum morphisms and the contractibility of the actual diagonal. -/

noncomputable section
open CategoryTheory Topology Opposite
open scoped Simplicial Topology unitInterval
universe u v w

namespace Topology.LoopPrespectrum

example (E : LoopPrespectrum.{u}) : IsOmega E ↔
    ∀ n, IsWeakHomotopyEquivalence (E.structureMap n) := Iff.rfl

example (E : OmegaSpectrum.{u}) (n : ℕ)
    (y : Path (E.obj.point (n + 1)) (E.obj.point (n + 1))) :
    ∃ x : E.obj.space n, Joined (E.obj.structureMap n x) y :=
  (E.property n).component_surjective y

example (E : OmegaSpectrum.{u}) (n k : ℕ) (x : E.obj.space n) :
    Function.Bijective (HomotopyGroup.map (N := Fin k) (E.obj.structureMap n)
      (x := x) rfl) := (E.property n).homotopy_bijective x k

-- Dimension zero is not omitted from the all-level property.
example (E : OmegaSpectrum.{u}) (n : ℕ) (x : E.obj.space n) :
    Function.Bijective (HomotopyGroup.map (N := Fin 0) (E.obj.structureMap n)
      (x := x) rfl) := (E.property n).homotopy_bijective x 0

-- Morphisms in the native full subcategory retain the original level maps and square.
example {E F : OmegaSpectrum.{u}} (f : E ⟶ F) (n : ℕ) (x : E.obj.space n) :
    basedLoopMap (f.hom.map (n + 1)) (f.hom.map_point (n + 1))
        (E.obj.structureMap n x) = F.obj.structureMap n (f.hom.map n x) :=
  f.hom.comm n x

example {E F : OmegaSpectrum.{u}} (f : E.obj ⟶ F.obj) :
    (ObjectProperty.homMk f : E ⟶ F).hom = f := rfl

example {E F G : OmegaSpectrum.{u}} (f : E ⟶ F) (g : F ⟶ G) (n : ℕ)
    (x : E.obj.space n) : (f ≫ g).hom.map n x = g.hom.map n (f.hom.map n x) := rfl

end Topology.LoopPrespectrum

section Cylinder

variable {X : Type u} {E : Type v} {B : Type w}
    [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) (e : E) (he : p e = b) (g : C(X, E))
    (hg : ∀ x, p (g x) = b) (H : (ContinuousMap.const X e).Homotopy g)

open Topology.HomotopyFiber unitInterval

example (x : X) (t : unitInterval) : cylinderLoop p b e he g hg H x t = p (H (t, x)) := rfl

example (x : X) : (cylinderStrictLift p b g hg x).1.1 = g x := rfl

example (x : X) (t : unitInterval) : (cylinderStrictLift p b g hg x).1.2 t = b := rfl

example (x : X) : cylinderStrictLift p b g hg x =
    strictFiberInclusion p b ⟨g x, hg x⟩ := rfl

example (s : unitInterval) (x : X) :
    (cylinderFiberHomotopy p b e he g hg H (s, x)).1.1 = H (s, x) := rfl

example (s t : unitInterval) (x : X) :
    (cylinderFiberHomotopy p b e he g hg H (s, x)).1.2 t =
      p (H (σ (σ s * σ t), x)) := rfl

example (x : X) : cylinderFiberHomotopy p b e he g hg H (0, x) =
    loopInclusion p b e he (cylinderLoop p b e he g hg H x) :=
  (cylinderFiberHomotopy p b e he g hg H).apply_zero x

example (x : X) : cylinderFiberHomotopy p b e he g hg H (1, x) =
    cylinderStrictLift p b g hg x := (cylinderFiberHomotopy p b e he g hg H).apply_one x

example : Continuous (fun z : unitInterval × X ↦
    cylinderFiberHomotopy p b e he g hg H z) :=
  (cylinderFiberHomotopy p b e he g hg H).continuous

end Cylinder

section Contractible

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] [ContractibleSpace Y] (f : C(X, Y)) (x : X)

example : (ContinuousMap.homotopyEquivOfContractible f x).toFun = f := rfl

example (y : Y) : (ContinuousMap.homotopyEquivOfContractible f x).invFun y = x := rfl

example : IsWeakHomotopyEquivalence f :=
  isWeakHomotopyEquivalence_of_homotopyEquiv (ContinuousMap.homotopyEquivOfContractible f x)

end Contractible

example (H : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    [PathConnectedSpace |H.obj (op ⦋0⦌)|] :
    PathConnectedSpace |SSet.diagonalSSet H| :=
  SSet.diagonal_pathConnected_of_zero_row H

example (H : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (h : ∀ n : SimplexCategory, ContractibleSpace |H.obj (op n)|) :
    ContractibleSpace |SSet.diagonalSSet H| :=
  SSet.diagonal_contractible_of_rows H h
