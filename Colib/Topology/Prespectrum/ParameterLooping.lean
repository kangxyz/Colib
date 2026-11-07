/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.Homotopy
public import Colib.Topology.Path.DoubleLoopTranspose

/-!
Actual parameter-correct looping keeps structure time external and homotopy time internal. The
transpose is explicit.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/ParameterLooping.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original continuous families, independent
parameters, fixed boundaries and strict structure compatibility are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology

namespace LoopPrespectrum

/-- Looping with the homotopy parameter internal and the structure parameter external. -/
def parameterLooping (E : LoopPrespectrum.{u}) : LoopPrespectrum.{u} where
  space n := TopCat.of (Path (E.point n) (E.point n))
  point n := Path.refl (E.point n)
  structureMap n := (Path.doubleLoopTranspose (E.point (n+1))).comp
    (basedLoopMap (E.structureMap n) (E.map_point n))
  map_point n := by
    change Path.doubleLoopTranspose _ (basedLoopMap _ _ (Path.refl _)) = _
    rw [basedLoopMap_refl, Path.doubleLoopTranspose_refl]

/-- The map on transposed parameter looping induced by a prespectrum morphism. -/
def parameterLoopingMap {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    parameterLooping E ⟶ parameterLooping F where
  map n := basedLoopMap (f.map n) (f.map_point n)
  map_point n := basedLoopMap_refl (f.map n) (f.map_point n)
  comm n γ := by
    change Path (E.point n) (E.point n) at γ
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    exact congrArg (fun p ↦ p t) (f.comm n (γ s))

/-- Looping with the structure parameter external and the homotopy parameter internal. -/
def parameterLoopingFunctor : LoopPrespectrum.{u} ⥤ LoopPrespectrum.{u} where
  obj := parameterLooping
  map := parameterLoopingMap
  map_id E := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro γ
    apply Path.ext
    funext t
    rfl
  map_comp f g := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro γ
    apply Path.ext
    funext t
    rfl

/-- A coherent self-homotopy at the zero map is an actual map into parameter-correct loops. -/
def Homotopy.zeroLoopMap {E F : LoopPrespectrum.{u}}
    (H : Homotopy (zeroHom E F) (zeroHom E F)) : E ⟶ parameterLooping F where
  map n := {
    toFun x := {
      toFun s := H.level n (s,x)
      continuous_toFun := by fun_prop
      source' := H.at_zero n x
      target' := H.at_one n x }
    continuous_toFun := by
      apply Path.continuous_uncurry_iff.mp
      exact (H.level n).continuous.comp continuous_swap }
  map_point n := by apply Path.ext; funext s; exact H.at_point n s
  comm n x := by
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    exact H.comm n s x t

@[simp] theorem Homotopy.zeroLoopMap_apply {E F : LoopPrespectrum.{u}}
    (H : Homotopy (zeroHom E F) (zeroHom E F)) (n : ℕ) (x : E.space n) (s : unitInterval) :
    Path.toContinuousMap ((H.zeroLoopMap).map n x) s = H.level n (s,x) := rfl

end LoopPrespectrum
end Topology
