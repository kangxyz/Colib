/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Category.TopCat.ULift

/-!
# Descent from topological colimits to arbitrary target universes

The native universe-lift functor preserves colimits. Descending after this lift
and returning along its actual homeomorphism gives the same universal property
with a target space in an independent universe, preserving every colimit leg.

Implementation provenance: the first three declarations of
`Quillen/Topology/Realization/UniverseLift.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace TopCat

/-- Lift a compatible family into one common universe. -/
def colimitDescAcrossCocone {J : Type w} [Category J] {F : J ⥤ TopCat.{u}}
    {Z : Type v} [TopologicalSpace Z] (f : ∀ j, C(F.obj j, Z))
    (hf : ∀ {j k} (a : j ⟶ k) (x : F.obj j), f k (F.map a x) = f j x) :
    Cocone (F ⋙ TopCat.uliftFunctor.{v}) where
  pt := TopCat.of (ULift.{u} Z)
  ι := {
    app j := TopCat.ofHom ⟨fun x ↦ ULift.up (f j x.down), by fun_prop⟩
    naturality j k a := by
      ext x
      exact congrArg ULift.up (hf a x.down) }

/-- A colimit in topological spaces also descends to targets in other universes. -/
def colimitDescAcross {J : Type w} [Category J] {F : J ⥤ TopCat.{u}}
    (c : Cocone F) (hc : IsColimit c) {Z : Type v} [TopologicalSpace Z]
    (f : ∀ j, C(F.obj j, Z))
    (hf : ∀ {j k} (a : j ⟶ k) (x : F.obj j), f k (F.map a x) = f j x) :
    C(c.pt, Z) := by
  let g := (isColimitOfPreserves TopCat.uliftFunctor.{v} hc).desc
    (colimitDescAcrossCocone f hf)
  exact ⟨fun x ↦ (show ULift.{u} Z from g (ULift.up x)).down, by
    exact continuous_uliftDown.comp (g.hom.continuous.comp continuous_uliftUp)⟩

@[simp] theorem colimitDescAcross_ι
    {J : Type w} [Category J] {F : J ⥤ TopCat.{u}}
    (c : Cocone F) (hc : IsColimit c) {Z : Type v} [TopologicalSpace Z]
    (f : ∀ j, C(F.obj j, Z))
    (hf : ∀ {j k} (a : j ⟶ k) (x : F.obj j), f k (F.map a x) = f j x)
    (j : J) (x : F.obj j) :
    dsimp% colimitDescAcross c hc f hf (c.ι.app j x) = f j x := by
  exact congrArg (fun z : ULift.{u} Z ↦ z.down) (ConcreteCategory.congr_hom
    ((isColimitOfPreserves TopCat.uliftFunctor.{v} hc).fac
      (colimitDescAcrossCocone f hf) j) (ULift.up x))

end TopCat
