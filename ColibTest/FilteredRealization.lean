/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FilteredRealization.HomotopyEquivalence

/-! Regression checks use an arbitrary filtered small category and the actual
realized maps. No transition is assumed monic, and no countability is assumed. -/
@[expose] public noncomputable section

open CategoryTheory Limits Topology
open scoped Simplicial

universe u v

namespace Topology.FilteredRealization

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)

example {T : Type v} [TopologicalSpace T] [CompactSpace T] (f : C(T, |c.pt|)) :
    ∃ j, ∃ g : C(T, |F.obj j|), (SSet.toTop.map (c.ι.app j)).hom.comp g = f :=
  compact_factors F c hc f

example {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (j : J) (f g : C(T, |F.obj j|))
    (h : (SSet.toTop.map (c.ι.app j)).hom.comp f =
      (SSet.toTop.map (c.ι.app j)).hom.comp g) :
    ∃ k, ∃ t : j ⟶ k, (SSet.toTop.map (F.map t)).hom.comp f =
      (SSet.toTop.map (F.map t)).hom.comp g :=
  compact_eq_eventually F c hc j f g h

variable
  (e : ∀ {j k : J} (_ : j ⟶ k), ContinuousMap.HomotopyEquiv |F.obj j| |F.obj k|)
  (he : ∀ {j k : J} (t : j ⟶ k), (e t).toFun = (SSet.toTop.map (F.map t)).hom)
  (j : J)

example : CompactHomotopyExtensionLiftingProperty (SSet.toTop.map (c.ι.app j)).hom :=
  stage_compactHELP F c hc e he j

example : (stageHomotopyEquiv F c hc e he j).toFun =
    (SSet.toTop.map (c.ι.app j)).hom := rfl

example :
    ((stageHomotopyEquiv F c hc e he j).invFun.comp
      (SSet.toTop.map (c.ι.app j)).hom).Homotopic (ContinuousMap.id |F.obj j|) :=
  (stageHomotopyEquiv F c hc e he j).left_inv

example :
    ((SSet.toTop.map (c.ι.app j)).hom.comp
      (stageHomotopyEquiv F c hc e he j).invFun).Homotopic (ContinuousMap.id |c.pt|) :=
  (stageHomotopyEquiv F c hc e he j).right_inv

end Topology.FilteredRealization
