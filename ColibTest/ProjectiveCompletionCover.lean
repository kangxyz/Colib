/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.KTheory.Quillen.ProjectiveCompletionCover
import Colib.Topology.Covering.PullbackFiber

/-! Regression checks for the actual zero-component cover and its canonical maps. -/
noncomputable section
open CategoryTheory Topology
open scoped Topology
universe u v w

example (R : Type u) [Ring R] :
    ∃ T : Type (u + 1), ∃ t : TopologicalSpace T,
      letI := t
      ∃ q : C(T, ModuleCat.FiniteProjective.StableCompletion.ZeroComponent R),
        IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace T :=
  ModuleCat.FiniteProjective.StableCompletion.exists_simplyConnected_zeroComponent_cover R

example (C : Type u) [Category.{v} C] (c : C) :
    ∃ T : Type (max u v), ∃ t : TopologicalSpace T,
      letI := t
      ∃ q : C(T, pathComponent (classifyingSpacePoint c)),
        IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace T :=
  exists_simplyConnected_classifying_component_cover C c

variable {X : Type u} {Y : Type v} {E : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
  (f : C(X, Y)) (q : C(E, Y)) (hq : IsCoveringMap q)
  (z : Covering.Pullback.Space f q)

example (e : E) (a : HomotopyGroup.Pi 2 E e) :
    hq.piProjectionEquiv 0 e rfl a = HomotopyGroup.piMap 1 q rfl a := rfl

example [SimplyConnectedSpace E] (a : HomotopyGroup.Pi 1 (Covering.Pullback.Space f q) z) :
    (Covering.Pullback.piOneKernelEquiv f q hq z a : HomotopyGroup.Pi 1 X z.val.1) =
      HomotopyGroup.piMap 0 (Covering.Pullback.projection f q) rfl a := rfl

example [SimplyConnectedSpace E] :
    Function.Bijective (Covering.Pullback.fiberPiOneMap f q z) :=
  Covering.Pullback.fiberPiOneMap_bijective f q hq z
