/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.Topology.Homotopy.HomotopyGroup.Equivalence

noncomputable section
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (e : ContinuousMap.HomotopyEquiv X Y) {x : X} {y : Y} (h : e.toFun x = y)

example (n : ℕ) : Function.Bijective (HomotopyGroup.piMap n e.toFun h) :=
  Topology.piMap_bijective_of_homotopyEquiv e h n

example (n : ℕ) :
    (Topology.homotopyEquivPiEquiv e h n).toMonoidHom = HomotopyGroup.piMap n e.toFun h := rfl

example (n : ℕ) (a : HomotopyGroup.Pi (n + 1) Y y) :
    ∃ b, HomotopyGroup.piMap n e.toFun h b = a :=
  (Topology.piMap_bijective_of_homotopyEquiv e h n).surjective a

example (f : C(X, Y)) (hf : f x = y) [ContractibleSpace (Topology.HomotopyFiber f y)]
    (n : ℕ) : Function.Bijective (HomotopyGroup.piMap n f hf) :=
  Topology.piMap_bijective_of_contractible_fiber f hf n
