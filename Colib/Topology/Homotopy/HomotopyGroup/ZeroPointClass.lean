/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Map
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Actual points in the original zero-dimensional homotopy set

Every original zero class has an actual point representative, and discreteness
makes that representative unique. Actual continuous maps preserve these classes.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/ZeroPointClass.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u v
namespace Topology
variable {X : Type u} [TopologicalSpace X]

/-- An actual point represents an original zero-dimensional homotopy class. -/
def zeroPointClass (x z : X) : HomotopyGroup.Pi 0 X x :=
  Quotient.mk' (⟨ContinuousMap.const _ z, by rintro t ⟨i, _⟩; exact Fin.elim0 i⟩ :
    GenLoop (Fin 0) X x)

lemma zeroPointClass_surjective (x : X) : Function.Surjective (zeroPointClass x) := by
  intro a
  induction a using Quotient.inductionOn with | _ p =>
    refine ⟨p 0, congrArg Quotient.mk' ?_⟩
    apply GenLoop.ext
    intro t
    exact congrArg p (Subsingleton.elim _ _)

lemma zeroPointClass_injective_of_discrete [DiscreteTopology X] (x : X) :
    Function.Injective (zeroPointClass x) := by
  intro z w h
  obtain ⟨H⟩ := Quotient.exact h
  have e := PreconnectedSpace.constant inferInstance H.toHomotopy.continuous
    (x := (0, (0 : Fin 0 → unitInterval))) (y := (1, (0 : Fin 0 → unitInterval)))
  exact (H.toHomotopy.map_zero_left 0).symm.trans
    (e.trans (H.toHomotopy.map_one_left 0))

lemma homotopyGroupMap_zeroPointClass {Y : Type*} [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y : Y} (h : f x = y) (z : X) :
    HomotopyGroup.map f h (zeroPointClass x z) = zeroPointClass y (f z) := rfl

end Topology
