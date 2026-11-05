/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.SourceEquivalence
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift

/-!
# Homotopy groups of contractible spaces

No contraction is required to fix the chosen point. The based loop space is
identified with the homotopy fiber of the point inclusion, which is an unbased
homotopy equivalence. Its contractibility and the genuine loop-degree shift
then give triviality in every finite degree, including the zeroth homotopy set.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/Contractible.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space models,
basepoint tracks, maps and universe parameters are retained. -/
@[expose] public section


noncomputable section
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X]

/-- The inclusion of any chosen point into a contractible space is a homotopy
equivalence; its inverse homotopies need not fix that point. -/
def pointHomotopyEquiv [ContractibleSpace X] (x : X) :
    ContinuousMap.HomotopyEquiv Unit X where
  toFun := ContinuousMap.const Unit x
  invFun := ContinuousMap.const X ()
  left_inv := by
    have h : (ContinuousMap.const X ()).comp (ContinuousMap.const Unit x) =
        ContinuousMap.id Unit := by ext a
    rw [h]
  right_inv := by
    obtain ⟨c, ⟨H⟩⟩ := id_nullhomotopic X
    exact ⟨(H.evalAt x).toHomotopyConst.trans H.symm⟩

/-- The based loop space of a contractible space is contractible, without a
well-pointedness assumption on the chosen basepoint. -/
theorem contractibleSpace_loopSpace [ContractibleSpace X] (x : X) :
    ContractibleSpace (Path x x) := by
  let : ContractibleSpace (HomotopyFiber (ContinuousMap.const Unit x) x) :=
    HomotopyFiber.contractibleSpace_homotopyEquiv (pointHomotopyEquiv x) x
  exact ((HomotopyFiber.constantHomeomorph Unit x x).trans
    (Homeomorph.uniqueProd Unit (Path x x))).symm.contractibleSpace

/-- All actual finite-dimensional homotopy sets of a contractible space have
one element, including degree zero. -/
theorem subsingleton_pi_of_contractible (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ContractibleSpace X] (x : X) : Subsingleton (HomotopyGroup.Pi n X x) := by
  induction n generalizing X with
  | zero =>
    exact (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).injective.subsingleton
  | succ n ih =>
    let : ContractibleSpace (Path x x) := contractibleSpace_loopSpace x
    let : Subsingleton (HomotopyGroup.Pi n (Path x x) (Path.refl x)) := ih _ _
    exact (loopShiftEquiv (x := x) n).injective.subsingleton

/-- Every positive homotopy-group element of a contractible space is identity. -/
theorem pi_eq_one_of_contractible [ContractibleSpace X] (x : X) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) X x) : a = 1 := by
  let := subsingleton_pi_of_contractible (n + 1) X x
  exact Subsingleton.elim _ _

end Topology
