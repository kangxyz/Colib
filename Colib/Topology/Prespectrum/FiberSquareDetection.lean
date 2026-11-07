/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.FiberNaturality

/-!
# Detecting the original target map from its fiber square

The actual all-integer fiber sequence and its original signed connecting map give the
remaining direction of the five-lemma comparison: stable equivalence on the source and
on the specified path-space fiber implies stable equivalence on the original target.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiberSquareDetection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual cone, full independent cylinder and loop parameters, signed degrees and
original hypotheses are retained under their native mathematical owners. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {A B : Arrow LoopPrespectrum.{u}}

/-- Source and original fiber equivalences detect the target of the same strict square. -/
theorem right_isStableEquivalence_of_fiber (sq : A ⟶ B)
    (hl : IsStableEquivalence sq.left) (hf : IsStableEquivalence (homotopyFiberMap sq)) :
    IsStableEquivalence sq.right := by
  have hs (d : ℤ) : IsIso ((stableHomotopyFunctor (d + 1)).map sq.right) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      ((stableHomotopyFunctor (d + 1)).map (homotopyFiberProjection A.hom)).hom
      ((stableHomotopyFunctor (d + 1)).map A.hom).hom (stableFiberConnecting A.hom d).hom
      ((stableHomotopyFunctor d).map (homotopyFiberProjection A.hom)).hom
      ((stableHomotopyFunctor (d + 1)).map (homotopyFiberProjection B.hom)).hom
      ((stableHomotopyFunctor (d + 1)).map B.hom).hom (stableFiberConnecting B.hom d).hom
      ((stableHomotopyFunctor d).map (homotopyFiberProjection B.hom)).hom
      ((stableHomotopyFunctor (d + 1)).map (homotopyFiberMap sq)).hom
      ((stableHomotopyFunctor (d + 1)).map sq.left).hom
      ((stableHomotopyFunctor (d + 1)).map sq.right).hom
      ((stableHomotopyFunctor d).map (homotopyFiberMap sq)).hom
      ((stableHomotopyFunctor d).map sq.left).hom
      ?_ ?_ ?_ ?_
      (stableHomotopyFiber_exact_source A.hom (d + 1))
      (stableFiberConnecting_exact_target A.hom d)
      (stableFiberConnecting_exact_fiber A.hom d)
      (stableHomotopyFiber_exact_source B.hom (d + 1))
      (stableFiberConnecting_exact_target B.hom d)
      (stableFiberConnecting_exact_fiber B.hom d)
      ((ConcreteCategory.isIso_iff_bijective _).mp (hf (d + 1))).surjective
      ((ConcreteCategory.isIso_iff_bijective _).mp (hl (d + 1)))
      ((ConcreteCategory.isIso_iff_bijective _).mp (hf d))
      ((ConcreteCategory.isIso_iff_bijective _).mp (hl d)).injective
    · ext x
      have he := congrArg ((stableHomotopyFunctor (d + 1)).map)
        (homotopyFiberProjection_naturality sq)
      rw [Functor.map_comp, Functor.map_comp] at he
      exact ConcreteCategory.congr_hom he x
    · ext x
      have he := congrArg ((stableHomotopyFunctor (d + 1)).map) sq.w
      rw [Functor.map_comp, Functor.map_comp] at he
      exact ConcreteCategory.congr_hom he x
    · ext x
      exact ConcreteCategory.congr_hom (stableFiberConnecting_naturality sq d) x
    · ext x
      have he := congrArg ((stableHomotopyFunctor d).map)
        (homotopyFiberProjection_naturality sq)
      rw [Functor.map_comp, Functor.map_comp] at he
      exact ConcreteCategory.congr_hom he x
  intro d
  have h := hs (d - 1)
  rw [show d - 1 + 1 = d by omega] at h
  exact h

end Topology.LoopPrespectrum
