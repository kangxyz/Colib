/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.Topology.Prespectrum.FiberNaturality

/-!
# Naturality and stable transport of the specified fiber lift

Three actual maps between two composable pairs, their two strict squares, and
preservation of the specified whole null track give a strict square of the
original path-space fiber lifts. If the three maps are stable equivalences,
stability of either original lift is equivalent to stability of the other.
No inverse map, point-set excision, or additional compatibility data is chosen.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiberLiftNaturality.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual fiber coordinates, strict
structure maps, specified whole nullhomotopies, integer grading and connecting signs
are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

variable {S A O S' A' O' : LoopPrespectrum.{u}}
    (f : S ⟶ A) (r : A ⟶ O) (f' : S' ⟶ A') (r' : A' ⟶ O')
    (N : Homotopy (f ≫ r) (zeroHom S O))
    (N' : Homotopy (f' ≫ r') (zeroHom S' O'))
    (s : S ⟶ S') (a : A ⟶ A') (o : O ⟶ O')
    (hf : f ≫ a = s ≫ f') (hr : a ≫ r' = r ≫ o)
    (hN : ∀ n t x, o.map n (N.level n (t, x)) = N'.level n (t, s.map n x))

include hf hN in
/-- The actual fiber lift keeps its source coordinate and every original null time. -/
theorem homotopyFiberLift_naturality :
    homotopyFiberLift r f N ≫
        homotopyFiberMap (Arrow.homMk (f := Arrow.mk r) (g := Arrow.mk r') a o hr) =
      s ≫ homotopyFiberLift r' f' N' := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun k => k.map n x) hf
  · apply ContinuousMap.ext
    intro t
    exact hN n t x

include hf hr hN in
/-- Stable equivalences of the three original objects transport stability of the same-null lift
in either direction, without choosing inverses to those comparison maps. -/
theorem homotopyFiberLift_isStableEquivalence_iff
    (hs : IsStableEquivalence s) (ha : IsStableEquivalence a)
    (ho : IsStableEquivalence o) :
    IsStableEquivalence (homotopyFiberLift r f N) ↔
      IsStableEquivalence (homotopyFiberLift r' f' N') := by
  have hsq := homotopyFiberMap_isStableEquivalence
    (Arrow.homMk (f := Arrow.mk r) (g := Arrow.mk r') a o hr) ha ho
  have hn := homotopyFiberLift_naturality f r f' r' N N' s a o hf hr hN
  constructor
  · intro h d
    let := hs d
    apply (isIso_comp_left_iff ((stableHomotopyFunctor d).map s)
      ((stableHomotopyFunctor d).map (homotopyFiberLift r' f' N'))).mp
    rw [← Functor.map_comp, ← hn]
    exact (h.comp hsq) d
  · intro h d
    let := hsq d
    apply (isIso_comp_right_iff
      ((stableHomotopyFunctor d).map (homotopyFiberLift r f N))
      ((stableHomotopyFunctor d).map
        (homotopyFiberMap (Arrow.homMk (f := Arrow.mk r) (g := Arrow.mk r') a o hr)))).mp
    rw [← Functor.map_comp, hn]
    exact (hs.comp h) d

end Topology.LoopPrespectrum
