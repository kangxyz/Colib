/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Residue.UnramifiedMapAcross

open Stacks.Chow

universe u v w z

variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type w} {E : Type z} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) [IsLocalHom j] (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R} (hπ : Irreducible π) (hjπ : Irreducible (j π))

-- Arbitrary classes and all residue degrees, with four independent universes.
example (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    milnorKTheoryMap (IsLocalRing.ResidueField.map j) n (dvrMilnorTameSymbol hπ n x) =
      dvrMilnorTameSymbol hjπ n (milnorKTheoryMap f (n + 1) x) :=
  DFunLike.congr_fun (dvrMilnorTameSymbol_map_across j f hf hπ hjπ n) x

-- The degree-one residue lands in degree zero; no positivity assumption is hidden.
example (x : MilnorKTheory F 1) :
    milnorKTheoryMap (IsLocalRing.ResidueField.map j) 0 (dvrMilnorTameSymbol hπ 0 x) =
      dvrMilnorTameSymbol hjπ 0 (milnorKTheoryMap f 1 x) :=
  DFunLike.congr_fun (dvrMilnorTameSymbol_map_across j f hf hπ hjπ 0) x

-- The ring extension and the already maintained homogeneous map agree on every class.
example {k : Type u} {K : Type v} [Field k] [Field K] (g : k →+* K)
    (n : ℕ) (x : MilnorKTheory k n) :
    milnorKRingMapLift g (x : MilnorKRing k) = (milnorKTheoryMap g n x : MilnorKRing K) :=
  milnorKRingMapLift_coe g n x

-- A common-universe input recovers the pinned Stacks ring map exactly.
example {k K : Type u} [Field k] [Field K] (g : k →+* K) :
    milnorKRingMapLift g = milnorKRingMap g := milnorKRingMapLift_eq g
