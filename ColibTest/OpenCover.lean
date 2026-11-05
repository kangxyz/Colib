/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Homotopy.OpenCover

/-!
# Open-cover path and subgroupoid regression tests

The hypotheses concern paths inside actual open sets. These tests do not assert
simplicial edge generation or a fundamental-groupoid equivalence.
-/

open CategoryTheory
open scoped Topology unitInterval

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

example {x y : X} (p : Path x y) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.range p ⊆ ⋃ i, U i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval),
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∀ k : Fin n, ∃ i, Set.range (p.subpath (t k.castSucc) (t k.succ)) ⊆ U i :=
  p.exists_subdivision_openCover U hU hcover

example (H : C(unitInterval × unitInterval, X))
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : Set.range H ⊆ ⋃ i, U i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval),
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∀ j k : Fin n, ∃ i,
        H '' (Set.Icc (t j.castSucc) (t j.succ) ×ˢ
          Set.Icc (t k.castSucc) (t k.succ)) ⊆ U i :=
  H.square_exists_subdivision_openCover U hU hcover

example (S : Subgroupoid (FundamentalGroupoid X))
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (hlocal : ∀ (i : ι) {x y : X} (p : Path x y), Set.range p ⊆ U i →
      (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _)
    {x y : X} (p : Path x y) :
    (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _ :=
  FundamentalGroupoid.path_mem_of_openCover S U hU hcover hlocal p

example (S : Subgroupoid (FundamentalGroupoid X))
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : Set.univ ⊆ ⋃ i, U i)
    (hlocal : ∀ (i : ι) {x y : X} (p : Path x y), Set.range p ⊆ U i →
      (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _) :
    S = ⊤ := FundamentalGroupoid.subgroupoid_eq_top_of_openCover S U hU hcover hlocal

example {V : Set X} (hV : IsSimplyConnected V) {x y : X}
    (p q : Path x y) (hp : Set.range p ⊆ V) (hq : Set.range q ⊆ V) : p.Homotopic q :=
  Path.homotopic_of_range_subset_isSimplyConnected hV p q hp hq

example (S : Subgroupoid (FundamentalGroupoid X))
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.univ ⊆ ⋃ i, U i) (hsc : ∀ i, IsSimplyConnected (U i))
    (hchosen : ∀ (i : ι) (x y : X), x ∈ U i → y ∈ U i →
      ∃ p : Path x y, Set.range p ⊆ U i ∧
        (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _) :
    S = ⊤ :=
  FundamentalGroupoid.subgroupoid_eq_top_of_simplyConnected_openCover S U hU hcover hsc hchosen
