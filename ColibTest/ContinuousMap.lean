/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

import Colib.Topology.ContinuousMap
import Mathlib.Basic.Nontrivial.Basic
import Mathlib.Geometry.Convex.ConvexSpace.Topology
import Mathlib.Topology.UnitInterval

/-!
# Continuous product extension families

These tests cover arbitrary predicates, empty selected families, singleton
codomains, and degreewise finite families on the native finitely supported
standard simplex.
-/

open scoped Topology unitInterval

section GeneralFamily

variable {X T Z : Type*}
    [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace Z]
    (p : C(X, Z) → Prop)

example : Nonempty ({f : C(X, Z) // p f} → C(X × T, Z)) := inferInstance

example (f : {f : C(X, Z) // p f}) (x : X) (t : T) :
    (f.val.comp (ContinuousMap.fst : C(X × T, X))) (x, t) = f.val x := rfl

example : Nonempty ({_f : C(X, Z) // False} → C(X × T, Z)) := inferInstance

example : ¬ Nontrivial ({_f : C(X, Z) // False} → C(X × T, Z)) :=
  fun h ↦ let ⟨_, _, hfg⟩ := h.exists_pair_ne
    hfg (funext fun s ↦ False.elim s.property)

end GeneralFamily

section SingletonCodomain

variable {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    [TopologicalSpace PUnit] (p : C(X, PUnit) → Prop)

example : Nonempty ({f : C(X, PUnit) // p f} → C(X × T, PUnit)) := inferInstance

example : ¬ Nontrivial ({f : C(X, PUnit) // p f} → C(X × T, PUnit)) :=
  not_nontrivial _

end SingletonCodomain

section SimplexFamily

variable {Z : Type*} [TopologicalSpace Z]
    (S : ∀ d : ℕ, Finset C(Convexity.StdSimplex ℝ (Fin (d + 1)), Z)) (d : ℕ)

example : Nonempty ({s // s ∈ S d} →
    C(Convexity.StdSimplex ℝ (Fin (d + 1)) × I, Z)) := inferInstance

example : ∀ d : ℕ, Nonempty ({s // s ∈ S d} →
    C(Convexity.StdSimplex ℝ (Fin (d + 1)) × I, Z)) := inferInstance

example : Nonempty (∀ d : ℕ,
    {s // s ∈ S d} → C(Convexity.StdSimplex ℝ (Fin (d + 1)) × I, Z)) := inferInstance

example : ∀ d : ℕ, Nonempty ({s // s ∈ S d} →
    C(Convexity.StdSimplex ℝ (Fin (d + 1)) × I, Z)) :=
  fun _ ↦ ⟨fun s ↦ s.val.comp ContinuousMap.fst⟩

example (s : {s // s ∈ S d})
    (x : Convexity.StdSimplex ℝ (Fin (d + 1))) (t : I) :
    (s.val.comp (ContinuousMap.fst : C(Convexity.StdSimplex ℝ (Fin (d + 1)) × I,
      Convexity.StdSimplex ℝ (Fin (d + 1))))) (x, t) = s.val x := rfl

end SimplexFamily
