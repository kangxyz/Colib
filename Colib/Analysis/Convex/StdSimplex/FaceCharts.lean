/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.Analysis.Convex.StdSimplex.Boundary
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-! # Coordinates of native simplex faces

Direct weight proofs for the native finite-support simplex, used for finite face gluing.
Adapted from the face constructions in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

namespace Convexity.StdSimplex

/-- Finite barycentric simplices are Hausdorff, as subspaces of finite real products. -/
instance finiteStdSimplex_t2Space {M : Type*} [Finite M] : T2Space (StdSimplex ℝ M) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ M).t2Space


/-- An injective vertex map preserves each coordinate at its image. -/
theorem map_apply_injective {A B : Type*}
    {f : A → B} (hf : Function.Injective f) (x : StdSimplex ℝ A) (a : A) :
    (x.map f).weights (f a) = x.weights a :=
  Finsupp.mapDomain_apply_of_injective hf x.weights a

/-- The coordinate omitted by an increasing face map is zero. -/
theorem map_succAbove_self {d : ℕ} (i : Fin (d + 2))
    (x : StdSimplex ℝ (Fin (d + 1))) : (x.map i.succAbove).weights i = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, hj⟩
  exact Fin.succAbove_ne _ _ hj

/-- Every zero-coordinate point has a native face preimage. -/
theorem mem_range_map_succAbove_iff {d : ℕ} (i : Fin (d + 2))
    (x : StdSimplex ℝ (Fin (d + 2))) :
    x ∈ Set.range (StdSimplex.map i.succAbove) ↔ x.weights i = 0 := by
  rw [StdSimplex.mem_range_map_iff]
  constructor
  · intro h
    exact h i (by rintro ⟨j, hj⟩; exact Fin.succAbove_ne _ _ hj)
  · intro hi j hj
    have hji : j = i := by
      by_contra hne
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
      exact hj ⟨k, hk⟩
    simpa only [hji] using hi

/-- Injective maps of vertices are injective on native simplex points. -/
theorem simplex_map_injective {A B : Type*}
    {f : A → B} (hf : Function.Injective f) :
    Function.Injective (StdSimplex.map (R := ℝ) f) := by
  intro x y h
  apply StdSimplex.ext
  apply Finsupp.mapDomain_injective hf
  exact congrArg StdSimplex.weights h

end Convexity.StdSimplex
