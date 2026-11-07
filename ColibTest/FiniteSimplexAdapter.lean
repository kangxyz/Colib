/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Realization.FiniteSimplexAdapter

/-!
# Finite simplex coordinate and realization regression tests

Both inverse directions, collapsed vertex maps and interval orientation are
checked on the actual old/new coordinates and the pinned realization functor.
No realization product or prism-gluing theorem is asserted here.
-/

open CategoryTheory FiniteSimplexAdapter
open scoped Simplicial

noncomputable section

section Coordinates

set_option linter.deprecated false

variable {M N : Type*} [Fintype M] [Fintype N]

example (x : stdSimplex ℝ M) : toOld (toConvex x) = x := by simp

example (x : Convexity.StdSimplex ℝ M) : toConvex (toOld x) = x := by simp

example (x : stdSimplex ℝ M) (i : M) : (homeomorph M x).weights i = x i := by simp

example (f : M → N) (x : stdSimplex ℝ M) :
    toConvex (stdSimplex.map f x) = Convexity.StdSimplex.map f (toConvex x) :=
  toConvex_map f x

example (x : stdSimplex ℝ (Fin 2)) :
    toConvex (stdSimplex.map (fun _ : Fin 2 => (0 : Fin 1)) x) =
      Convexity.StdSimplex.map (fun _ : Fin 2 => (0 : Fin 1)) (toConvex x) :=
  toConvex_map _ x

example (x : Convexity.StdSimplex ℝ (Fin 2)) :
    toOld (Convexity.StdSimplex.map (fun _ : Fin 2 => (0 : Fin 1)) x) =
      stdSimplex.map (fun _ : Fin 2 => (0 : Fin 1)) (toOld x) := toOld_map _ x

example [DecidableEq M] (i : M) :
    toConvex (stdSimplex.vertex i) = Convexity.StdSimplex.single i := by simp

example (x : stdSimplex ℝ (Fin 2)) :
    Convexity.StdSimplex.homeomorphI (toConvex x) = stdSimplexHomeomorphUnitInterval x :=
  interval_compat x

example (x : stdSimplex ℝ (Fin 2)) :
    (Homeomorph.ulift.symm : unitInterval ≃ₜ TopCat.I)
      (Convexity.StdSimplex.homeomorphI (toConvex x)) =
        (Homeomorph.ulift.symm : unitInterval ≃ₜ TopCat.I) (stdSimplexHomeomorphUnitInterval x) :=
  interval_ulift_compat x

example (x : stdSimplex ℝ (Fin 2)) :
    ((Convexity.StdSimplex.homeomorphI (toConvex x) : unitInterval) : ℝ) = x 1 := by
  rw [Convexity.StdSimplex.homeomorphI_apply_coe, toConvex_weights]

end Coordinates

example {n m : SimplexCategory} (f : n ⟶ m) (x : |SSet.stdSimplex.obj n|) :
    toTopHomeomorph m (SSet.toTop.map (SSet.stdSimplex.map f) x) =
      Convexity.StdSimplex.map f (toTopHomeomorph n x) :=
  toTopHomeomorph_naturality_apply f x

example {n m : SimplexCategory} (f : n ⟶ m)
    (x : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    (toTopHomeomorph m).symm (Convexity.StdSimplex.map f x) =
      SSet.toTop.map (SSet.stdSimplex.map f) ((toTopHomeomorph n).symm x) :=
  toTopHomeomorph_symm_naturality_apply f x

example (x : |(Δ[1] : SSet)|) :
    (Homeomorph.ulift.symm : unitInterval ≃ₜ TopCat.I)
      (Convexity.StdSimplex.homeomorphI (toTopHomeomorph ⦋1⦌ x)) =
        SSet.stdSimplex.toTopObjIsoI.hom x := realization_interval_compat x
