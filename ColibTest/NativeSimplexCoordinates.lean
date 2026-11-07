/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Native simplex coordinate and realization regression tests

These source-only regressions use the pinned function-subtype simplex directly.
They retain finite vertex maps, collapsed coordinates, realized naturality and
both orientations of the interval identification without a conversion model.
-/

open CategoryTheory
open scoped Simplicial Topology

noncomputable section

universe u

section Coordinates

variable {M N P : Type*} [Fintype M] [Fintype N] [Fintype P]

example (x : stdSimplex ℝ M) : stdSimplex.map id x = x :=
  stdSimplex.map_id_apply x

example (f : M → N) (g : N → P) (x : stdSimplex ℝ M) :
    stdSimplex.map g (stdSimplex.map f x) = stdSimplex.map (g.comp f) x :=
  stdSimplex.map_comp_apply f g x

example [DecidableEq M] [DecidableEq N] (f : M → N) (i : M) :
    stdSimplex.map (S := ℝ) f (stdSimplex.vertex i) = stdSimplex.vertex (f i) :=
  stdSimplex.map_vertex f i

example (x : stdSimplex ℝ (Fin 2)) :
    stdSimplex.map (fun _ : Fin 2 ↦ (0 : Fin 1)) x = stdSimplex.vertex 0 := by
  apply Subsingleton.elim

example (x : stdSimplex ℝ (Fin 2)) :
    stdSimplex.map (SimplexCategory.σ (0 : Fin 1)) x = stdSimplex.vertex 0 := by
  apply Subsingleton.elim

end Coordinates

example : stdSimplexHomeomorphUnitInterval (stdSimplex.vertex 0) = 0 :=
  stdSimplexHomeomorphUnitInterval_zero

example : stdSimplexHomeomorphUnitInterval (stdSimplex.vertex 1) = 1 :=
  stdSimplexHomeomorphUnitInterval_one

example : stdSimplexHomeomorphUnitInterval.symm 0 = stdSimplex.vertex 0 :=
  stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
    stdSimplexHomeomorphUnitInterval_zero.symm

example : stdSimplexHomeomorphUnitInterval.symm 1 = stdSimplex.vertex 1 :=
  stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
    stdSimplexHomeomorphUnitInterval_one.symm

example (x : stdSimplex ℝ (Fin 2)) :
    ((stdSimplexHomeomorphUnitInterval x : unitInterval) : ℝ) = x 1 := rfl

example (t : unitInterval) : stdSimplexHomeomorphUnitInterval.symm t 0 = 1 - (t : ℝ) := rfl

example (t : unitInterval) : stdSimplexHomeomorphUnitInterval.symm t 1 = (t : ℝ) := rfl

example (x : stdSimplex ℝ (Fin 2)) :
    (Homeomorph.ulift.symm : unitInterval ≃ₜ TopCat.I.{u})
      (stdSimplexHomeomorphUnitInterval x) = TopCat.stdSimplexHomeomorphI x := rfl

example {n m : SimplexCategory} (f : n ⟶ m)
    (x : |SSet.stdSimplex.{u}.obj n|) :
    SimplexCategory.toTopHomeo m (SSet.toTop.map (SSet.stdSimplex.map f) x) =
      stdSimplex.map f (SimplexCategory.toTopHomeo n x) :=
  SimplexCategory.toTopHomeo_naturality_apply f x

example {n m : SimplexCategory} (f : n ⟶ m)
    (x : stdSimplex ℝ (Fin (n.len + 1))) :
    (SimplexCategory.toTopHomeo.{u} m).symm (stdSimplex.map f x) =
      SSet.toTop.map (SSet.stdSimplex.map f) ((SimplexCategory.toTopHomeo n).symm x) :=
  SimplexCategory.toTopHomeo_symm_naturality_apply f x

example (x : |(Δ[1] : SSet.{u})|) :
    (Homeomorph.ulift.symm : unitInterval ≃ₜ TopCat.I.{u})
      (stdSimplexHomeomorphUnitInterval (SimplexCategory.toTopHomeo ⦋1⦌ x)) =
        SSet.stdSimplex.toTopObjIsoI.hom x := rfl
