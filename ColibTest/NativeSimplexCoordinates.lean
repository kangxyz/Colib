/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Native simplex coordinate and realization regression tests

These source-only regressions use the pinned finite-support simplex directly.
They retain finite vertex maps, collapsed coordinates, realized naturality and
both orientations of the interval identification without a conversion model.
-/

open CategoryTheory
open scoped Simplicial Topology

noncomputable section

universe u

section Coordinates

variable {M N P : Type*} [Fintype M] [Fintype N] [Fintype P]

example (x : Convexity.StdSimplex ℝ M) : Convexity.StdSimplex.map id x = x :=
  Convexity.StdSimplex.map_id x

example (f : M → N) (g : N → P) (x : Convexity.StdSimplex ℝ M) :
    Convexity.StdSimplex.map g (Convexity.StdSimplex.map f x) =
      Convexity.StdSimplex.map (g.comp f) x :=
  (Convexity.StdSimplex.map_comp x f g).symm

example [DecidableEq M] [DecidableEq N] (f : M → N) (i : M) :
    Convexity.StdSimplex.map (R := ℝ) f (Convexity.StdSimplex.single i) =
      Convexity.StdSimplex.single (f i) :=
  Convexity.StdSimplex.map_single i f

example (x : Convexity.StdSimplex ℝ (Fin 2)) :
    Convexity.StdSimplex.map (fun _ : Fin 2 ↦ (0 : Fin 1)) x = Convexity.StdSimplex.single 0 := by
  apply Subsingleton.elim

example (x : Convexity.StdSimplex ℝ (Fin 2)) :
    Convexity.StdSimplex.map (SimplexCategory.σ (0 : Fin 1)) x = Convexity.StdSimplex.single 0 := by
  apply Subsingleton.elim

end Coordinates

example : Convexity.StdSimplex.homeomorphI (Convexity.StdSimplex.single 0) = 0 :=
  Convexity.StdSimplex.homeomorphI_single_zero

example : Convexity.StdSimplex.homeomorphI (Convexity.StdSimplex.single 1) = 1 :=
  Convexity.StdSimplex.homeomorphI_single_one

example : Convexity.StdSimplex.homeomorphI.symm 0 = Convexity.StdSimplex.single 0 :=
  Convexity.StdSimplex.homeomorphI.symm_apply_eq.mpr
    Convexity.StdSimplex.homeomorphI_single_zero.symm

example : Convexity.StdSimplex.homeomorphI.symm 1 = Convexity.StdSimplex.single 1 :=
  Convexity.StdSimplex.homeomorphI.symm_apply_eq.mpr
    Convexity.StdSimplex.homeomorphI_single_one.symm

example (x : Convexity.StdSimplex ℝ (Fin 2)) :
    ((Convexity.StdSimplex.homeomorphI x : unitInterval) : ℝ) = x.weights 1 :=
  Convexity.StdSimplex.homeomorphI_apply_coe x

example (t : unitInterval) :
    (Convexity.StdSimplex.homeomorphI.symm t).weights 0 = 1 - (t : ℝ) := by
  calc
    _ = 1 - (Convexity.StdSimplex.homeomorphI.symm t).weights 1 :=
      eq_sub_iff_add_eq.mpr (Convexity.StdSimplex.homeomorphI.symm t).total_fin_two
    _ = 1 - (t : ℝ) := by
      rw [← Convexity.StdSimplex.homeomorphI_apply_coe, Homeomorph.apply_symm_apply]

example (t : unitInterval) :
    (Convexity.StdSimplex.homeomorphI.symm t).weights 1 = (t : ℝ) := by
  rw [← Convexity.StdSimplex.homeomorphI_apply_coe, Homeomorph.apply_symm_apply]

example (x : Convexity.StdSimplex ℝ (Fin 2)) :
    (Homeomorph.ulift.symm : unitInterval ≃ₜ TopCat.I.{u})
      (Convexity.StdSimplex.homeomorphI x) = TopCat.stdSimplexHomeomorphI x := rfl

example {n m : SimplexCategory} (f : n ⟶ m)
    (x : |SSet.stdSimplex.{u}.obj n|) :
    SimplexCategory.toTopHomeo m (SSet.toTop.map (SSet.stdSimplex.map f) x) =
      Convexity.StdSimplex.map f (SimplexCategory.toTopHomeo n x) :=
  SimplexCategory.toTopHomeo_naturality_apply f x

example {n m : SimplexCategory} (f : n ⟶ m)
    (x : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    (SimplexCategory.toTopHomeo.{u} m).symm (Convexity.StdSimplex.map f x) =
      SSet.toTop.map (SSet.stdSimplex.map f) ((SimplexCategory.toTopHomeo n).symm x) :=
  SimplexCategory.toTopHomeo_symm_naturality_apply f x

example (x : |(Δ[1] : SSet.{u})|) :
    (Homeomorph.ulift.symm : unitInterval ≃ₜ TopCat.I.{u})
      (Convexity.StdSimplex.homeomorphI (SimplexCategory.toTopHomeo ⦋1⦌ x)) =
        SSet.stdSimplex.toTopObjIsoI.hom x := rfl
