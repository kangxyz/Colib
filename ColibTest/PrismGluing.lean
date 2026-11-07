/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Realization.PrismGluing

/-!
# Realized standard prism regression tests

The homeomorphism is asserted only for standard simplices. The general cylinder
comparison is tested as a natural continuous map, not as an isomorphism.
-/

open Convexity.StdSimplex CategoryTheory MonoidalCategory
  CartesianMonoidalCategory Opposite
open scoped Simplicial Topology unitInterval

universe u

noncomputable section

open SSet

example (X : SSet.{u}) : realizationCylinderComparison X ≫ fst _ _ =
    SSet.toTop.map (fst X Δ[1]) := realizationCylinderComparison_fst X

example (X : SSet.{u}) : realizationCylinderComparison X ≫ snd _ _ =
    SSet.toTop.map (snd X Δ[1]) ≫ SSet.stdSimplex.toTopObjIsoI.hom :=
  realizationCylinderComparison_snd X

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map (f ▷ Δ[1]) ≫ realizationCylinderComparison Y =
      realizationCylinderComparison X ≫ (SSet.toTop.map f ▷ TopCat.I) :=
  realizationCylinderComparison_naturality f

example {n : ℕ} (i : Fin (n + 1)) : realizationPrismCell.{u} i =
    SSet.toTop.map (SSet.yonedaEquiv.symm
      (SSet.prodStdSimplex₁.nonDegenerateEquiv i).val) := rfl

example {n : ℕ} (i : Fin (n + 1)) (v : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    realizationPrismCoordinates n (realizationPrismCell.{u} i
      ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm v)) = prismProject i v :=
  realizationPrismCoordinates_cell i v

example {n : ℕ} (x : |(Δ[n] ⊗ Δ[1] : SSet.{u})|) :
    ∃ (i : Fin (n + 1)) (t : |(Δ[n + 1] : SSet.{u})|), realizationPrismCell i t = x :=
  realizationPrismCell_jointly_surjective x

example {n : ℕ} {m : SimplexCategoryᵒᵖ} (s : (Δ[n] ⊗ Δ[1] : SSet.{u}).obj m) :
    ∃ (i : Fin (n + 1)) (f : m.unop ⟶ ⦋n + 1⦌),
      (Δ[n] ⊗ Δ[1]).map f.op (SSet.prodStdSimplex₁.nonDegenerateEquiv i).val = s :=
  prism_simplex_factors s

example {n : ℕ} (i : Fin n) :
    SSet.toTop.map (SSet.stdSimplex.δ i.castSucc.succ) ≫
        realizationPrismCell.{u} i.castSucc =
      SSet.toTop.map (SSet.stdSimplex.δ i.succ.castSucc) ≫
        realizationPrismCell.{u} i.succ := realizationPrismCell_adjacent_face i

example {n : ℕ} (i : Fin (n + 1)) (z : prismCell i) :
    realizationPrismLift.{u} i z = realizationPrismCell i
      ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm (prismLift i z)) := rfl

example {n : ℕ} (i : Fin (n + 1)) (z : prismCell i) :
    realizationPrismCoordinates n (realizationPrismLift.{u} i z) = z.1 :=
  realizationPrismCoordinates_lift i z

example {n : ℕ} (i : Fin (n + 1))
    {z : Convexity.StdSimplex ℝ (Fin (n + 2)) × unitInterval}
    (hi : z ∈ prismCell i.castSucc) (hj : z ∈ prismCell i.succ) :
    realizationPrismLift.{u} i.castSucc ⟨z, hi⟩ =
      realizationPrismLift.{u} i.succ ⟨z, hj⟩ := realizationPrismLift_adjacent i hi hj

example {n : ℕ} (i j : Fin (n + 1))
    {z : Convexity.StdSimplex ℝ (Fin (n + 1)) × unitInterval}
    (hi : z ∈ prismCell i) (hj : z ∈ prismCell j) :
    realizationPrismLift.{u} i ⟨z, hi⟩ = realizationPrismLift.{u} j ⟨z, hj⟩ :=
  realizationPrismLift_overlap i j hi hj

example (n : ℕ) : Function.Bijective (realizationPrismCoordinates.{u} n) :=
  ⟨realizationPrismCoordinates_injective n, realizationPrismCoordinates_surjective n⟩

example (n : ℕ) (x : |(Δ[n] ⊗ Δ[1] : SSet.{u})|) :
    realizationPrismHomeomorph n x = realizationPrismCoordinates n x := rfl

example (n : ℕ) (x : |(Δ[n] ⊗ Δ[1] : SSet.{u})|) :
    (realizationPrismHomeomorph n).symm (realizationPrismCoordinates n x) = x :=
  (realizationPrismHomeomorph n).symm_apply_apply x

example (n : ℕ) (z : Convexity.StdSimplex ℝ (Fin (n + 1)) × unitInterval) :
    realizationPrismCoordinates n ((realizationPrismHomeomorph.{u} n).symm z) = z :=
  (realizationPrismHomeomorph n).apply_symm_apply z

example (n : ℕ) (x : |(Δ[n] ⊗ Δ[1] : SSet.{u})|) :
    (SimplexCategory.toTopHomeo ⦋n⦌
        ((realizationCylinderComparison Δ[n] x).1),
      (realizationCylinderComparison Δ[n] x).2.down) = realizationPrismHomeomorph n x := by
  apply Prod.ext
  · rfl
  · rfl

example (n : ℕ) : CompactSpace |(Δ[n] ⊗ Δ[1] : SSet.{u})| := inferInstance

example (n : SimplexCategory) : CompactSpace |SSet.stdSimplex.{u}.obj n| := inferInstance

example {n : ℕ} (i : Fin (n + 1)) : Continuous (realizationPrismLift.{u} i) :=
  (realizationPrismLift i).continuous
