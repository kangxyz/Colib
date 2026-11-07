/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SquareHomology
public import Colib.Topology.LocalCoefficients.RelativeHomology

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SquareRelative.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual coefficient maps.

 # The original coefficient morphism of a spatial square -/

@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y Z W : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace W]

/-- The square carries its canonical source and target pullback conversions. -/
def squareCoefficientMap (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, W)) (U : C(Z, W))
    (w : U.comp s = t.comp h) (A : System.{u, u} W) :
    pullback s (pullback U A) ⟶ pullback h (pullback t A) :=
  (pullbackCompositionIso s U A).inv ≫
    eqToHom (congrArg (fun k ↦ pullback k A) w) ≫ (pullbackCompositionIso h t A).hom

/-- The square homology map is the actual relative map of its canonical coefficient morphism. -/
theorem squareHomologyMap_eq_relative (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, W))
    (U : C(Z, W)) (w : U.comp s = t.comp h) (A : System.{u, u} W) (n : ℕ) :
    squareHomologyMap h s t U w A n =
      relativeHomologyMap h (squareCoefficientMap h s t U w A) n := by
  simp only [squareHomologyMap, triangleHomologyMap, relativeHomologyMap,
    squareCoefficientMap, coefficientHomologyMap_comp, Category.assoc]

end FundamentalGroupoid.LocalCoefficients
