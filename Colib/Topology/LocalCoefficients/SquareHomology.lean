/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.TrianglePullback

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SquareHomology.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual coefficient maps.

 # Actual local-homology naturality of strictly commuting spatial squares -/

@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z W : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace W]

/-- The original upper map of a square, with the precise total-map pullback conversion. -/
def squareHomologyMap (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, W)) (U : C(Z, W))
    (w : U.comp s = t.comp h) (A : System.{u, u} W) (n : ℕ) :
    homology (pullback s (pullback U A)) n ⟶ homology (pullback t A) n :=
  coefficientHomologyMap (pullbackCompositionIso s U A).inv n ≫
    triangleHomologyMap h (U.comp s) t w A n

/-- The square's finite map followed by its target leg is exactly its source
leg followed by the specified total map. -/
@[reassoc]
theorem squareHomologyMap_to_target (h : C(X, Y)) (s : C(X, Z)) (t : C(Y, W))
    (U : C(Z, W)) (w : U.comp s = t.comp h) (A : System.{u, u} W) (n : ℕ) :
    squareHomologyMap h s t U w A n ≫ pushforwardHomologyMap t A n =
      pushforwardHomologyMap s (pullback U A) n ≫ pushforwardHomologyMap U A n := by
  rw [squareHomologyMap, Category.assoc, triangleHomologyMap_to_target,
    pushforwardHomologyMap_comp, ← Category.assoc, ← Category.assoc,
    ← coefficientHomologyMap_comp, Iso.inv_hom_id,
    coefficientHomologyMap_id, Category.id_comp]

/-- The triangle map does not depend on a presentation of its actual spatial arrow. -/
theorem triangleHomologyMap_congr {h h' : C(X, Y)} (hh : h = h')
    (s : C(X, Z)) (t : C(Y, Z)) (w : s = t.comp h) (w' : s = t.comp h')
    (A : System.{u, u} Z) (n : ℕ) :
    triangleHomologyMap h s t w A n = triangleHomologyMap h' s t w' A n := by
  subst h'
  rfl

/-- A genuine commuting diagram of squares commutes on actual local homology.
Both source and target coefficient pullbacks retain their canonical conversions. -/
@[reassoc]
theorem squareHomologyMap_naturality
    {X' Y' : Type u} [TopologicalSpace X'] [TopologicalSpace Y']
    (j : C(X, X')) (k : C(Y, Y')) (h : C(X, Y)) (h' : C(X', Y'))
    (s : C(X, Z)) (s' : C(X', Z)) (t : C(Y, W)) (t' : C(Y', W)) (U : C(Z, W))
    (ws : s = s'.comp j) (wt : t = t'.comp k)
    (wh : U.comp s = t.comp h) (wh' : U.comp s' = t'.comp h')
    (hh : k.comp h = h'.comp j) (A : System.{u, u} W) (n : ℕ) :
    squareHomologyMap h s t U wh A n ≫ triangleHomologyMap k t t' wt A n =
      triangleHomologyMap j s s' ws (pullback U A) n ≫
        squareHomologyMap h' s' t' U wh' A n := by
  have wj : U.comp s = (U.comp s').comp j := by rw [ws]; rfl
  have wa : U.comp s = t'.comp (k.comp h) := by rw [wh, wt]; rfl
  have wb : U.comp s = t'.comp (h'.comp j) := by rw [wj, wh']; rfl
  unfold squareHomologyMap
  rw [Category.assoc, triangleHomologyMap_comp h k (U.comp s) t t' wh wt wa]
  rw [← Category.assoc, triangleHomologyMap_pullback j s s' ws U A wj n,
    Category.assoc, triangleHomologyMap_comp j h' (U.comp s) (U.comp s') t' wj wh' wb]
  congr 1
  exact triangleHomologyMap_congr hh _ _ _ _ A n

end FundamentalGroupoid.LocalCoefficients
