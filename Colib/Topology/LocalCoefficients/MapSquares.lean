/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.MapComposition

/-!
Adapted from `Quillen/Topology/LocalCoefficients/MapSquares.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native Colib objects.

# Exact twisted chain squares of original commuting spatial maps

A strictly commuting spatial square induces its canonical coefficient pullback
isomorphism. The original spatial chain maps commute after that explicit
coefficient conversion, as a consequence of actual identity/composition laws.
-/

@[expose] public section
noncomputable section
open Topology CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y Z T : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]

/-- Coefficient composition on the actual chain complexes. -/
@[reassoc]
theorem coefficientChainMap_comp {A B C : System.{u, u} X} (η : A ⟶ B) (θ : B ⟶ C) :
    coefficientChainMap (η ≫ θ) = coefficientChainMap η ≫ coefficientChainMap θ := by
  simp only [coefficientChainMap, coefficientSimplicialMap_comp, Functor.map_comp]

/-- Coefficient identity on the actual chain complexes. -/
@[simp]
theorem coefficientChainMap_id (A : System.{u, u} X) :
    coefficientChainMap (𝟙 A) = 𝟙 (singularChainComplex A) := by
  simp only [coefficientChainMap, coefficientSimplicialMap_id, CategoryTheory.Functor.map_id,
    singularChainComplex]

/-- Strict equality of spatial maps gives the canonical pullback-system isomorphism. -/
def pullbackCongrIso {f g : C(X, Y)} (h : f = g) (A : System.{u, u} Y) :
    pullback f A ≅ pullback g A :=
  eqToIso (congrArg (fun k ↦ pullback k A) h)

/-- Original chain maps respect strict spatial equality with the actual coefficient conversion. -/
theorem pushforwardChainMap_congr {f g : C(X, Y)} (h : f = g) (A : System.{u, u} Y) :
    coefficientChainMap (pullbackCongrIso h A).hom ≫ pushforwardChainMap g A =
      pushforwardChainMap f A := by
  subst g
  change coefficientChainMap (𝟙 (pullback f A)) ≫ _ = _
  rw [coefficientChainMap_id, Category.id_comp]

/-- The explicit coefficient comparison around an original commuting spatial square. -/
def pullbackSquareIso (f : C(X, Y)) (g : C(Z, T)) (a : C(X, Z)) (b : C(Y, T))
    (w : b.comp f = g.comp a) (A : System.{u, u} T) :
    pullback f (pullback b A) ≅ pullback a (pullback g A) :=
  (pullbackCompositionIso f b A).symm ≪≫ pullbackCongrIso w A ≪≫
    pullbackCompositionIso a g A

/-- The exact square of original spatial chain maps, with its pullback coefficient isomorphism. -/
theorem pushforwardChainMap_square (f : C(X, Y)) (g : C(Z, T))
    (a : C(X, Z)) (b : C(Y, T)) (w : b.comp f = g.comp a) (A : System.{u, u} T) :
    coefficientChainMap (pullbackSquareIso f g a b w A).hom ≫
        pushforwardChainMap a (pullback g A) ≫ pushforwardChainMap g A =
      pushforwardChainMap f (pullback b A) ≫ pushforwardChainMap b A := by
  change coefficientChainMap
      ((pullbackCompositionIso f b A).inv ≫ ((pullbackCongrIso w A).hom ≫
        (pullbackCompositionIso a g A).hom)) ≫
      pushforwardChainMap a (pullback g A) ≫ pushforwardChainMap g A = _
  simp only [coefficientChainMap_comp, Category.assoc]
  rw [← pushforwardChainMap_comp, pushforwardChainMap_congr, pushforwardChainMap_comp]
  rw [← Category.assoc, ← coefficientChainMap_comp,
    Iso.inv_hom_id, coefficientChainMap_id, Category.id_comp]

end FundamentalGroupoid.LocalCoefficients
