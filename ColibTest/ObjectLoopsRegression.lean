/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.GrothendieckComparison.ObjectLoops

/-!
# Object-loop comparison regression tests

These test actual maps and the canonical-generator subgroup, not surjectivity
onto all of K₀ or commutativity of that whole group.
-/

@[expose] public noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Topology

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

example (X : C) : E.kZeroObjectLoop X =
    (classifyingSpacePath
      (E.fromZeroTotal (CategoryTheory.QConstruction.of E.deflation E.inflation X))).trans
      (classifyingSpacePath
        (E.fromZero (CategoryTheory.QConstruction.of E.deflation E.inflation X))).symm := rfl

example (X : C) : E.kZeroFundamentalGroupEquiv (E.kZeroObjectClass X) =
    (⟦E.kZeroObjectLoop X⟧ : FundamentalGroup E.KSpace E.kBasepoint) :=
  E.kZeroFundamentalGroupEquiv_objectClass X

example (X : C) : E.grothendieckToKZero
    (Multiplicative.ofAdd (E.grothendieckClass X)) = E.kZeroObjectClass X :=
  E.grothendieckToKZero_class X

example : E.grothendieckToKZero.range = E.kZeroObjectSubgroup :=
  E.grothendieckToKZero_range

example : CommGroup E.kZeroObjectSubgroup := inferInstance
example : Group (E.K 0) := inferInstance

example {S : ShortComplex C} (hS : E.conflation S) :
    E.kZeroObjectClass S.X₂ = E.kZeroObjectClass S.X₁ * E.kZeroObjectClass S.X₃ :=
  E.kZeroObjectClass_conflation hS

example : E.kZeroObjectClass (0 : C) = 1 := E.kZeroObjectClass_zero

end CategoryTheory.ExactCategory.ExactStructure

example {C : Type u} [Category.{v} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    ((classifyingSpacePath f).trans (classifyingSpacePath g)).Homotopic
      (classifyingSpacePath (f ≫ g)) := classifyingSpacePath_comp f g

example {C : Type u} [Category.{v} C] {x y : C} (f : x ⟶ y) :
    (classifyingFundamentalGroupoidFunctor C).map f = ⟦classifyingSpacePath f⟧ := rfl


open scoped Simplicial unitInterval
open SSet

example {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) (t : unitInterval) :
    realizationEdgePath e t =
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) (realizationInterval t) := rfl

example {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    realizationEdgePath e 0 = realizationPoint x := (realizationEdgePath e).source

example {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    realizationEdgePath e 1 = realizationPoint y := (realizationEdgePath e).target

example {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (s : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    ((realizationEdgePath e₀₁).trans (realizationEdgePath e₁₂)).Homotopic
      (realizationEdgePath e₀₂) := realizationEdgePath_comp s

example : SSet.yonedaEquiv.symm (simplexEdge.{u} 2 0 1 (by decide)).edge =
    SSet.stdSimplex.δ 2 := simplexEdge_01_yoneda

example : SSet.yonedaEquiv.symm (simplexEdge.{u} 2 1 2 (by decide)).edge =
    SSet.stdSimplex.δ 0 := simplexEdge_12_yoneda

example : SSet.yonedaEquiv.symm (simplexEdge.{u} 2 0 2 (by decide)).edge =
    SSet.stdSimplex.δ 1 := simplexEdge_02_yoneda

example {M : Type u} [Finite M] {x y : Convexity.StdSimplex ℝ M} (p q : Path x y) :
    p.Homotopy q := Convexity.StdSimplex.pathHomotopy p q

example {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {c d : C} (f : c ⟶ d) (t : unitInterval) :
    classifyingSpaceMap F (classifyingSpacePath f t) = classifyingSpacePath (F.map f) t :=
  classifyingSpacePath_naturality F f t

example {C : Type u} [Category.{v} C] (c : C) :
    (classifyingFundamentalGroupoidFunctor C).obj c =
      FundamentalGroupoid.mk (classifyingSpacePoint c) := rfl

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

example : E.kZeroFundamentalGroupEquiv = HomotopyGroup.pi1MulEquivFundamentalGroup := rfl

example (X : C) :
    (⟦E.kZeroObjectLoop X⟧ : FundamentalGroup E.KSpace E.kBasepoint) =
      E.qObjectClass (classifyingFundamentalGroupoidFunctor E.QCategory) X :=
  E.kZeroObjectLoop_eq_qObjectClass X

example (X Y : C) : Commute (E.kZeroObjectClass X) (E.kZeroObjectClass Y) :=
  E.kZeroObjectClass_commute X Y

example : E.kZeroObjectSubgroup = Subgroup.closure (Set.range E.kZeroObjectClass) := rfl

example : E.grothendieckToKZero =
    E.kZeroObjectSubgroup.subtype.comp E.grothendieckToKZeroSubgroup := rfl

example (X : C) : E.grothendieckToKZeroSubgroup
    (Multiplicative.ofAdd (E.grothendieckClass X)) = E.kZeroObjectClassInSubgroup X :=
  E.grothendieckToKZeroSubgroup_class X

example {X Y : C} (e : X ≅ Y) : E.kZeroObjectClass X = E.kZeroObjectClass Y :=
  E.kZeroObjectClass_iso e

end CategoryTheory.ExactCategory.ExactStructure
