/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.ConstantIso

/-! The discrete comparison retains its actual coproduct construction,
vertex formula, and naturality without a nonempty assumption. -/

@[expose] public noncomputable section

open CategoryTheory Opposite SSet
open scoped Simplicial

universe u

example (A : Type u) :
    constantRealizationIso A =
      (SSet.toTop.mapIso (pointSigmaIso A)).symm ≪≫
        realizationSigmaIso (fun _ : A ↦ (Δ[0] : SSet.{u})) ≪≫
          TopCat.isoOfHomeo (TopCat.sigmaPointHomeomorph A) := rfl

example (A : Type u) (a : A) :
    (constantRealizationIso A).hom
      (realizationPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj A) a) = a :=
  constantRealizationIso_point A a

example {A B : Type u} (f : A ⟶ B) :
    SSet.toTop.map ((Functor.const SimplexCategoryᵒᵖ).map f) ≫ (constantRealizationIso B).hom =
      (constantRealizationIso A).hom ≫ TopCat.discrete.map f :=
  constantRealizationIso_naturality f

example :
    SSet.toTop.obj ((Functor.const SimplexCategoryᵒᵖ).obj PEmpty.{u + 1}) ≅
      TopCat.discrete.obj PEmpty.{u + 1} :=
  constantRealizationIso _

open CategoryTheory.Limits
open scoped Topology

example {ι : Type u} (X : ι → SSet.{u}) (i : ι) (p : SimplexCategoryᵒᵖ)
    (x : (X i).obj p) : (simplicialSigmaι X i).app p x = ⟨i, x⟩ := rfl

example {ι : Type u} (X : ι → SSet.{u}) :
    IsColimit (Cofan.mk (simplicialSigma X) (simplicialSigmaι X)) :=
  simplicialSigmaIsColimit X

example {ι : Type u} (X : ι → SSet.{u}) (i : ι) :
    SSet.toTop.map (simplicialSigmaι X i) ≫ (realizationSigmaIso X).hom =
      TopCat.sigmaι (fun i ↦ SSet.toTop.obj (X i)) i := realizationSigmaIso_ι X i

example (A : Type u) (a : A) :
    (TopCat.sigmaPointHomeomorph A).symm a = ⟨a, default⟩ := rfl

example (A : Type u) :
    (constantRealizationIso A).hom ≫ (constantRealizationIso A).inv = 𝟙 _ :=
  (constantRealizationIso A).hom_inv_id

example (X : PEmpty.{u + 1} → SSet.{u}) :
    SSet.toTop.obj (simplicialSigma X) ≅ TopCat.of (Σ i, |X i|) := realizationSigmaIso X
