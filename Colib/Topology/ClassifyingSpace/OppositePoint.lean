/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.Opposite
public import Colib.Topology.ClassifyingSpace.Constant

/-! The natural opposite-realization homeomorphism preserves each object
vertex, as follows immediately by naturality for the constant endofunctor. -/
/-! Implementation source: `Quillen/Topology/ClassifyingSpace/OppositePoint.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, paths and identity
basepoints are retained under native namespace and dependency ownership. -/
@[expose] public section

noncomputable section
open SSet TopCat Topology CategoryTheory Opposite
universe u
namespace CategoryTheory
variable {C : Type u} [SmallCategory C]

private theorem point_of_const_square {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : TopCat.const x ≫ f = f ≫ TopCat.const y) : f x = y :=
  ConcreteCategory.congr_hom h x

@[simp] theorem classifyingOppositeIso_point (c : C) :
    (classifyingOppositeIso C).hom (classifyingSpacePoint (op c)) = classifyingSpacePoint c := by
  let F : C ⥤ C := (Functor.const C).obj c
  have hf : F.op = (Functor.const Cᵒᵖ).obj (op c) := rfl
  have h₁ : classifyingSpaceMap F.op =
      TopCat.const (X := ClassifyingSpace Cᵒᵖ) (classifyingSpacePoint (op c)) :=
    (congrArg classifyingSpaceMap hf).trans (classifyingSpaceMap_const_direct (op c))
  have h₂ : classifyingSpaceMap F =
      TopCat.const (X := ClassifyingSpace C) (classifyingSpacePoint c) :=
    classifyingSpaceMap_const_direct c
  have h := classifyingOppositeIso_naturality F
  have hc : TopCat.const (classifyingSpacePoint (op c)) ≫ (classifyingOppositeIso C).hom =
      (classifyingOppositeIso C).hom ≫ TopCat.const (classifyingSpacePoint c) :=
    (congrArg (fun k ↦ k ≫ (classifyingOppositeIso C).hom) h₁.symm).trans
      (h.trans (congrArg (fun k ↦ (classifyingOppositeIso C).hom ≫ k) h₂))
  exact point_of_const_square (classifyingOppositeIso C).hom _ _ hc

end CategoryTheory
