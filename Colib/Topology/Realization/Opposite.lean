/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! Reversal of simplex coordinates and geometric realization of opposite
simplicial sets. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Opposite
open scoped Simplicial Topology
universe u
namespace SSet

/-- Reverse the barycentric coordinates of a topological simplex. -/
def simplexReverse (n : SimplexCategory) :
    SimplexCategory.toTop.obj n ⟶ SimplexCategory.toTop.obj n :=
  TopCat.ofHom ⟨fun x ↦ ULift.up (StdSimplex.map Fin.rev x.down),
    continuous_uliftUp.comp ((StdSimplex.continuous_map ℝ Fin.rev).comp continuous_uliftDown)⟩

theorem simplexReverse_involutive (n : SimplexCategory) :
    simplexReverse n ≫ simplexReverse n = 𝟙 _ := by
  ext x
  change ULift.up (StdSimplex.map Fin.rev (StdSimplex.map Fin.rev x.down)) = x
  have h : (Fin.rev ∘ Fin.rev : Fin (n.len + 1) → Fin (n.len + 1)) = id := by
    funext i; exact Fin.rev_rev i
  simp only [← StdSimplex.map_comp, h, StdSimplex.map_id]
  rfl

/-- Reversal conjugates every simplicial operator to its order reversal. -/
theorem simplexReverse_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    SimplexCategory.toTop.map (SimplexCategory.rev.map f) ≫ simplexReverse m =
      simplexReverse n ≫ SimplexCategory.toTop.map f := by
  ext x
  change ULift.up (StdSimplex.map Fin.rev
      (StdSimplex.map (SimplexCategory.rev.map f).toOrderHom x.down)) =
    ULift.up (StdSimplex.map f.toOrderHom (StdSimplex.map Fin.rev x.down))
  rw [← StdSimplex.map_comp, ← StdSimplex.map_comp]
  congr 2
  funext i
  simp [SimplexCategory.rev_map_apply]

/-- Reversal identifies the opposite singular simplicial set with the original. -/
def singularOppositeIso (X : TopCat.{u}) : (TopCat.toSSet.obj X).op ≅ TopCat.toSSet.obj X :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso {
    toFun := fun s ↦ ULift.up (simplexReverse n.unop ≫ s.down)
    invFun := fun s ↦ ULift.up (simplexReverse n.unop ≫ s.down)
    left_inv := fun s ↦ by
      change ULift.up (simplexReverse n.unop ≫ simplexReverse n.unop ≫ s.down) = s
      rw [← Category.assoc, simplexReverse_involutive, Category.id_comp]
      rfl
    right_inv := fun s ↦ by
      change ULift.up (simplexReverse n.unop ≫ simplexReverse n.unop ≫ s.down) = s
      rw [← Category.assoc, simplexReverse_involutive, Category.id_comp]
      rfl }) (by
    intro n m f
    ext s : 3
    change ULift.up (simplexReverse m.unop ≫
      SimplexCategory.toTop.map (SimplexCategory.rev.map f.unop) ≫ s.down) =
      ULift.up (SimplexCategory.toTop.map f.unop ≫ simplexReverse n.unop ≫ s.down)
    rw [← Category.assoc, ← Category.assoc]
    congr 2
    simpa using (simplexReverse_naturality (SimplexCategory.rev.map f.unop)).symm)

/-- Singular coordinate reversal is natural in the topological space. -/
def singularOppositeNatIso : TopCat.toSSet ⋙ SSet.opFunctor ≅ TopCat.toSSet :=
  NatIso.ofComponents singularOppositeIso (by
    intro X Y f
    ext n s : 4
    change ULift.up (simplexReverse n.unop ≫ s.down ≫ f) =
      ULift.up ((simplexReverse n.unop ≫ s.down) ≫ f)
    rw [Category.assoc])

/-- Opposite simplicial sets have naturally homeomorphic geometric realizations.
This follows from actual barycentric reversal on singular simplices and
uniqueness of the left adjoint to the singular functor. -/
def realizationOppositeNatIso : SSet.opFunctor ⋙ SSet.toTop ≅ SSet.toTop :=
  ((SSet.opEquivalence.toAdjunction.comp sSetTopAdj).ofNatIsoRight
    singularOppositeNatIso).leftAdjointUniq sSetTopAdj

/-- The canonical topological homeomorphism reversing simplex coordinates. -/
def realizationOppositeHomeomorph (X : SSet.{u}) : |X.op| ≃ₜ |X| :=
  TopCat.homeoOfIso (realizationOppositeNatIso.app X)

/-- The opposite comparison intertwines the realizations of every simplicial map. -/
theorem realizationOpposite_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map (SSet.opFunctor.map f) ≫ (realizationOppositeNatIso.app Y).hom =
      (realizationOppositeNatIso.app X).hom ≫ SSet.toTop.map f :=
  realizationOppositeNatIso.hom.naturality f

end SSet
