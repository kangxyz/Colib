/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.NerveHomotopy
public import Colib.Topology.Realization.Opposite

/-! Opposite-chain presentation of the source columns. -/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

private theorem chainMap_heq {n : ℕ} (c : ComposableArrows C n)
    {i j i' j' : Fin (n + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : c.map f ≍ c.map g := by
  subst i'; subst j'
  exact heq_of_eq (congrArg c.map (Subsingleton.elim f g))

private theorem chainMap_op_heq {n : ℕ} (c : ComposableArrows C n)
    {i j i' j' : Fin (n + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : (c.map f).op ≍ (c.map g).op := by
  subst i'; subst j'
  exact heq_of_eq (congrArg (fun f ↦ (c.map f).op) (Subsingleton.elim f g))

/-- Reverse a chain while passing to the opposite category. -/
def reverseChain {n : ℕ} (c : ComposableArrows C n) : ComposableArrows Cᵒᵖ n where
  obj i := op (c.obj i.rev)
  map {i j} f := (c.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom f)))).op
  map_id i := by simp
  map_comp f g := by
    change (c.map _).op = (c.map _ ≫ c.map _).op
    rw [← c.map_comp]
    rfl

/-- Read a reversed opposite chain in its original direction. -/
def unreverseChain {n : ℕ} (c : ComposableArrows Cᵒᵖ n) : ComposableArrows C n where
  obj i := (c.obj i.rev).unop
  map {i j} f := (c.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom f)))).unop
  map_id i := by simp
  map_comp f g := by
    change (c.map _).unop = (c.map _ ≫ c.map _).unop
    rw [← c.map_comp]
    rfl

@[simp] theorem unreverse_reverseChain {n : ℕ} (c : ComposableArrows C n) :
    unreverseChain (reverseChain c) = c := by
  refine CategoryTheory.Functor.hext (fun i ↦ by simp [reverseChain, unreverseChain]) ?_
  intro i j f
  exact chainMap_heq c (Fin.rev_rev i) (Fin.rev_rev j) _ _

@[simp] theorem reverse_unreverseChain {n : ℕ} (c : ComposableArrows Cᵒᵖ n) :
    reverseChain (unreverseChain c) = c := by
  refine CategoryTheory.Functor.hext (fun i ↦ by simp [reverseChain, unreverseChain]) ?_
  intro i j f
  exact chainMap_heq c (Fin.rev_rev i) (Fin.rev_rev j) _ _

/-- Reversal is a bijection on chains, including their actual objects and arrows. -/
def reverseChainEquiv (n : ℕ) : ComposableArrows C n ≃ ComposableArrows Cᵒᵖ n where
  toFun := reverseChain
  invFun := unreverseChain
  left_inv := unreverse_reverseChain
  right_inv := reverse_unreverseChain

/-- Reversal intertwines the two simplicial operators. -/
theorem reverseChain_naturality {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q)
    (c : (nerve C).obj p) :
    reverseChain ((nerve C).map (SimplexCategory.rev.map α.unop).op c) =
      (nerve Cᵒᵖ).map α (reverseChain c) := by
  refine CategoryTheory.Functor.hext (fun i ↦ ?_) ?_
  · change op (c.obj (α.unop.toOrderHom i.rev.rev).rev) =
      op (c.obj (α.unop.toOrderHom i).rev)
    simp
  · intro i j f
    change (c.map (homOfLE (show (α.unop.toOrderHom j.rev.rev).rev ≤
      (α.unop.toOrderHom i.rev.rev).rev from by
        simpa using Fin.rev_le_rev.mpr (α.unop.toOrderHom.monotone (leOfHom f))))).op ≍
        (c.map (homOfLE (show (α.unop.toOrderHom j).rev ≤
          (α.unop.toOrderHom i).rev from
            Fin.rev_le_rev.mpr (α.unop.toOrderHom.monotone (leOfHom f))))).op
    exact chainMap_op_heq c (by simp) (by simp) _ _

/-- The nerve of the opposite category is the reversed nerve. -/
def nerveOppositeIso : (nerve C).op ≅ nerve Cᵒᵖ :=
  NatIso.ofComponents (fun p ↦ (reverseChainEquiv p.unop.len).toIso) (by
    intro p q α
    ext c : 3
    exact reverseChain_naturality α c)

end CategoryTheory
