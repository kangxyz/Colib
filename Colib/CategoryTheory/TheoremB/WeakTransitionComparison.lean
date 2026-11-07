/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.WeakVertexComparison
public import Colib.CategoryTheory.TheoremB.StructuredWeakTransport

/-! # Canonical Theorem B comparisons under weak transition equivalences

Implementation source: `Quillen/CategoryTheory/TheoremB/WeakTransitionComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original transition maps, all
homotopy degrees and identity-arrow basepoints are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open Topology CategoryTheory Opposite
open scoped Simplicial Topology
namespace CategoryTheory.TheoremB
open TheoremA
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- Weakness of each prescribed costructured transition; no inverse is selected. -/
def TransitionWeakEquivalences : Prop :=
  ∀ ⦃d e : D⦄ (f : d ⟶ e), IsWeakHomotopyEquivalence (transitionMap F f)

/-- Weakness of each prescribed structured transition. -/
def StructuredTransitionWeakEquivalences : Prop :=
  ∀ ⦃d e : D⦄ (f : d ⟶ e), IsWeakHomotopyEquivalence (structuredTransitionMap F f)

/-- Weak transitions suffice for all homotopy groups of the original comma comparison. -/
theorem fiberComparison_bijective_of_weakTransitions (h : TransitionWeakEquivalences F)
    (c : C) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (fiberComparison F (F.obj c)) (fiberComparison_identity F c)) := by
  apply fiberComparison_bijective_of_replacement F c n
  exact (vertexFiberComparison_isWeakHomotopyEquivalence_of_weakCartesian (commaNerveDiagram F)
    (replacementPointAugmentation_transitionWeakCartesian (commaNerveDiagram F)
      (fun {_ _} f => h f)) (F.obj c)).homotopy_bijective _ n

/-- Opposite comma transport preserves actual weak transition maps. -/
theorem transitionWeakEquivalences_op_of_structured
    (h : StructuredTransitionWeakEquivalences F) : TransitionWeakEquivalences F.op := by
  intro d e f
  have hs := isWeakHomotopyEquivalence_of_homotopyEquiv
    (structuredCommaOppositeEquiv F d.unop)
  have ht := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (structuredCommaOppositeEquiv F e.unop)).comp (h f.unop)
  rw [← structuredCommaOppositeEquiv_transition] at ht
  exact ht.of_comp_left hs

/-- The original structured comparison is bijective in every homotopy degree
under weak structured transitions alone. -/
theorem structuredFiberComparison_bijective_of_weakTransitions
    (h : StructuredTransitionWeakEquivalences F) (c : C) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (structuredFiberComparison F (F.obj c)) (structuredFiberComparison_identity F c)) :=
  structuredFiberComparison_bijective_of_opposite F c n
    (fiberComparison_bijective_of_weakTransitions F.op
      (transitionWeakEquivalences_op_of_structured F h) (op c) n)

/-- The positive-degree group isomorphism of Theorem B has precisely the
canonical comma-to-fiber map as its forward group homomorphism. -/
def fiberComparisonPiEquivOfWeakTransitions (h : TransitionWeakEquivalences F) (c : C) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (ClassifyingSpace (CostructuredArrow F (F.obj c)))
      (classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) ≃*
    HomotopyGroup.Pi (n + 1)
      (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c)))
      (HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c)) :=
  MulEquiv.ofBijective
    (HomotopyGroup.piMap n (fiberComparison F (F.obj c)) (fiberComparison_identity F c))
    (fiberComparison_bijective_of_weakTransitions F h c (n + 1))

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem fiberComparisonPiEquivOfWeakTransitions_coe
    (h : TransitionWeakEquivalences F) (c : C) (n : ℕ) :
    ↑(fiberComparisonPiEquivOfWeakTransitions F h c n) =
      HomotopyGroup.piMap n (fiberComparison F (F.obj c)) (fiberComparison_identity F c) := rfl


/-- The structured comparison induces its canonical positive-degree group
isomorphism; no separately chosen unbased equivalence is substituted. -/
def structuredFiberComparisonPiEquivOfWeakTransitions
    (h : StructuredTransitionWeakEquivalences F) (c : C) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (ClassifyingSpace (StructuredArrow (F.obj c) F))
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) ≃*
    HomotopyGroup.Pi (n + 1)
      (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c)))
      (HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c)) :=
  MulEquiv.ofBijective
    (HomotopyGroup.piMap n (structuredFiberComparison F (F.obj c))
      (structuredFiberComparison_identity F c))
    (structuredFiberComparison_bijective_of_weakTransitions F h c (n + 1))

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem structuredFiberComparisonPiEquivOfWeakTransitions_coe
    (h : StructuredTransitionWeakEquivalences F) (c : C) (n : ℕ) :
    ↑(structuredFiberComparisonPiEquivOfWeakTransitions F h c n) =
      HomotopyGroup.piMap n (structuredFiberComparison F (F.obj c))
        (structuredFiberComparison_identity F c)
        := rfl


end CategoryTheory.TheoremB
