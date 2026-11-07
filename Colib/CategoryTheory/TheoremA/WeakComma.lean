/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.DiscreteWeakEquivalence
public import Colib.CategoryTheory.TheoremB.WeakVertexComparison
public import Colib.CategoryTheory.TheoremA.ContractibleComma
public import Colib.Topology.Realization.FiniteNullhomotopy

/-!
# Quillen Theorem A from weakly contractible comma nerves

Weakly contractible coefficients make the original simplicial replacement
augmentation weak. The genuine diagonal source equivalence and augmentation
homotopy then prove complete weakness of the original classifying-space map.
A finite-subcomplex nullhomotopy criterion requires no global contraction.

Implementation provenance:
`Quillen/CategoryTheory/TheoremA/WeakComma.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology Simplicial unitInterval
universe u v w
namespace CategoryTheory

namespace TheoremB
open TheoremA CategoryTheory.TheoremB.Skeletal Topology.HomotopyPullback.Sequential
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- Weakly contractible realized coefficients make the original replacement
augmentation a complete weak equivalence, with no global inverse chosen. -/
theorem replacementBaseMap_isWeakHomotopyEquivalence
    (h : ∀ d : D, IsWeakHomotopyEquivalence
      (ContinuousMap.const |H.obj d| (PUnit.unit : PUnit.{u + 1}))) :
    IsWeakHomotopyEquivalence (SSet.toTop.map (replacementBaseMap H)).hom := by
  have htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      IsWeakHomotopyEquivalence (SSet.toTop.map (H.map f)).hom := by
    intro d e f
    have hc : IsWeakHomotopyEquivalence
        ((ContinuousMap.const |H.obj e| (PUnit.unit : PUnit.{u + 1})).comp
          (SSet.toTop.map (H.map f)).hom) := h d
    exact hc.of_comp_right (h e)
  apply isWeakHomotopyEquivalence_of_classifying_vertex_fibers
  intro d
  have hv := vertexFiberComparison_isWeakHomotopyEquivalence_of_weakCartesian H
    (replacementPointAugmentation_transitionWeakCartesian H htrans) d
  exact IsWeakHomotopyEquivalence.of_comp_left
    (f := vertexFiberComparison H d)
    (g := ContinuousMap.const _ (PUnit.unit : PUnit.{u + 1})) (h d) hv

end TheoremB

namespace TheoremA

/-- Weak Quillen Theorem A for the original functor and original classifying
map: each actual comma nerve need only be weakly contractible. -/
theorem classifyingSpaceMap_isWeakHomotopyEquivalence_of_weak_comma
    {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)
    (h : ∀ d : D, IsWeakHomotopyEquivalence
      (ContinuousMap.const (ClassifyingSpace (CostructuredArrow F d))
        (PUnit.unit : PUnit.{u + 1}))) :
    IsWeakHomotopyEquivalence (classifyingSpaceMap F).hom := by
  have hb := TheoremB.replacementBaseMap_isWeakHomotopyEquivalence
    (commaNerveDiagram F) h
  have hc := hb.of_homotopy (diagonalAugmentationHomotopy F).symm
  have hs : IsWeakHomotopyEquivalence (SSet.toTop.map (diagonalSourceMap F)).hom := by
    rw [← diagonalSourceHomotopyEquiv_toFun]
    exact isWeakHomotopyEquivalence_of_homotopyEquiv (diagonalSourceHomotopyEquiv F)
  exact hc.of_comp_left hs

/-- It is enough to nullhomotope each finite subcomplex inclusion inside its
original comma realization. This includes the empty-subcomplex test. -/
theorem classifyingSpaceMap_isWeakHomotopyEquivalence_of_finite_comma_nullhomotopic
    {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)
    (h : ∀ d : D, ∀ A : (nerve (CostructuredArrow F d)).Subcomplex,
      SSet.Finite A → (SSet.toTop.map A.ι).hom.Nullhomotopic) :
    IsWeakHomotopyEquivalence (classifyingSpaceMap F).hom :=
  classifyingSpaceMap_isWeakHomotopyEquivalence_of_weak_comma F
    (fun d => realization_toPoint_isWeakHomotopyEquivalence_of_finite_nullhomotopic (h d))

end TheoremA
end CategoryTheory
