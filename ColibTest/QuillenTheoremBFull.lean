module

public import Colib.CategoryTheory.TheoremB.WeakComparison
public import Colib.CategoryTheory.TheoremB.StructuredWeakComparison
public import Colib.CategoryTheory.TheoremB.FullWeakComparison
public import Colib.CategoryTheory.TheoremB.StructuredFullWeakComparison

@[expose] public noncomputable section
universe u v
open CategoryTheory CategoryTheory.TheoremB Topology
open scoped Topology

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

example (h : TransitionHomotopyEquivalences F) (d : D)
    (y : HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :
    ∃ x, Joined (fiberComparison F d x) y :=
  (fiberComparison_isWeakHomotopyEquivalence F h d).component_surjective y

example (h : StructuredTransitionHomotopyEquivalences F) (d : D)
    (y : HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :
    ∃ x, Joined (structuredFiberComparison F d x) y :=
  (structuredFiberComparison_isWeakHomotopyEquivalence F h d).component_surjective y

example (h : TransitionHomotopyEquivalences F) (d : D)
    (x : ClassifyingSpace (CostructuredArrow F d)) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (fiberComparison F d) (x := x) rfl) :=
  (fiberComparison_isWeakHomotopyEquivalence F h d).homotopy_bijective x n

example (h : StructuredTransitionHomotopyEquivalences F) (d : D)
    (x : ClassifyingSpace (StructuredArrow d F)) (n : ℕ) :
    Function.Bijective
      (HomotopyGroup.map (N := Fin n) (structuredFiberComparison F d) (x := x) rfl) :=
  (structuredFiberComparison_isWeakHomotopyEquivalence F h d).homotopy_bijective x n

example (h : TransitionHomotopyEquivalences F) (d : D)
    (x : ClassifyingSpace (CostructuredArrow F d)) :
    Function.Bijective (HomotopyGroup.map (N := Fin 0) (fiberComparison F d) (x := x) rfl) :=
  (fiberComparison_isWeakHomotopyEquivalence F h d).homotopy_bijective x 0

example (h : StructuredTransitionHomotopyEquivalences F) (d : D)
    (x : ClassifyingSpace (StructuredArrow d F)) :
    Function.Bijective
      (HomotopyGroup.map (N := Fin 0) (structuredFiberComparison F d) (x := x) rfl) :=
  (structuredFiberComparison_isWeakHomotopyEquivalence F h d).homotopy_bijective x 0

example (h : TransitionHomotopyEquivalences F) (d : D)
    [IsEmpty (ClassifyingSpace (CostructuredArrow F d))] :
    IsEmpty (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  (fiberComparison_isWeakHomotopyEquivalence F h d).isEmpty_target

example (h : StructuredTransitionHomotopyEquivalences F) (d : D)
    [IsEmpty (ClassifyingSpace (StructuredArrow d F))] :
    IsEmpty (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  (structuredFiberComparison_isWeakHomotopyEquivalence F h d).isEmpty_target

example (h : TransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (fiberComparison F (F.obj c))
      (fiberComparison_identity F c)) := fiberComparison_bijective F h c n

example (h : StructuredTransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (structuredFiberComparison F (F.obj c))
      (structuredFiberComparison_identity F c)) := structuredFiberComparison_bijective F h c n

example (h : TransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    ↑(fiberComparisonPiEquiv F h c n) =
      HomotopyGroup.piMap n (fiberComparison F (F.obj c)) (fiberComparison_identity F c) := rfl

example (h : StructuredTransitionHomotopyEquivalences F) (c : C) (n : ℕ) :
    ↑(structuredFiberComparisonPiEquiv F h c n) =
      HomotopyGroup.piMap n (structuredFiberComparison F (F.obj c))
        (structuredFiberComparison_identity F c) := rfl

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (hf : IsWeakHomotopyEquivalence f) (H : f.Homotopy g) :
    IsWeakHomotopyEquivalence g := hf.of_homotopy H

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X)
    (hf : Function.Bijective (HomotopyGroup.map (N := Fin 0) f (x := x) rfl)) :
    Function.Bijective (HomotopyGroup.map (N := Fin 0) g (x := x) rfl) :=
  homotopyGroupMap_bijective_of_homotopy H x 0 hf
