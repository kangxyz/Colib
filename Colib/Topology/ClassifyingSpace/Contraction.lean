/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.HomotopyBridge
public import Colib.Topology.ClassifyingSpace.Map
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # Classifying-space contractions from initial and terminal objects

Selected from `Quillen/Topology/ClassifyingSpace/Equivalence.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No homotopy-group map theory or
adjunction equivalence is needed for these explicit contractions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial Topology
universe u v
namespace CategoryTheory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- A constant functor induces the actual constant continuous map at its
object vertex. -/
theorem classifyingSpaceMap_const (d : D) :
    (classifyingSpaceMap ((Functor.const C).obj d)).hom =
      ContinuousMap.const (ClassifyingSpace C) (classifyingSpacePoint d) := by
  have h : SSet.stdSimplex.isTerminalObj₀.from (nerve C) ≫ nerveVertexMap d =
      nerveMap ((Functor.const C).obj d) := by
    ext n s
    rfl
  ext x
  unfold classifyingSpaceMap
  rw [← h, Functor.map_comp]
  change SSet.toTop.map (nerveVertexMap d)
    (SSet.toTop.map (SSet.stdSimplex.isTerminalObj₀.from (nerve C)) x) = _
  rw [Subsingleton.elim
    (SSet.toTop.map (SSet.stdSimplex.isTerminalObj₀.from (nerve C)) x) default]
  rfl

/-- An initial object contracts the classifying space to its vertex. -/
def classifyingSpaceInitialContraction {c : C} (hc : IsInitial c) :
    (ContinuousMap.const (ClassifyingSpace C) (classifyingSpacePoint c)).Homotopy
      (ContinuousMap.id (ClassifyingSpace C)) := by
  let α : (Functor.const C).obj c ⟶ 𝟭 C :=
    { app := fun d ↦ hc.to d
      naturality := fun _ _ _ ↦ hc.hom_ext _ _ }
  simpa only [classifyingSpaceMap_const, classifyingSpaceMap_id, TopCat.hom_id]
    using classifyingSpaceNaturalTransformationHomotopy α

/-- A terminal object contracts the classifying space to its vertex. -/
def classifyingSpaceTerminalContraction {c : C} (hc : IsTerminal c) :
    (ContinuousMap.id (ClassifyingSpace C)).Homotopy
      (ContinuousMap.const (ClassifyingSpace C) (classifyingSpacePoint c)) := by
  let α : 𝟭 C ⟶ (Functor.const C).obj c :=
    { app := fun d ↦ hc.from d
      naturality := fun _ _ _ ↦ hc.hom_ext _ _ }
  simpa only [classifyingSpaceMap_const, classifyingSpaceMap_id, TopCat.hom_id]
    using classifyingSpaceNaturalTransformationHomotopy α

/-- The actual classifying space of a category with an initial object is contractible. -/
theorem classifyingSpace_contractible_of_isInitial {c : C} (hc : IsInitial c) :
    ContractibleSpace (ClassifyingSpace C) :=
  (contractible_iff_id_nullhomotopic _).2
    ⟨classifyingSpacePoint c, ⟨(classifyingSpaceInitialContraction hc).symm⟩⟩

/-- The actual classifying space of a category with a terminal object is contractible. -/
theorem classifyingSpace_contractible_of_isTerminal {c : C} (hc : IsTerminal c) :
    ContractibleSpace (ClassifyingSpace C) :=
  (contractible_iff_id_nullhomotopic _).2
    ⟨classifyingSpacePoint c, ⟨classifyingSpaceTerminalContraction hc⟩⟩

instance classifyingSpace_contractible_of_hasInitial [HasInitial C] :
    ContractibleSpace (ClassifyingSpace C) :=
  classifyingSpace_contractible_of_isInitial initialIsInitial

instance classifyingSpace_contractible_of_hasTerminal [HasTerminal C] :
    ContractibleSpace (ClassifyingSpace C) :=
  classifyingSpace_contractible_of_isTerminal terminalIsTerminal

end CategoryTheory
