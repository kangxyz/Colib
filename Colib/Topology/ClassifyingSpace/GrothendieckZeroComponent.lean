/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.GrothendieckComponentCofinality
public import Colib.Topology.ClassifyingSpace.ConnectedComponents
public import Colib.CategoryTheory.TheoremA.ContractibleStructured

/-!
Adapted from `Quillen/Topology/ClassifyingSpace/GrothendieckZeroComponent.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual objects,
functors, coefficient universes and comparison maps.

# Original fully faithful free-stage models of telescope zero components -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace CategoryTheory.Grothendieck
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (F : ℕ ⥤ Cat.{u, u}) [∀ n, IsGroupoid (F.obj n)]
  {D : Type u} [Category.{u} D] [IsPreconnected D]
  (G : D ⥤ Grothendieck F) [G.Full] [G.Faithful]
  (S : ℕ ⥤ D) (hS : ∀ n, (G.obj (S.obj n)).base = n)

/-- The original functor restricted to its actual categorical zero component. -/
def componentLift : D ⥤
    (CategoryTheory.ConnectedComponents.mk (G.obj (S.obj 0))).Component :=
  (CategoryTheory.ConnectedComponents.mk (G.obj (S.obj 0))).objectProperty.lift G
    (fun d ↦ Quotient.sound' (zigzag_obj_of_zigzag G (isPreconnected_zigzag d (S.obj 0))))

omit [∀ n, IsGroupoid (F.obj n)] [G.Full] [G.Faithful] in
/-- Restricting the codomain does not change the original functor. -/
theorem componentLift_comp_inclusion :
    componentLift F G S ⋙ CategoryTheory.ConnectedComponents.ι _ = G := rfl

include hS in
/-- All original structured comma categories over the actual zero component contract. -/
theorem componentLift_structured_contractible
    (x : (CategoryTheory.ConnectedComponents.mk (G.obj (S.obj 0))).Component) :
    ContractibleSpace (ClassifyingSpace (StructuredArrow x (componentLift F G S))) := by
  have hx : Zigzag (G.obj (S.obj 0)) x.obj := (Quotient.exact' x.property).symm
  obtain ⟨k, ⟨f⟩⟩ := reaches_sequence_of_zigzag F (S ⋙ G) hS hx
  let ht : ContractibleSpace (ClassifyingSpace (StructuredArrow x.obj G)) :=
    structuredArrow_contractible_of_reaches F G S hS x.obj k f
  let e : StructuredArrow x (componentLift F G S) ≌ StructuredArrow x.obj G :=
    (StructuredArrow.post x (componentLift F G S)
      (CategoryTheory.ConnectedComponents.ι _)).asEquivalence
  exact (equivalenceClassifyingHomotopyEquiv e).contractibleSpace

/-- The original functor is a genuine homotopy equivalence onto its categorical component. -/
def componentClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace D)
      (ClassifyingSpace (CategoryTheory.ConnectedComponents.mk (G.obj (S.obj 0))).Component) :=
  TheoremA.contractibleStructuredClassifyingHomotopyEquiv (componentLift F G S)
    (componentLift_structured_contractible F G S hS)

/-- The free-stage comparison lands in the actual path-component subspace. -/
def zeroComponentHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace D)
      (pathComponent (classifyingSpacePoint (G.obj (S.obj 0)))) :=
  (componentClassifyingHomotopyEquiv F G S hS).trans
    (classifyingSpaceComponentHomeomorph (Grothendieck F) (G.obj (S.obj 0))).toHomotopyEquiv

/-- The forward map is exactly the original classifying-space map, restricted to its component. -/
@[simp]
theorem zeroComponentHomotopyEquiv_val (x : ClassifyingSpace D) :
    (zeroComponentHomotopyEquiv F G S hS x).val = classifyingSpaceMap G x := by
  change (classifyingSpaceComponentHomeomorph (Grothendieck F) (G.obj (S.obj 0))
    (classifyingSpaceMap (componentLift F G S) x)).val = _
  rw [classifyingSpaceComponentHomeomorph_val]
  change (classifyingSpaceMap (componentLift F G S) ≫
    classifyingSpaceMap (CategoryTheory.ConnectedComponents.ι _)) x = _
  rw [← classifyingSpaceMap_comp, componentLift_comp_inclusion]

end CategoryTheory.Grothendieck
