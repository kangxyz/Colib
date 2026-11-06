/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.Constant
public import Colib.Topology.Realization.HomotopyBridge
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.CategoryTheory.Category.Preorder

/-! # Contractibility of join-semilattice classifying spaces

For any nonempty join-semilattice, joining with a chosen element receives
natural transformations from both the identity and the constant functor.
Their realized homotopies give a concrete contraction of the actual classifying space.

Adapted from `Quillen/Localization/Serre/LocalizationComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native Q-spans,
comma categories, functors and realization maps are retained.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory

/-- A nonempty join-semilattice has a concrete classifying-space contraction:
join with one chosen object receives natural transformations from both the
identity and the constant functor. No general filtered-nerve theorem is used. -/
theorem classifyingSpace_contractible_of_semilatticeSup
    (A : Type u) [SemilatticeSup A] [Nonempty A] : ContractibleSpace (ClassifyingSpace A) := by
  let a : A := Classical.choice inferInstance
  let F : A ⥤ A := (show Monotone (fun x : A => x ⊔ a) from
    fun _ _ h => sup_le_sup_right h a).functor
  let η : 𝟭 A ⟶ F := { app := fun x => homOfLE le_sup_left }
  let ε : (Functor.const A).obj a ⟶ F := { app := fun x => homOfLE le_sup_right }
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨classifyingSpacePoint a, ?_⟩
  simpa only [classifyingSpaceMap_id, classifyingSpaceMap_const_direct, TopCat.hom_id,
    TopCat.const, TopCat.hom_ofHom, ContinuousMap.const] using
    (ContinuousMap.Homotopic.trans
      ⟨classifyingSpaceNaturalTransformationHomotopy η⟩
      ⟨(classifyingSpaceNaturalTransformationHomotopy ε).symm⟩)

end CategoryTheory
