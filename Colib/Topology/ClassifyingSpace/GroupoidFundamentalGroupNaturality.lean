/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.FundamentalGroup
public import Colib.Topology.ClassifyingSpace.ArrowPathsNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.FundamentalGroup

/-! # Naturality of the actual group-nerve fundamental-group equivalence

Implementation provenance: `Quillen/Waldhausen/Cofinality/KZeroNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This generic result retains the original realized arrow and basepoint equality.
-/

@[expose] public noncomputable section

open CategoryTheory Topology
universe u

namespace CategoryTheory.GroupoidClassifying

lemma singleObjPiOneEquiv_natural {G H : Type u} [Group G] [Group H]
    (f : G →* H) (g : G) :
    HomotopyGroup.mapHom (classifyingSpaceMap f.toFunctor).hom
      (classifyingSpaceMap_point f.toFunctor (SingleObj.star G))
      (singleObjPiOneEquiv G g) = singleObjPiOneEquiv H (f g) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (HomotopyGroup.map (classifyingSpaceMap f.toFunctor).hom
      (classifyingSpaceMap_point f.toFunctor (SingleObj.star G)) (singleObjPiOneEquiv G g)) = _
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
  simp only [singleObjPiOneEquiv_apply]
  rw [FundamentalGroup.mapOfEq_apply]
  apply End.ext
  exact congrArg Path.Homotopic.Quotient.mk
    (classifyingSpacePath_map f.toFunctor (SingleObj.toEnd G g).asHom)

end CategoryTheory.GroupoidClassifying
