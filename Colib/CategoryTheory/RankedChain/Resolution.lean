/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.RankedChain.Comma
public import Colib.CategoryTheory.SemisimplexResolution.Contraction

/-!
# The actual poset resolution of a category

The constructed append-or-terminal-identity-compression closure receives
actual natural transformations from the identity and a constant on each
ORIGINAL last-vertex comma. The resulting genuine comma contractions let the
existing contractible-comma Theorem A construct an actual homotopy equivalence.
No weak-equivalence lifting or CW Whitehead upgrade is used.

Applied to the original semisimplex category, whose dimension is a direct
rank, this gives an actual poset ResolutionPoset C and resolutionFunctor C to
any small category C. The composed homotopy equivalence's forward map is
proved exactly the original displayed functor's classifying-space map.

Implementation provenance:
`Quillen/CategoryTheory/RankedChain/Resolution.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u

namespace CategoryTheory.RankedChainOrder
variable (C : Type u) [SmallCategory C] (rank : C → ℕ)
  (hRank : IsDirectRank C rank)

/-- Append genuine terminal progress, or retain the unchanged chain when its
terminal arrow is an identity. Maps use the proved mixed-case extension. -/
def closeFunctor (Y : C) : CostructuredArrow (lastVertex C rank) Y ⥤
    CostructuredArrow (lastVertex C rank) Y where
  obj := closeObj C rank
  map {S B} f := (exists_close_to_closed C rank S (closeObj C rank B)
    (closeObj_closed C rank hRank B) (f ≫ toClose C rank B)).some
  map_id _ := by apply CostructuredArrow.hom_ext; exact Subsingleton.elim _ _
  map_comp _ _ := by apply CostructuredArrow.hom_ext; exact Subsingleton.elim _ _

/-- Every original comma object maps naturally to its actual closure. -/
def identityToClose (Y : C) : 𝟭 (CostructuredArrow (lastVertex C rank) Y) ⟶
    closeFunctor C rank hRank Y where
  app := toClose C rank
  naturality _ _ _ := by apply CostructuredArrow.hom_ext; exact Subsingleton.elim _ _

/-- The fixed original target vertex maps naturally to the same closure. -/
def constantToClose (Y : C) :
    (Functor.const (CostructuredArrow (lastVertex C rank) Y)).obj (vertexComma C rank Y) ⟶
      closeFunctor C rank hRank Y where
  app S := vertexToClosed C rank (closeObj C rank S) (closeObj_closed C rank hRank S)
  naturality _ _ _ := by apply CostructuredArrow.hom_ext; exact Subsingleton.elim _ _

include hRank in
/-- The original last-vertex comma is genuinely contractible via the actual
append-or-compress zigzag; higher contraction is not an input premise. -/
theorem comma_contractible (Y : C) :
    ContractibleSpace (ClassifyingSpace (CostructuredArrow (lastVertex C rank) Y)) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨classifyingSpacePoint (vertexComma C rank Y), ⟨?_⟩⟩
  have H := (classifyingSpaceNaturalTransformationHomotopy (identityToClose C rank hRank Y)).trans
    (classifyingSpaceNaturalTransformationHomotopy (constantToClose C rank hRank Y)).symm
  simpa only [classifyingSpaceMap_id, TopCat.hom_id, classifyingSpaceMap_const] using H

/-- The original last-vertex functor is an actual homotopy equivalence, by
Theorem A from the proved original comma contractions. -/
def lastVertexHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Obj C rank)) (ClassifyingSpace C) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (lastVertex C rank)
    (comma_contractible C rank hRank)

/-- Its forward map is literally the original last-vertex classifying map. -/
@[simp] theorem lastVertexHomotopyEquiv_toFun :
    (lastVertexHomotopyEquiv C rank hRank).toFun = (classifyingSpaceMap (lastVertex C rank)).hom :=
      rfl

/-- The actual poset of strict chains in the original semisimplex category. -/
abbrev ResolutionPoset := Obj (SemisimplexResolution.Obj C) SemisimplexResolution.Obj.dim

/-- The original last-vertex functors give a comparison from the actual poset
to the original category, retaining all parallel-arrow chain data. -/
def resolutionFunctor : ResolutionPoset C ⥤ C :=
  lastVertex (SemisimplexResolution.Obj C) SemisimplexResolution.Obj.dim ⋙
    SemisimplexResolution.lastVertex C

/-- Every small category has this actual poset resolution by a homotopy
equivalence, without requiring its nerve to be a regular simplicial complex. -/
def resolutionHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (ResolutionPoset C)) (ClassifyingSpace C) :=
  (lastVertexHomotopyEquiv (SemisimplexResolution.Obj C) SemisimplexResolution.Obj.dim
    (semisimplex_directRank C)).trans (SemisimplexResolution.lastVertexHomotopyEquiv C)

/-- The resolution equivalence's forward map retains exactly the displayed
original categorical comparison, rather than an unspecified equivalent map. -/
@[simp] theorem resolutionHomotopyEquiv_toFun :
    (resolutionHomotopyEquiv C).toFun = (classifyingSpaceMap (resolutionFunctor C)).hom := by
  change (SemisimplexResolution.lastVertexHomotopyEquiv C).toFun.comp
    (lastVertexHomotopyEquiv (SemisimplexResolution.Obj C) SemisimplexResolution.Obj.dim
      (semisimplex_directRank C)).toFun = _
  rw [lastVertexHomotopyEquiv_toFun, SemisimplexResolution.lastVertexHomotopyEquiv_toFun]
  exact congrArg TopCat.Hom.hom (classifyingSpaceMap_comp _ _).symm

end CategoryTheory.RankedChainOrder
