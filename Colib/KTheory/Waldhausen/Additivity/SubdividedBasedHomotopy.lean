/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References

public import Colib.KTheory.Waldhausen.Additivity.NormalizedEndpointHomotopies
public import Colib.KTheory.Waldhausen.Additivity.NormalizedMixedHomotopy
public import Colib.KTheory.Waldhausen.Additivity.BasedHomotopyTools


/-! # The actual subdivided based three-stage deformation

All three deformation homotopies have proved constant chosen-zero tracks.
The three homotopies compose before any cancellation of subdivision.
No additivity equality or subdivision surjectivity is asserted.


Implementation provenance: `Quillen/Waldhausen/Additivity/BasedAdditivity.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v

namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
variable {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
variable (hs : IsCofibrationSequence V W a b)

/-- The actual rebased middle map and the common normalized separated sum
are homotopic relative to the displayed subdivided zero point. -/
def subdividedBasedAdditivityHomotopy :
    ((realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase)).comp
      (realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet
        V)))).HomotopyRel
      (realizedDiagonalMap (normalizedSumMap V W hs.exactH hs.exactF))
      {subdivisionBasepoint V} := by
  let h₀ := homotopyRelOfFixed
    (normalizedIdentityEndpointRealizationHomotopy V W a hs.exactF hs.exactG hs.cofibration)
    (SSet.realizationPoint (diagonalZeroVertex V)) (SSet.realizationPoint (diagonalZeroVertex W))
    (normalizedIdentityEndpointRealizationHomotopy_fixed_zero V W a hs.exactF hs.exactG
      hs.cofibration)
  let hm := homotopyRelOfFixed
    (SSet.realizationSimplicialHomotopy
      (normalizedMixedEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration))
    (subdivisionBasepoint V) (SSet.realizationPoint (diagonalZeroVertex W))
    (normalizedMixedRealizationHomotopy_fixed_zero V W a hs.exactF hs.exactG hs.cofibration)
  let h₁ := homotopyRelOfFixed
    (normalizedSeparatedEndpointRealizationHomotopy V W a b hs)
    (subdivisionBasepoint V) (SSet.realizationPoint (diagonalZeroVertex W))
    (normalizedSeparatedEndpointRealizationHomotopy_fixed_zero V W a b hs)
  have hm' :
      ((realizedDiagonalMap (normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration)).comp
        (realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet
          V)))).HomotopyRel
        (realizedDiagonalMap (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration))
        {subdivisionBasepoint V} :=
    hm.cast (congrArg TopCat.Hom.hom (SSet.toTop.map_comp _ _)) rfl
  exact (homotopyRelPrecompPoint h₀
    (realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
    (subdivisionBasepoint V) (horizontalEndpoint_basepoint V)).symm.trans (hm'.trans h₁)

end CategoryTheory.Waldhausen.Additivity

attribute [colib_tag "COL-0218",
  colib_ref "WeibelKBook" "V, Definition 1.1(b) and Theorem 1.2, pages 1-2"
    "adaptation"
    "Actual mixed-ordinal three-stage chosen-zero-relative deformation for additivity"]
  CategoryTheory.Waldhausen.Additivity.subdividedBasedAdditivityHomotopy
