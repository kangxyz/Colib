/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedEndpointFamilies
public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedZeroMaps
public import Colib.KTheory.Waldhausen.Additivity.SubdivisionBasepoint

/-! # Actual fixed-zero homotopies of normalized additivity endpoints

These homotopies use the actual weak natural-transformation families. Their
zero tracks are proved constant from the concrete endpoint zero diagrams.


Implementation provenance: `Quillen/Waldhausen/Additivity/NormalizedEndpointHomotopies.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial
universe u v

namespace CategoryTheory.Waldhausen.Additivity

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) {F G H : C ⥤ D} (a : F ⟶ G)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (hc : IsCofibrationTransformation W a V)

/-- The normalized identity deformation is homotopic to the actual canonical
rebased middle-functor map. -/
def normalizedIdentityEndpointHomotopy :
    SSet.Homotopy (SSet.diagonalMap (normalizedIdentityMap V W a hF hG hc))
      (SSet.diagonalMap (bisimplicialSSetMap V.cof V.weq hG.rebase)) :=
  diagonalWeakGridHomotopy W _ _ (normalizedIdentityEndpointFamily V W a hF hG hc)
    (normalizedIdentityEndpointFamily_weak V W a hF hG hc) (by
      intro n n' α A x
      exact (normalizedIdentityEndpointFamily_reindex_app V W a hF hG hc α.unop α.unop A x).symm)

/-- The actual realized identity-endpoint homotopy retains these exact maps. -/
def normalizedIdentityEndpointRealizationHomotopy :
    (SSet.toTop.map (SSet.diagonalMap (normalizedIdentityMap V W a hF hG hc))).hom.Homotopy
      (SSet.toTop.map (SSet.diagonalMap (bisimplicialSSetMap V.cof V.weq hG.rebase))).hom :=
  SSet.realizationSimplicialHomotopy (normalizedIdentityEndpointHomotopy V W a hF hG hc)

/-- Both actual endpoint zero diagrams force the whole identity-endpoint
simplicial zero track to be constant. -/
theorem normalizedIdentityEndpointHomotopy_fixed_zero :
    SSet.yonedaEquiv.symm (diagonalZeroVertex V) ▷ Δ[1] ≫
        (normalizedIdentityEndpointHomotopy V W a hF hG hc).h =
      CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
        SSet.yonedaEquiv.symm (diagonalZeroVertex W) := by
  refine weakGridFamilyCylinder_fixed_vertex W _ _
    (normalizedIdentityEndpointFamily V W a hF hG hc)
    (normalizedIdentityEndpointFamily_weak V W a hF hG hc) (by
      intro n n' α A x
      exact (normalizedIdentityEndpointFamily_reindex_app V W a hF hG hc α.unop α.unop A x).symm)
    (diagonalZeroVertex V) ?_ ?_
  · intro n z p
    exact normalizedIntervalDiagram_zero_obj V W a hF hG hc _ _ _ p
  · intro n z p
    exact CategoryTheory.rebaseFunctor_obj_base G V.zero W.zero ((hG.zero V.isZero).iso W.isZero)

/-- The identity-endpoint homotopy is fixed at the actual chosen zero vertex. -/
theorem normalizedIdentityEndpointRealizationHomotopy_fixed_zero (t : unitInterval) :
    normalizedIdentityEndpointRealizationHomotopy V W a hF hG hc
      (t, SSet.realizationPoint (diagonalZeroVertex V)) = SSet.realizationPoint
        (diagonalZeroVertex W) :=
  SSet.realizationSimplicialHomotopy_fixed_vertex
    (normalizedIdentityEndpointHomotopy V W a hF hG hc) _ _
    (normalizedIdentityEndpointHomotopy_fixed_zero V W a hF hG hc) t

variable [HasBinaryCoproducts D]
variable (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

/-- The normalized separated deformation is homotopic to the actual common
normalized pair-sum map. -/
def normalizedSeparatedEndpointHomotopy :
    SSet.Homotopy
      (SSet.diagonalMap (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration))
      (SSet.diagonalMap (normalizedSumMap V W hs.exactH hs.exactF)) :=
  diagonalWeakGridHomotopy W _ _ (normalizedSeparatedEndpointFamily V W a b hs)
    (normalizedSeparatedEndpointFamily_weak V W a b hs) (by
      intro n n' α A x
      exact (normalizedSeparatedEndpointFamily_reindex_app V W a b hs α.unop α.unop A x).symm)

/-- The actual realized separated-endpoint homotopy retains these exact maps. -/
def normalizedSeparatedEndpointRealizationHomotopy :
    (SSet.toTop.map (SSet.diagonalMap
      (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration))).hom.Homotopy
      (SSet.toTop.map (SSet.diagonalMap (normalizedSumMap V W hs.exactH hs.exactF))).hom :=
  SSet.realizationSimplicialHomotopy (normalizedSeparatedEndpointHomotopy V W a b hs)

/-- The actual subdivided zero vertex has a strictly constant separated
endpoint track, derived from the concrete normalized zero values. -/
theorem normalizedSeparatedEndpointHomotopy_fixed_zero :
    SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1] ≫
        (normalizedSeparatedEndpointHomotopy V W a b hs).h =
      CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
        SSet.yonedaEquiv.symm (diagonalZeroVertex W) := by
  refine weakGridFamilyCylinder_fixed_vertex W _ _
    (normalizedSeparatedEndpointFamily V W a b hs)
    (normalizedSeparatedEndpointFamily_weak V W a b hs) (by
      intro n n' α A x
      exact (normalizedSeparatedEndpointFamily_reindex_app V W a b hs α.unop α.unop A x).symm)
    (subdivisionZeroVertex V) ?_ ?_
  · intro n z p
    exact normalizedIntervalDiagram_zero_obj V W a hs.exactF hs.exactG hs.cofibration _ _ _ p
  · intro n z p
    exact normalizedSumGrid_zero_obj V W hs.exactH hs.exactF p

/-- The realized separated-endpoint homotopy is fixed at the actual
subdivision basepoint. -/
theorem normalizedSeparatedEndpointRealizationHomotopy_fixed_zero (t : unitInterval) :
    normalizedSeparatedEndpointRealizationHomotopy V W a b hs
      (t, subdivisionBasepoint V) = SSet.realizationPoint (diagonalZeroVertex W) :=
  SSet.realizationSimplicialHomotopy_fixed_vertex
    (normalizedSeparatedEndpointHomotopy V W a b hs) _ _
    (normalizedSeparatedEndpointHomotopy_fixed_zero V W a b hs) t

end CategoryTheory.Waldhausen.Additivity
