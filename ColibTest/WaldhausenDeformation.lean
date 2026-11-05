/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.KTheory.Waldhausen.Additivity.SubdividedBasedHomotopy

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
variable {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
variable (hs : IsCofibrationSequence V W a b)

example :
    ((realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase)).comp
      (realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint
        (bisimplicialSSet V)))).HomotopyRel
      (realizedDiagonalMap (normalizedSumMap V W hs.exactH hs.exactF))
        {subdivisionBasepoint V} := subdividedBasedAdditivityHomotopy V W a b hs

example (t : unitInterval) :
    normalizedIdentityEndpointRealizationHomotopy V W a hs.exactF hs.exactG hs.cofibration
      (t, SSet.realizationPoint (diagonalZeroVertex V)) =
        SSet.realizationPoint (diagonalZeroVertex W) :=
  normalizedIdentityEndpointRealizationHomotopy_fixed_zero V W a hs.exactF hs.exactG
    hs.cofibration t

example (t : unitInterval) :
    normalizedSeparatedEndpointRealizationHomotopy V W a b hs (t, subdivisionBasepoint V) =
      SSet.realizationPoint (diagonalZeroVertex W) :=
  normalizedSeparatedEndpointRealizationHomotopy_fixed_zero V W a b hs t

example (t : unitInterval) :
    SSet.realizationSimplicialHomotopy
      (normalizedMixedEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration)
        (t, subdivisionBasepoint V) = SSet.realizationPoint (diagonalZeroVertex W) :=
  normalizedMixedRealizationHomotopy_fixed_zero V W a hs.exactF hs.exactG hs.cofibration t

example :
    realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))
      (subdivisionBasepoint V) = SSet.realizationPoint (diagonalZeroVertex V) :=
  horizontalEndpoint_basepoint V

example : SSet.Homotopy
    (SSet.diagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) ≫
      SSet.diagonalMap (normalizedIdentityMap V W a hs.exactF hs.exactG hs.cofibration))
    (SSet.diagonalMap (normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration)) :=
  normalizedMixedEndpointHomotopy V W a hs.exactF hs.exactG hs.cofibration
