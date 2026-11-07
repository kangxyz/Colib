/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.EndpointHomotopies
public import Colib.KTheory.Waldhausen.Additivity.RealizationHomotopy
public import Colib.KTheory.Waldhausen.Additivity.DiagonalNaturality
public import Colib.Topology.Realization.OrdinalSubdivisionComparison

/-! # Genuine realized additivity for cofibration sequences of exact functors

For a structural cofibration sequence `F → G → H`, the original map of
Waldhausen S-realizations induced by `G` is homotopic to that induced by
`H ⨿ F`. The proof uses actual pushout diagrams on the mixed ordinal cylinder,
their coherent endpoint isomorphisms, and the proved ordinary subdivision
realization equivalence. No additivity or fibration assertion is a hypothesis.

These are explicitly unbased homotopies. The chosen-zero track and the
resulting canonical based K-map equality require an additional argument.

Implementation provenance: `Quillen/Waldhausen/Additivity/RealizedAdditivity.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original exact-functor
maps, structural cofibration-sequence hypotheses and universes are retained.
The diagonal naturality lemma is reused from its existing native owner.
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

/-- Before cancelling ordinary subdivision, the original middle map is
homotopic to the actual common separated-sum endpoint. -/
theorem subdivided_middle_homotopic_sum :
    ((realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG)).comp
      (realizedDiagonalMap
        (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))).Homotopic
      (realizedDiagonalMap (separatedSumMap V W hs.exactH hs.exactF)) := by
  have h₀ : (realizedDiagonalMap (identityDeformationMap V W a hs.exactF hs.exactG
    hs.cofibration)).Homotopic
      (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG)) :=
    ⟨SSet.realizationSimplicialHomotopy (identityEndpointHomotopy V W a hs.exactF hs.exactG
      hs.cofibration)⟩
  have h₁ : (realizedDiagonalMap (separatedDeformationMap V W a hs.exactF hs.exactG
    hs.cofibration)).Homotopic
      (realizedDiagonalMap (separatedSumMap V W hs.exactH hs.exactF)) :=
    ⟨SSet.realizationSimplicialHomotopy (separatedEndpointHomotopy V W a b hs)⟩
  have hm := mixed_deformation_endpoints (bisimplicialSSet V) (bisimplicialSSet W)
    (mixedDeformationMap V W a hs.exactF hs.exactG hs.cofibration)
  rw [mixedDeformationMap_zero, mixedDeformationMap_one] at hm
  exact (h₀.comp (ContinuousMap.Homotopic.refl _)).symm.trans (hm.trans h₁)

/-- The genuine additivity homotopy on the independent-grid model. -/
theorem bisimplicial_additivity :
    (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG)).Homotopic
      (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq
        (sumFunctor_isExact V W hs.exactH hs.exactF))) := by
  have h := (subdivided_middle_homotopic_sum V W a b hs).trans
    (subdivided_middle_homotopic_sum V W (sumInr H F) (sumProjection W H F)
      (splitIsCofibrationSequence V W hs.exactH hs.exactF)).symm
  exact homotopic_of_precomp_equivalence
    (SSet.OrdinalSubdivision.horizontalRealizationHomotopyEquiv (bisimplicialSSet V)) _ _ h

/-- Actual Waldhausen additivity for a genuine cofibration sequence of exact
functors, retaining the original `deloopingMap` at both endpoints. -/
theorem deloopingMap_additivity :
    (deloopingMap hs.exactG).hom.Homotopic
      (deloopingMap (sumFunctor_isExact V W hs.exactH hs.exactF)).hom := by
  have h := (ContinuousMap.Homotopic.refl
    (SSet.toTop.map (bisimplicialDiagonalIso W).hom).hom).comp
      (bisimplicial_additivity V W a b hs)
  rw [realizedDiagonalMap_exact_naturality V W hs.exactG,
    realizedDiagonalMap_exact_naturality V W (sumFunctor_isExact V W hs.exactH hs.exactF)] at h
  exact homotopic_of_precomp_equivalence
    (TopCat.homeoOfIso (SSet.toTop.mapIso (bisimplicialDiagonalIso V))).toHomotopyEquiv _ _ h

/-- A chosen actual continuous additivity homotopy. This construction does
not assert that its track at the chosen zero vertex is constant. -/
def additivityHomotopy :
    (deloopingMap hs.exactG).hom.Homotopy
      (deloopingMap (sumFunctor_isExact V W hs.exactH hs.exactF)).hom :=
  Classical.choice (deloopingMap_additivity V W a b hs)

end CategoryTheory.Waldhausen.Additivity

namespace CategoryTheory.Waldhausen.Additivity

attribute [colib_tag "COL-0219",
  colib_ref "WeibelKBook" "V, Additivity Theorem 1.2 and proof, page 2"
    "adaptation"
    "Actual realized middle map homotopic to the quotient-before-subobject coproduct map"]
  deloopingMap_additivity

end CategoryTheory.Waldhausen.Additivity

attribute [colib_ref "Waldhausen1985"
    "Proposition 1.3.2(4), pp. 331-332, and Theorem 1.4.2, p. 336" "adaptation"
    "The actual realized middle map is homotopic to the coproduct map; no basedness of this \
      homotopy is asserted"]
  CategoryTheory.Waldhausen.Additivity.deloopingMap_additivity
