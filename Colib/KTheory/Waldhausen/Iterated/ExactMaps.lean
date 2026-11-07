/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.OmegaSpectrum
public import Colib.KTheory.Waldhausen.Functoriality

/-! Actual prespectrum maps of arbitrary original exact functors, retaining the public K-map.
Canonical zero normalization removes the chosen-zero-image equality hypothesis. -/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/ExactMaps.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete based tracks,
structure-map parameters and universe assumptions are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Every original exact functor has an actual prespectrum map, using the existing
canonical zero rebase rather than requiring equality of the original zero image. -/
def exactOriginalPrespectrumMap : originalPrespectrum W ⟶ originalPrespectrum V :=
  originalPrespectrumMap W V hF.rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

/-- The exact-functor map is unchanged by the proved Omega-spectrum enhancement. -/
def exactOriginalOmegaSpectrumMap : originalOmegaSpectrum W ⟶ originalOmegaSpectrum V :=
  ObjectProperty.homMk (exactOriginalPrespectrumMap W V hF)

/-- The induced homotopy-set map retains the original public KMap. -/
lemma exactOriginalZeroSpaceEquiv_naturality (n : ℕ) (a : W.K n) :
    originalZeroSpaceEquiv V n (KMap hF n a) =
      HomotopyGroup.map ((exactOriginalPrespectrumMap W V hF).map 0)
        ((exactOriginalPrespectrumMap W V hF).map_point 0) (originalZeroSpaceEquiv W n a) := by
  have h := KMap_eq_of_iso hF hF.rebase
    (CategoryTheory.rebaseFunctorIso F W.zero V.zero ((hF.zero W.isZero).iso V.isZero)) n
  rw [h]
  exact originalZeroSpaceEquiv_naturality W V hF.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) n a

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0276"]
  CategoryTheory.Waldhausen.IteratedS.exactOriginalPrespectrumMap
  CategoryTheory.Waldhausen.IteratedS.exactOriginalZeroSpaceEquiv_naturality

attribute [colib_tag "COL-0282"]
  CategoryTheory.Waldhausen.IteratedS.exactOriginalOmegaSpectrumMap
