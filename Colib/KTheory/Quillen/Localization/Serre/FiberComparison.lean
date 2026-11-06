/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Quillen.Localization.Serre.Basic
public import Colib.Topology.ClassifyingSpace.Constant
public import Colib.Topology.Realization.HomotopyBridge
public import Colib.Topology.HomotopyFiber.Basic
public import Colib.KTheory.Quillen.Devissage.Basic
public import Colib.CategoryTheory.QConstruction.ZeroFunctor
public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic

/-! # The categorical nullhomotopy data for Serre localization

The quotient after the exact inclusion of the Serre subcategory is naturally
isomorphic, at the Q-category level, to the constant zero functor. This is
actual comparison data; a homotopy-fiber equivalence is not asserted here.
-/
/-! Implementation provenance: adapted from
`Quillen/Localization/Serre/FiberComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual functors, maps and
basepoint tracks are retained, using native Colib lower owners. -/

@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Topology HomotopyGroup

namespace CategoryTheory.ExactCategory.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- Canonical categorical nullhomotopy data for the quotient composed with
inclusion of the Serre class. -/
def quotientInclusionZeroIso :
    Abelian.Devissage.mapQ P ⋙ quotientMapQ P ≅
      (Functor.const (abelianExactStructure P.FullSubcategory).QCategory).obj
        ((abelianExactStructure P.isoModSerre.Localization)).qZero :=
  ((abelianExactStructure
    P.isoModSerre.Localization)).qFunctorIsoConstZero _ (fun X =>
    (quotient_isZero_obj_iff P X.obj.of.obj).2 X.obj.of.property)

/-- Realizing the categorical zero comparison gives an actual nullhomotopy
of the quotient map composed with the inclusion map. -/
def quotientInclusionNullhomotopy :
    ((classifyingSpaceMap (quotientMapQ P)).hom.comp
      (classifyingSpaceMap (Abelian.Devissage.mapQ P)).hom).Homotopy
      (ContinuousMap.const _ ((abelianExactStructure
        P.isoModSerre.Localization)).kBasepoint) :=
  (classifyingSpaceNaturalTransformationHomotopy (quotientInclusionZeroIso P).hom).cast
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
    (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- The genuine map from the Serre Q-space to the path-space homotopy fiber
of the quotient. The zero-normalized comparison is proved to be a weak homotopy
equivalence in `FiberEquivalence`; no global homotopy inverse is asserted here. -/
def localizationFiberComparison :
    C((abelianExactStructure P.FullSubcategory).KSpace,
      HomotopyFiber (classifyingSpaceMap (quotientMapQ P)).hom
        ((abelianExactStructure
          P.isoModSerre.Localization)).kBasepoint) :=
  HomotopyFiber.lift _ _ (classifyingSpaceMap (Abelian.Devissage.mapQ P)).hom
    (quotientInclusionNullhomotopy P)

/-- The fiber comparison really lies over the inclusion, strictly. -/
@[simp]
theorem localizationFiberComparison_projection :
    (HomotopyFiber.projection (classifyingSpaceMap (quotientMapQ P)).hom
      ((abelianExactStructure
        P.isoModSerre.Localization)).kBasepoint).comp
        (localizationFiberComparison P) =
      (classifyingSpaceMap (Abelian.Devissage.mapQ P)).hom :=
  HomotopyFiber.projection_lift _ _ _ _

end CategoryTheory.ExactCategory.SerreLocalization
