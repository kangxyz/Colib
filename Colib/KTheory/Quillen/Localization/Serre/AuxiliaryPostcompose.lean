/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Actual native restricted-span Q-arrows, comparison functors and realization maps are retained. -/

public import Colib.CategoryTheory.Abelian.SerreClass.OverKernelPostcompose
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryBaseChange
public import Colib.KTheory.Quillen.Localization.Serre.ImageKernelComma
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

/-!
# Postcomposition equivalences for Serre auxiliary categories

For an arbitrary Serre-isomorphism of bases, the inclusion of the old
kernel into the composite kernel is natural on actual Q-spans. Comparing
with the proved kernel equivalences gives the postcomposition equivalence.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Abelian.SerreLocalization CategoryTheory.Localization
open scoped ZeroObject
namespace CategoryTheory.ExactCategory.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{u} C] [Abelian C]

/-- Kernel inclusion remains a natural transformation after the actual
restricted-span construction. -/
def overPostcomposeKernelQMap {M N : C} (i : M ⟶ N) :
    overKernelQ M ⟶ overPostcomposeQ i ⋙ overKernelQ N where
  app X := QConstruction.inflationArrow (overPostcomposeKernelMap i X.obj.of)
  naturality X Y f := by
    obtain ⟨s, rfl⟩ := Quotient.exists_rep f
    change QConstruction.mkHom _ _ ((overKernelCompatible M).mapSpan s) ≫
        QConstruction.inflationArrow (overPostcomposeKernelMap i Y.obj.of) =
      QConstruction.inflationArrow (overPostcomposeKernelMap i X.obj.of) ≫
        QConstruction.mkHom _ _ ((overKernelCompatible N).mapSpan
          ((overPostcomposeCompatible i).mapSpan s))
    apply QConstruction.span_naturality_of_pullback _ _ _ _ (overPostcomposeKernelMap i s.apex)
    · simpa only [QConstruction.CompatibleFunctor.mapSpan, overKernelCompatible,
        overPostcomposeCompatible,
        QConstruction.CompatibleFunctor.ofPreservesPullbacks] using
        overPostcomposeKernelMap_isPullback i s.l
    · exact overPostcomposeKernelMap_naturality i s.r

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- The same kernel inclusion takes values in the actual Serre Q-category. -/
def auxiliaryPostcomposeKernelMap {M N : C} (i : M ⟶ N) (hi : P.isoModSerre i) :
    auxiliaryKernelFunctor P M ⟶ auxiliaryPostcompose P i hi ⋙ auxiliaryKernelFunctor P N where
  app X := (Abelian.Devissage.mapQ P).preimage ((overPostcomposeKernelQMap i).app X.obj)
  naturality X Y f := by
    apply (Abelian.Devissage.mapQ P).map_injective
    simp only [Functor.map_comp, Functor.comp_map, auxiliaryPostcompose,
      auxiliaryKernelFunctor, Functor.map_preimage]
    exact (overPostcomposeKernelQMap i).naturality f.hom

/-- Any Serre-isomorphism of bases gives a homotopy equivalence of auxiliary
categories, with the actual postcomposition functor as its forward map. -/
def auxiliaryPostcomposeClassifyingHomotopyEquiv {M N : C} (i : M ⟶ N)
    (hi : P.isoModSerre i) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P M))
      (ClassifyingSpace (AuxiliaryKernel P N)) := by
  let eM := auxiliaryKernelClassifyingHomotopyEquiv P M
  let eN := auxiliaryKernelClassifyingHomotopyEquiv P N
  let f := (classifyingSpaceMap (auxiliaryPostcompose P i hi)).hom
  have h : (eN.toFun.comp f).Homotopic eM.toFun := by
    simpa only [eM, eN, f, auxiliaryKernelClassifyingHomotopyEquiv_toFun,
      classifyingSpaceMap_comp, TopCat.hom_comp] using
      (show (classifyingSpaceMap (auxiliaryPostcompose P i hi ⋙ auxiliaryKernelFunctor P
        N)).hom.Homotopic
        (classifyingSpaceMap (auxiliaryKernelFunctor P M)).hom from
        ⟨(classifyingSpaceNaturalTransformationHomotopy (auxiliaryPostcomposeKernelMap P i
          hi)).symm⟩)
  apply TheoremA.homotopyEquivWithMap (eM.trans eN.symm) f
  exact (show f.Homotopic (eN.invFun.comp (eN.toFun.comp f)) from by
    simpa using ContinuousMap.Homotopic.comp eN.left_inv.symm (.refl f)).trans
      (ContinuousMap.Homotopic.comp (.refl eN.invFun) h)

@[simp]
theorem auxiliaryPostcomposeClassifyingHomotopyEquiv_toFun {M N : C} (i : M ⟶ N)
    (hi : P.isoModSerre i) :
    (auxiliaryPostcomposeClassifyingHomotopyEquiv P i hi).toFun =
      (classifyingSpaceMap (auxiliaryPostcompose P i hi)).hom := rfl

end CategoryTheory.ExactCategory.SerreLocalization
