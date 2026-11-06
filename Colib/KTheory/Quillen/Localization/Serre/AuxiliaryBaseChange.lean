/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Uses native Q-construction and intrinsic abelian full-subcategory exact structure. -/

public import Colib.CategoryTheory.Abelian.SerreClass.OverKernelBaseChange
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.QConstruction.Abelian.SpanNaturality
public import Colib.KTheory.Quillen.Localization.Serre.OverQArrows
public import Colib.KTheory.Quillen.Localization.Serre.KernelPushoutComparison
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion

/-! # Base change for the auxiliary kernel categories -/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject


namespace CategoryTheory.ExactCategory.SerreLocalization

open CategoryTheory.Abelian.SerreLocalization CategoryTheory.Abelian
attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{u} C] [Abelian C]

/-- Base change preserves both admissible legs and the pullbacks used in QConstruction
  composition. -/
def overBaseChangeCompatible {M N : C} (i : M ⟶ N) :
    QConstruction.CompatibleFunctor (overDeflation N) (overInflation N)
      (overDeflation M) (overInflation M) :=
  QConstruction.CompatibleFunctor.ofPreservesPullbacks _ _ _ _ (Over.pullback i)
    (fun f h => MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
      (overBaseChange_map_isPullback i f).flip h)
    (fun f h => MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms C)
      (overBaseChange_map_isPullback i f).flip h)

/-- The actual restricted-span Q-functor of slice base change. -/
def overBaseChangeQ {M N : C} (i : M ⟶ N) : OverQ N ⥤ OverQ M :=
  (overBaseChangeCompatible i).mapQ

/-- An ordinary natural isomorphism of compatible functors induces a
natural isomorphism on their actual quotient span categories. -/
def compatibleKernelQIso
    {D : Type u} [Category.{u} D]
    {W V : MorphismProperty D}
    [W.ContainsIdentities] [V.ContainsIdentities]
    [W.IsStableUnderComposition] [V.IsStableUnderComposition]
    [W.HasPullbacksAgainst V] [W.IsStableUnderBaseChangeAgainst V]
    [V.IsStableUnderBaseChangeAgainst W]
    (F G : QConstruction.CompatibleFunctor W V (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation) (e : F.toFunctor ≅ G.toFunctor) :
    F.mapQ ≅ G.mapQ :=
  NatIso.ofComponents (fun X => (abelianExactStructure C).qIsoOfIso (e.app X.obj.of)) (by
    rintro X Y ⟨s⟩
    change QConstruction.mkHom _ _ (F.mapSpan s) ≫ QConstruction.inflationArrow (e.app
      Y.obj.of).hom =
      QConstruction.inflationArrow (e.app X.obj.of).hom ≫ QConstruction.mkHom _ _ (G.mapSpan s)
    apply QConstruction.span_naturality_of_pullback _ _ _ _ (e.app s.apex).hom
    · exact IsPullback.of_vert_isIso ⟨e.hom.naturality s.l⟩
    · exact e.hom.naturality s.r)

/-- The kernel comparison is natural on Q-arrows, with the chosen ordinary
pullback comparison as its component. -/
def overBaseChangeKernelQIso {M N : C} (i : M ⟶ N) :
    overBaseChangeQ i ⋙ overKernelQ M ≅ overKernelQ N :=
  NatIso.ofComponents
    (fun X => (abelianExactStructure C).qIsoOfIso ((overBaseChangeKernelIso i).app X.obj.of))
    (by
      rintro X Y ⟨s⟩
      exact (compatibleKernelQIso ((overBaseChangeCompatible i).comp (overKernelCompatible M))
        (overKernelCompatible N) (overBaseChangeKernelIso i)).hom.naturality (QConstruction.mkHom
          _ _ s))

/-- Postcomposition changes the base without changing underlying span legs. -/
def overPostcomposeCompatible {M N : C} (i : M ⟶ N) :
    QConstruction.CompatibleFunctor (overDeflation M) (overInflation M)
      (overDeflation N) (overInflation N) := by
  have : PreservesLimitsOfShape WalkingCospan (Over.map i) := by
    have : PreservesLimitsOfShape WalkingCospan (Over.map i ⋙ Over.forget N) :=
      inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Over.forget M))
    exact preservesLimitsOfShape_of_reflects_of_preserves (Over.map i) (Over.forget N)
  exact QConstruction.CompatibleFunctor.ofPreservesPullbacks _ _ _ _ (Over.map i)
    (fun _ h => h) (fun _ h => h)

/-- The functor from `OverQ M` to `OverQ N` induced by postcomposing each slice structure map
with `i : M ⟶ N`. -/
def overPostcomposeQ {M N : C} (i : M ⟶ N) : OverQ M ⥤ OverQ N :=
  (overPostcomposeCompatible i).mapQ

/-- The postcomposition kernel comparison lifts to actual Q-arrows. -/
def overPostcomposeKernelQIso {M N : C} (i : M ⟶ N) [Mono i] :
    overPostcomposeQ i ⋙ overKernelQ N ≅ overKernelQ M :=
  NatIso.ofComponents
    (fun X => (abelianExactStructure C).qIsoOfIso ((overPostcomposeKernelIso i).app X.obj.of))
    (by
      rintro X Y ⟨s⟩
      exact (compatibleKernelQIso ((overPostcomposeCompatible i).comp (overKernelCompatible N))
        (overKernelCompatible M) (overPostcomposeKernelIso i)).hom.naturality (QConstruction.mkHom
          _ _ s))

/-- The pullback inclusion gives a natural transformation on Q-categories;
its naturality follows from the actual cartesian square on each left leg. -/
def overBaseChangeCounitQ {M N : C} (i : M ⟶ N) [Mono i] :
    overBaseChangeQ i ⋙ overPostcomposeQ i ⟶ 𝟭 (OverQ N) where
  app X := overInflationArrow ((Over.mapPullbackAdj i).counit.app X.obj.of)
  naturality X Y f := by
    obtain ⟨s, rfl⟩ := Quotient.exists_rep f
    apply (overForgetQ N).map_injective
    simp only [Functor.map_comp, overForgetQ_inflationArrow, Over.mapPullbackAdj_counit_app]
    change QConstruction.mkHom _ _ ((overForgetCompatible N).mapSpan
      ((overPostcomposeCompatible i).mapSpan ((overBaseChangeCompatible i).mapSpan s))) ≫
        QConstruction.inflationArrow (pullback.fst Y.obj.of.hom i) =
      QConstruction.inflationArrow (pullback.fst X.obj.of.hom i) ≫
        QConstruction.mkHom _ _ ((overForgetCompatible N).mapSpan s)
    apply QConstruction.span_naturality_of_pullback _ _ _ _ (pullback.fst s.apex.hom i)
    · exact overBaseChange_map_isPullback i s.l
    · exact (overBaseChange_map_isPullback i s.r).w

/-- Kernel compatibility of the actual Q-valued pullback counit. -/
lemma overBaseChangeCounitQ_kernel {M N : C} (i : M ⟶ N) [Mono i] (X : OverQ N) :
    (overKernelQ N).map ((overBaseChangeCounitQ i).app X) =
      (overPostcomposeKernelQIso i).hom.app ((overBaseChangeQ i).obj X) ≫
        (overBaseChangeKernelQIso i).hom.app X := by
  change (overKernelQ N).map (overInflationArrow _) = _
  rw [overKernelQ_inflationArrow]
  change QConstruction.inflationArrow ((overKernel N).map ((Over.mapPullbackAdj i).counit.app
    X.obj.of)) =
    QConstruction.inflationArrow (overPostcomposeKernelObjIso i ((Over.pullback i).obj
      X.obj.of)).hom ≫
      QConstruction.inflationArrow (overBaseChangeKernelObjIso i X.obj.of).hom
  rw [QConstruction.inflationArrow_comp]
  simp only [overBaseChangeCounit_kernel]

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- Change of base on the full auxiliary categories. -/
def auxiliaryBaseChange {M N : C} (i : M ⟶ N) :
    AuxiliaryKernel P N ⥤ AuxiliaryKernel P M where
  obj X := ⟨(overBaseChangeQ i).obj X.obj,
    overBaseChange_isoModSerre P i X.obj.obj.of X.property⟩
  map f := ObjectProperty.homMk ((overBaseChangeQ i).map f.hom)
  map_id X := by apply ObjectProperty.hom_ext; exact (overBaseChangeQ i).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; exact (overBaseChangeQ i).map_comp _ _

/-- Change of base on epimorphic auxiliary objects. -/
def epiAuxiliaryBaseChange {M N : C} (i : M ⟶ N) :
    EpiAuxiliaryKernel P N ⥤ EpiAuxiliaryKernel P M where
  obj X := ⟨(overBaseChangeQ i).obj X.obj,
    overBaseChange_isoModSerre P i X.obj.obj.of X.property.1,
    MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
      (IsPullback.of_hasPullback X.obj.obj.of.hom i) X.property.2⟩
  map f := ObjectProperty.homMk ((overBaseChangeQ i).map f.hom)
  map_id X := by apply ObjectProperty.hom_ext; exact (overBaseChangeQ i).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; exact (overBaseChangeQ i).map_comp _ _

/-- A Serre-isomorphic change of base sends auxiliary objects forward. -/
def auxiliaryPostcompose {M N : C} (i : M ⟶ N) (hi : P.isoModSerre i) :
    AuxiliaryKernel P M ⥤ AuxiliaryKernel P N where
  obj X := ⟨(overPostcomposeQ i).obj X.obj,
    P.isoModSerre.comp_mem X.obj.obj.of.hom i X.property hi⟩
  map f := ObjectProperty.homMk ((overPostcomposeQ i).map f.hom)
  map_id X := by apply ObjectProperty.hom_ext; exact (overPostcomposeQ i).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; exact (overPostcomposeQ i).map_comp _ _

/-- The monomorphic pullback counit restricts to the actual auxiliary categories. -/
def auxiliaryBaseChangeCounit {M N : C} (i : M ⟶ N) [Mono i] (hi : P.isoModSerre i) :
    auxiliaryBaseChange P i ⋙ auxiliaryPostcompose P i hi ⟶ 𝟭 (AuxiliaryKernel P N) where
  app X := ObjectProperty.homMk ((overBaseChangeCounitQ i).app X.obj)
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    exact (overBaseChangeCounitQ i).naturality f.hom

/-- The base-change kernel comparison retains values in the Serre Q-category. -/
def auxiliaryBaseChangeKernelIso {M N : C} (i : M ⟶ N) :
    auxiliaryBaseChange P i ⋙ auxiliaryKernelFunctor P M ≅ auxiliaryKernelFunctor P N :=
  NatIso.ofComponents
    (fun X => (Devissage.mapQ P).preimageIso ((overBaseChangeKernelQIso i).app X.obj)) (by
      intro X Y f
      apply (Devissage.mapQ P).map_injective
      simp only [Functor.comp_map, auxiliaryBaseChange, auxiliaryKernelFunctor,
        Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (overBaseChangeKernelQIso i).hom.naturality f.hom)

/-- The postcomposition kernel comparison retains values in the Serre Q-category. -/
def auxiliaryPostcomposeKernelIso {M N : C} (i : M ⟶ N) [Mono i]
    (hi : P.isoModSerre i) :
    auxiliaryPostcompose P i hi ⋙ auxiliaryKernelFunctor P N ≅ auxiliaryKernelFunctor P M :=
  NatIso.ofComponents
    (fun X => (Devissage.mapQ P).preimageIso ((overPostcomposeKernelQIso i).app X.obj)) (by
      intro X Y f
      apply (Devissage.mapQ P).map_injective
      simp only [Functor.comp_map, auxiliaryPostcompose, auxiliaryKernelFunctor,
        Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (overPostcomposeKernelQIso i).hom.naturality f.hom)

/-- The auxiliary counit satisfies the exact kernel identity needed to lift
it to kernel comma categories. -/
lemma auxiliaryBaseChangeCounit_kernel {M N : C} (i : M ⟶ N) [Mono i]
    (hi : P.isoModSerre i) (X : AuxiliaryKernel P N) :
    (auxiliaryKernelFunctor P N).map ((auxiliaryBaseChangeCounit P i hi).app X) =
      (auxiliaryPostcomposeKernelIso P i hi).hom.app ((auxiliaryBaseChange P i).obj X) ≫
        (auxiliaryBaseChangeKernelIso P i).hom.app X := by
  apply (Devissage.mapQ P).map_injective
  simp only [Functor.map_comp, auxiliaryBaseChangeCounit, auxiliaryKernelFunctor,
    auxiliaryPostcomposeKernelIso, auxiliaryBaseChangeKernelIso, NatIso.ofComponents_hom_app,
    Functor.preimageIso_hom, Functor.map_preimage]
  exact overBaseChangeCounitQ_kernel i X.obj

end CategoryTheory.ExactCategory.SerreLocalization
