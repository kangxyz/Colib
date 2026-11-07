/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryColimit
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryStructuredTransition
public import Colib.KTheory.Quillen.Localization.Serre.AuxiliaryBaseChangeEquivalence
public import Colib.Topology.FilteredRealization.HomotopyEquivalence
public import Colib.CategoryTheory.TheoremB.StructuredTransitionCalculus
public import Colib.CategoryTheory.QConstruction.Abelian.SpanFactorization

/-!
# Actual Serre quotient structured-transition homotopy equivalences

The actual auxiliary nerves form a filtered simplicial colimit. Native filtered
realization supplies the comparison equivalences, with exactly the realized
cocone legs as forward maps. Actual mono/epi squares and fixed-target quotient
span lifting then prove every structured transition is a homotopy equivalence.
No auxiliary comparison equivalence is assumed.

Adapted from `Quillen/Localization/Serre/StructuredTransitions.lean` and its
three assembly/reduction files at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The conditional assembly interfaces are eliminated by using the proved maps
and homotopy equivalences directly. Theorem B's fiber conclusion is separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Localization CategoryTheory.Abelian.SerreLocalization Topology
namespace CategoryTheory.ExactCategory.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The actual canonical stage map into the isomorphism-comma nerve is a
homotopy equivalence, by the proved filtered realization theorem. -/
def quotientAuxiliaryNerveStageHomotopyEquiv
    (V : P.isoModSerre.Localization) (A : QuotientAuxiliaryLift P V) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj ((quotientAuxiliaryNerveDiagram P V).obj A))
      (SSet.toTop.obj (quotientAuxiliaryNerveCocone P V).pt) :=
  FilteredRealization.stageHomotopyEquiv (quotientAuxiliaryNerveDiagram P V)
    (quotientAuxiliaryNerveCocone P V) (quotientAuxiliaryNerveCoconeIsColimit P V)
    (quotientAuxiliaryNerveTransitionEquiv P V)
    (quotientAuxiliaryNerveTransitionEquiv_toFun P V) A

@[simp]
theorem quotientAuxiliaryNerveStageHomotopyEquiv_toFun
    (V : P.isoModSerre.Localization) (A : QuotientAuxiliaryLift P V) :
    (quotientAuxiliaryNerveStageHomotopyEquiv P V A).toFun =
      (SSet.toTop.map ((quotientAuxiliaryNerveCocone P V).ι.app A)).hom := rfl

/-- Quillen's auxiliary comparison for every specified ordinary quotient
identification, with exactly the genuine functor as its forward map. -/
def auxiliaryToIsoStructuredWithBaseClassifyingHomotopyEquiv
    {N : C} {V : P.isoModSerre.Localization} (φ : P.isoModSerre.Q.obj N ≅ V) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P N))
      (ClassifyingSpace (IsoStructuredComma P
        (QConstruction.of ((abelianExactStructure P.isoModSerre.Localization)).deflation
          ((abelianExactStructure P.isoModSerre.Localization)).inflation V))) := by
  let A := auxiliaryLiftMk P.isoModSerre.Q V φ
  let e := quotientAuxiliaryNerveStageHomotopyEquiv P V A
  apply TheoremA.homotopyEquivWithMap e (classifyingSpaceMap (auxiliaryToIsoStructuredWithBase P
    φ)).hom
  have he : e.toFun = (classifyingSpaceMap (auxiliaryToIsoStructuredWithBase P φ)).hom := by
    dsimp only [e, A]
    rw [quotientAuxiliaryNerveStageHomotopyEquiv_toFun, quotientAuxiliaryNerveCocone_map,
      asIso_auxiliaryLiftMk]
  rw [he]

@[simp]
theorem auxiliaryToIsoStructuredWithBaseClassifyingHomotopyEquiv_toFun
    {N : C} {V : P.isoModSerre.Localization} (φ : P.isoModSerre.Q.obj N ≅ V) :
    (auxiliaryToIsoStructuredWithBaseClassifyingHomotopyEquiv P φ).toFun =
      (classifyingSpaceMap (auxiliaryToIsoStructuredWithBase P φ)).hom := rfl

/-- The fixed-base auxiliary comparison, with its actual functor as forward map. -/
def auxiliaryToIsoStructuredClassifyingHomotopyEquiv (N : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P N))
      (ClassifyingSpace (IsoStructuredComma P ((quotientMapQ P).obj
        (QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
          N)))) := by
  let e := auxiliaryToIsoStructuredWithBaseClassifyingHomotopyEquiv P
    (Iso.refl (P.isoModSerre.Q.obj N))
  apply TheoremA.homotopyEquivWithMap e
    (classifyingSpaceMap (auxiliaryToIsoStructured P N)).hom
  have he : e.toFun = (classifyingSpaceMap (auxiliaryToIsoStructured P N)).hom := by
    rw [show e.toFun = _ from
      auxiliaryToIsoStructuredWithBaseClassifyingHomotopyEquiv_toFun P _]
    rw [auxiliaryToIsoStructured_eq_withBaseRefl]
  rw [he]

@[simp]
theorem auxiliaryToIsoStructuredClassifyingHomotopyEquiv_toFun (N : C) :
    (auxiliaryToIsoStructuredClassifyingHomotopyEquiv P N).toFun =
      (classifyingSpaceMap (auxiliaryToIsoStructured P N)).hom := rfl

/-- Composing with the already proved isomorphism-comma inclusion gives the
full structured-comma comparison, with its actual map retained. -/
def fullAuxiliaryStructuredEquiv (N : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (AuxiliaryKernel P N))
      (ClassifyingSpace (StructuredArrow ((quotientMapQ P).obj
        (QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
          N))
          (quotientMapQ P))) :=
  (auxiliaryToIsoStructuredClassifyingHomotopyEquiv P N).trans
    (isoStructuredInclusionClassifyingHomotopyEquiv P _)

lemma fullAuxiliaryStructuredEquiv_toFun (N : C) :
    (fullAuxiliaryStructuredEquiv P N).toFun =
      (classifyingSpaceMap (auxiliaryToIsoStructured P N ⋙ isoStructuredInclusion P _)).hom := by
  change (isoStructuredInclusionClassifyingHomotopyEquiv P _).toFun.comp
    (auxiliaryToIsoStructuredClassifyingHomotopyEquiv P N).toFun = _
  rw [auxiliaryToIsoStructuredClassifyingHomotopyEquiv_toFun,
    isoStructuredInclusionClassifyingHomotopyEquiv_toFun,
    classifyingSpaceMap_comp, TopCat.hom_comp]
  rfl

/-- The monomorphic transition square gives the actual mono transition equivalence. -/
theorem structuredInflationTransitionIsHE {M N : C} (i : M ⟶ N) [Mono i] :
    TheoremB.StructuredTransitionIsHE (quotientMapQ P) ((quotientMapQ P).map
      (QConstruction.inflationArrow i))
      := by
  let s := fullAuxiliaryStructuredEquiv P N
  let t := (auxiliaryBaseChangeClassifyingHomotopyEquiv P i).trans (fullAuxiliaryStructuredEquiv P
    M)
  let f := TheoremB.structuredTransitionMap (quotientMapQ P) ((quotientMapQ P).map
    (QConstruction.inflationArrow
    i))
  have h : (f.comp s.toFun).Homotopic t.toFun := by
    have H := (classifyingSpaceNaturalTransformationHomotopy (auxiliaryStructuredInflationSquare P
      i)).symm
    refine ⟨H.cast ?_ ?_⟩
    · simp only [f, s, fullAuxiliaryStructuredEquiv_toFun P,
        TheoremB.structuredTransitionMap, TheoremB.structuredTransition,
        classifyingSpaceMap_comp, TopCat.hom_comp, ContinuousMap.comp_assoc]
    · change _ = (fullAuxiliaryStructuredEquiv P M).toFun.comp
        (auxiliaryBaseChangeClassifyingHomotopyEquiv P i).toFun
      rw [fullAuxiliaryStructuredEquiv_toFun P,
        auxiliaryBaseChangeClassifyingHomotopyEquiv_toFun]
      simp only [classifyingSpaceMap_comp, TopCat.hom_comp, ContinuousMap.comp_assoc]
  exact ⟨TheoremA.homotopyEquivOfTriangle s t f h, rfl⟩

/-- The reversed-epimorphism square gives the actual epi transition equivalence. -/
theorem structuredSurjectionTransitionIsHE {M N : C} (p : M ⟶ N) [Epi p] :
    TheoremB.StructuredTransitionIsHE (quotientMapQ P) ((quotientMapQ P).map
      (QConstruction.surjectionArrow p))
      := by
  let s := (auxiliaryBaseChangeClassifyingHomotopyEquiv P p).trans (fullAuxiliaryStructuredEquiv P
    M)
  let t := fullAuxiliaryStructuredEquiv P N
  let f := TheoremB.structuredTransitionMap (quotientMapQ P) ((quotientMapQ P).map
    (QConstruction.surjectionArrow p))
  have h : (f.comp s.toFun).Homotopic t.toFun := by
    have H := (classifyingSpaceNaturalTransformationHomotopy (auxiliaryStructuredSurjectionSquare P
      p)).symm
    refine ⟨H.cast ?_ ?_⟩
    · change _ = f.comp ((fullAuxiliaryStructuredEquiv P M).toFun.comp
        (auxiliaryBaseChangeClassifyingHomotopyEquiv P p).toFun)
      rw [fullAuxiliaryStructuredEquiv_toFun P,
        auxiliaryBaseChangeClassifyingHomotopyEquiv_toFun]
      simp only [f, TheoremB.structuredTransitionMap, TheoremB.structuredTransition,
        classifyingSpaceMap_comp, TopCat.hom_comp, ContinuousMap.comp_assoc]
    · exact (fullAuxiliaryStructuredEquiv_toFun P N).symm
  exact ⟨TheoremA.homotopyEquivOfTriangle s t f h, rfl⟩

/-- Every actual mapped Q-span induces a homotopy equivalence of structured commas. -/
theorem structuredTransitionIsHE_mapQ
    {X Y : (abelianExactStructure C).QCategory} (f : X ⟶ Y) :
    TheoremB.StructuredTransitionIsHE (quotientMapQ P) ((quotientMapQ P).map f) := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  change QConstruction.AbelianSpan X.obj.of Y.obj.of at s
  change TheoremB.StructuredTransitionIsHE (quotientMapQ P) ((quotientMapQ P).map
    (QConstruction.mkHom _ _ s))
  rw [← QConstruction.span_factorization, Functor.map_comp]
  exact TheoremB.StructuredTransitionIsHE.comp _ (structuredSurjectionTransitionIsHE P s.l)
    (structuredInflationTransitionIsHE P s.r)

/-- The canonical Serre quotient satisfies Theorem B's actual structured-transition
hypothesis. Only the abelian and Serre-class assumptions occur. -/
theorem quotientStructuredTransitionHomotopyEquivalences :
    TheoremB.StructuredTransitionHomotopyEquivalences (quotientMapQ P) := by
  apply TheoremB.structuredTransitions_of_pointwise
  intro d e f
  let L := P.isoModSerre.Q
  let := Localization.essSurj L P.isoModSerre
  let M := L.objPreimage e.obj.of
  let β : (quotientMapQ P).obj (QConstruction.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation M) ≅ e :=
    ((abelianExactStructure P.isoModSerre.Localization)).qIsoOfIso (L.objObjPreimageIso e.obj.of)
  obtain ⟨X, g, a, h⟩ := exists_qHom_lift L P (M := M) (V := d.obj.of) (f ≫ β.inv)
  let α : (quotientMapQ P).obj (QConstruction.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X) ≅ d := ((abelianExactStructure
        P.isoModSerre.Localization)).qIsoOfIso a
  have hg : (quotientMapQ P).map g = α.hom ≫ (f ≫ β.inv) := h
  have hf : f = α.inv ≫ (quotientMapQ P).map g ≫ β.hom := by rw [hg]; simp
  rw [hf]
  exact TheoremB.StructuredTransitionIsHE.comp _
    (TheoremB.structuredTransitionIsHE_of_isIso _ α.inv)
    (TheoremB.StructuredTransitionIsHE.comp _
      (structuredTransitionIsHE_mapQ P g)
      (TheoremB.structuredTransitionIsHE_of_isIso _ β.hom))

end CategoryTheory.ExactCategory.SerreLocalization
