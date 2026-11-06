/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Localization.Serre.StructuredTransitions

/-!
# Regression clients for the actual Serre transition theorem

Only abelian-category and Serre-class assumptions occur. In particular, no
comparison equivalences, filtered colimits or lifting assumptions are supplied.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.ExactCategory.SerreLocalization Topology

noncomputable section
universe u
attribute [local instance] Abelian.hasFiniteBiproducts canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

example (V : P.isoModSerre.Localization) (A : QuotientAuxiliaryLift P V) :
    (quotientAuxiliaryNerveStageHomotopyEquiv P V A).toFun =
      (SSet.toTop.map ((quotientAuxiliaryNerveCocone P V).ι.app A)).hom := rfl

example {N : C} {V : P.isoModSerre.Localization} (φ : P.isoModSerre.Q.obj N ≅ V) :
    (auxiliaryToIsoStructuredWithBaseClassifyingHomotopyEquiv P φ).toFun =
      (classifyingSpaceMap (auxiliaryToIsoStructuredWithBase P φ)).hom := rfl

example (N : C) :
    (auxiliaryToIsoStructuredClassifyingHomotopyEquiv P N).toFun =
      (classifyingSpaceMap (auxiliaryToIsoStructured P N)).hom := rfl

example (N : C) :
    (fullAuxiliaryStructuredEquiv P N).toFun =
      (classifyingSpaceMap (auxiliaryToIsoStructured P N ⋙ isoStructuredInclusion P _)).hom :=
  fullAuxiliaryStructuredEquiv_toFun P N

example {M N : C} (i : M ⟶ N) [Mono i] :
    TheoremB.StructuredTransitionIsHE (quotientMapQ P)
      ((quotientMapQ P).map (QConstruction.inflationArrow i)) :=
  structuredInflationTransitionIsHE P i

example {M N : C} (p : M ⟶ N) [Epi p] :
    TheoremB.StructuredTransitionIsHE (quotientMapQ P)
      ((quotientMapQ P).map (QConstruction.surjectionArrow p)) :=
  structuredSurjectionTransitionIsHE P p

example {X Y : (abelianExactStructure C).QCategory} (f : X ⟶ Y) :
    TheoremB.StructuredTransitionIsHE (quotientMapQ P) ((quotientMapQ P).map f) :=
  structuredTransitionIsHE_mapQ P f

example : TheoremB.StructuredTransitionHomotopyEquivalences (quotientMapQ P) :=
  quotientStructuredTransitionHomotopyEquivalences P

example {X Y : (abelianExactStructure P.isoModSerre.Localization).QCategory} (f : X ⟶ Y) :
    (TheoremB.structuredTransitionHomotopyEquiv (quotientMapQ P)
      (quotientStructuredTransitionHomotopyEquivalences P) f).toFun =
      (classifyingSpaceMap (StructuredArrow.map (T := quotientMapQ P) f)).hom := rfl

example {X Y : (abelianExactStructure P.isoModSerre.Localization).QCategory} (f : X ⟶ Y) :
    ∃ g : C(ClassifyingSpace (StructuredArrow X (quotientMapQ P)),
      ClassifyingSpace (StructuredArrow Y (quotientMapQ P))),
      (g.comp (TheoremB.structuredTransitionMap (quotientMapQ P) f)).Homotopic
        (ContinuousMap.id _) ∧
      ((TheoremB.structuredTransitionMap (quotientMapQ P) f).comp g).Homotopic
        (ContinuousMap.id _) := quotientStructuredTransitionHomotopyEquivalences P f
