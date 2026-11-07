/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Pi.FiniteStages
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion
public import Colib.KTheory.Quillen.Map.RebasePath
public import Colib.Topology.FilteredRealization.FullNerveColimit
public import Colib.Topology.FilteredRealization.BasedGroups
public import Colib.Topology.ClassifyingSpace.AsSmall

/-!
# Actual finite-support Q stages and their based K-maps

The finite subsets of the original category family index a strict diagram of
actual Q-categories. Existing full faithfulness of the Serre Q-inclusions and
finite support of objects give a genuine nerve colimit. A single original zero
family supplies strictly compatible vertices, including the empty stage.

Stage representability and eventual equality follow for the based homotopy
groups. The displayed original-category zero isomorphism identifies the raw
stage map with the library's normalized K-map, yielding
`KMap_jointlySurjective` in every nonnegative K-degree. No finite-support
K-decomposition or field calculation is assumed here.

Implementation provenance: `Quillen/KTheory/FiniteSupport/FilteredStages.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual objects, maps, degrees
and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology HomotopyGroup
open scoped Simplicial ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.Pi.FiniteSupport
open CategoryTheory.Pi

/-- The finite-subset category lifted to the realization universe. -/
abbrev StageIndex (I : Type u) := AsSmall.{v} (Finset I)

variable {I : Type u} (C : I → Type v) [∀ i, Category.{v} (C i)] [∀ i, Abelian (C i)]

/-- The original finite subset represented by a lifted stage index. -/
abbrev stageSet (s : StageIndex.{u, v} I) : Finset I := AsSmall.down.obj s

/-- The nested support condition in the original finite-support family. -/
abbrev stageProperty (s : StageIndex.{u, v} I) :=
  finiteFamilyStageObjectProperty C (stageSet s)

/-- The canonical abelian exact structure on a nested stage. -/
abbrev stageStructure (s : StageIndex.{u, v} I) :=
  abelianExactStructure (stageProperty C s).FullSubcategory

/-- The actual Q-category of a nested stage. -/
abbrev stageQ (s : StageIndex.{u, v} I) := (stageStructure C s).QCategory

/-- The literal exact inclusion associated to an inclusion of finite subsets. -/
abbrev stageTransition {s t : StageIndex.{u, v} I} (f : s ⟶ t) :=
  finiteFamilyStageExactInclusion C (leOfHom (AsSmall.down.map f))

/-- The original exact inclusion from a nested stage to the finite-support family. -/
abbrev stageLeg (s : StageIndex.{u, v} I) :=
  ObjectProperty.exactInclusion (stageProperty C s)

/-- The strict diagram of raw Q-inclusions preserving the original families. -/
def qDiagram : StageIndex.{u, v} I ⥤ Cat.{max u v, max u v} where
  obj s := Cat.of (stageQ C s)
  map f := (stageTransition C f).mapQ.toCatHom
  map_id s := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.hext (fun X => rfl) ?_
    intro X Y a
    induction a using Quotient.inductionOn with | h a => rfl
  map_comp f g := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.hext (fun X => rfl) ?_
    intro X Y a
    induction a using Quotient.inductionOn with | h a => rfl

/-- The strict cocone of actual stage Q-inclusions. -/
def qCocone : Cocone (qDiagram C) where
  pt := Cat.of (finiteCategoryExactStructure C).QCategory
  ι := {
    app s := (stageLeg C s).mapQ.toCatHom
    naturality {s t} f := by
      apply Cat.Hom.ext
      refine CategoryTheory.Functor.hext (fun X => rfl) ?_
      intro X Y a
      induction a using Quotient.inductionOn with | h a => rfl }

instance stageLeg_full (s : StageIndex.{u, v} I) : (stageLeg C s).mapQ.Full :=
  CategoryTheory.Abelian.Devissage.mapQ_full (stageProperty C s)

instance stageLeg_faithful (s : StageIndex.{u, v} I) : (stageLeg C s).mapQ.Faithful :=
  CategoryTheory.Abelian.Devissage.mapQ_faithful (stageProperty C s)

lemma stageLeg_obj_injective (s : StageIndex.{u, v} I) :
    Function.Injective (stageLeg C s).mapQ.obj := by
  intro X Y h
  cases X with | mk X =>
    cases X with | mk X =>
      cases Y with | mk Y =>
        cases Y with | mk Y =>
          have hh : X.obj = Y.obj := congrArg (fun x => x.obj.of) h
          cases X
          cases Y
          cases hh
          rfl

lemma qObjects_cover (X : (finiteCategoryExactStructure C).QCategory) :
    ∃ (s : StageIndex.{u, v} I) (Y : stageQ C s), (stageLeg C s).mapQ.obj Y = X := by
  obtain ⟨s, hs⟩ := finiteCategoryFamily_exists_stage C X.obj.of
  exact ⟨AsSmall.up.obj s, QConstruction.of _ _ ⟨X.obj.of, hs⟩, rfl⟩

/-- The actual finite-stage Q nerves have the original Q nerve as their colimit. -/
def qNerveCoconeIsColimit : IsColimit (nerveFunctor.mapCocone (qCocone C)) := by
  letI : ∀ j, (FilteredNerveColimit.leg (qDiagram C) (qCocone C) j).Full :=
    fun j => stageLeg_full C j
  letI : ∀ j, (FilteredNerveColimit.leg (qDiagram C) (qCocone C) j).Faithful :=
    fun j => stageLeg_faithful C j
  exact FilteredNerveColimit.nerveCoconeIsColimitOfFullOfInjective
    (qDiagram C) (qCocone C) (qObjects_cover C) (stageLeg_obj_injective C)

/-- A single actual zero family, present in every nested stage. -/
def commonZero (s : StageIndex.{u, v} I) : (stageProperty C s).FullSubcategory :=
  ⟨0, finiteFamilyStageObjectProperty_zero C (stageSet s)
    (isZero_zero (FiniteCategoryFamily C))⟩

/-- The Q vertex of the common zero family at a stage. -/
def commonPoint (s : StageIndex.{u, v} I) : (stageStructure C s).KSpace :=
  classifyingSpacePoint (QConstruction.of _ _ (commonZero C s))

lemma commonPoint_step {s t : StageIndex.{u, v} I} (f : s ⟶ t) :
    SSet.toTop.map ((qDiagram C ⋙ nerveFunctor).map f) (commonPoint C s) =
      commonPoint C t := by
  change classifyingSpaceMap (stageTransition C f).mapQ
    (classifyingSpacePoint (QConstruction.of _ _ (commonZero C s))) = _
  rw [classifyingSpaceMap_point]
  rfl

lemma commonPoint_leg (s : StageIndex.{u, v} I) :
    SSet.toTop.map ((nerveFunctor.mapCocone (qCocone C)).ι.app s) (commonPoint C s) =
      (finiteCategoryExactStructure C).kBasepoint := by
  change classifyingSpaceMap (stageLeg C s).mapQ
    (classifyingSpacePoint (QConstruction.of _ _ (commonZero C s))) = _
  rw [classifyingSpaceMap_point]
  rfl

/-- Every original family K-class has a representative at a common-zero stage. -/
theorem rawPiMap_jointlySurjective (n : ℕ) (a : (finiteCategoryExactStructure C).K n) :
    ∃ s : StageIndex.{u, v} I,
      ∃ b : HomotopyGroup.Pi (n + 1) (stageStructure C s).KSpace (commonPoint C s),
        piMap n (classifyingSpaceMap (stageLeg C s).mapQ).hom
          (commonPoint_leg C s) b = a := by
  exact Topology.FilteredRealization.piMap_jointlySurjective
    (qDiagram C ⋙ nerveFunctor) (nerveFunctor.mapCocone (qCocone C))
    (qNerveCoconeIsColimit C) (commonPoint C)
    (finiteCategoryExactStructure C).kBasepoint
    (fun f => commonPoint_step C f) (commonPoint_leg C) n a

/-- Equality of common-zero stage classes is detected at a later actual Q stage. -/
theorem rawPiMap_eq_eventually (s : StageIndex.{u, v} I) (n : ℕ)
    (a b : HomotopyGroup.Pi (n + 1) (stageStructure C s).KSpace (commonPoint C s))
    (h : piMap n (classifyingSpaceMap (stageLeg C s).mapQ).hom (commonPoint_leg C s) a =
      piMap n (classifyingSpaceMap (stageLeg C s).mapQ).hom (commonPoint_leg C s) b) :
    ∃ t : StageIndex.{u, v} I, ∃ f : s ⟶ t,
      piMap n (classifyingSpaceMap (stageTransition C f).mapQ).hom
        (commonPoint_step C f) a =
      piMap n (classifyingSpaceMap (stageTransition C f).mapQ).hom
        (commonPoint_step C f) b := by
  exact Topology.FilteredRealization.piMap_eq_eventually
    (qDiagram C ⋙ nerveFunctor) (nerveFunctor.mapCocone (qCocone C))
    (qNerveCoconeIsColimit C) (commonPoint C)
    (finiteCategoryExactStructure C).kBasepoint
    (fun f => commonPoint_step C f) (commonPoint_leg C) s n a b h

lemma commonZero_isZero (s : StageIndex.{u, v} I) : IsZero (commonZero C s) :=
  IsZero.of_full_of_faithful_of_isZero (stageProperty C s).ι (commonZero C s)
    (isZero_zero (FiniteCategoryFamily C))

/-- The original-category zero isomorphism fixes the stage rebasing. -/
def stageZeroIso (s : StageIndex.{u, v} I) :
    (0 : (stageProperty C s).FullSubcategory) ≅ commonZero C s :=
  (isZero_zero _).iso (commonZero_isZero C s)

/-- Its actual Q edge runs from the selected stage zero to the common vertex. -/
def stageZeroPath (s : StageIndex.{u, v} I) :
    Path (stageStructure C s).kBasepoint (commonPoint C s) :=
  classifyingSpacePath ((stageStructure C s).qIsoOfIso (stageZeroIso C s)).hom

lemma stageLeg_zeroPath (s : StageIndex.{u, v} I) :
    (stageLeg C s).qZeroBasePath =
      ((stageZeroPath C s).map (classifyingSpaceMap (stageLeg C s).mapQ).hom.continuous).cast
        rfl (commonPoint_leg C s).symm := by
  have he : (stageLeg C s).toFunctor.mapZeroObject =
      (stageLeg C s).toFunctor.mapIso (stageZeroIso C s) := by
    apply Iso.ext
    exact Subsingleton.elim _ _
  ext t
  change classifyingSpacePath
    ((finiteCategoryExactStructure C).qIsoOfIso
      (stageLeg C s).toFunctor.mapZeroObject).hom t =
    classifyingSpaceMap (stageLeg C s).mapQ
      (classifyingSpacePath ((stageStructure C s).qIsoOfIso (stageZeroIso C s)).hom t)
  rw [classifyingSpacePath_naturality]
  have hi := congrArg Iso.hom ((stageLeg C s).mapQ_qIsoOfIso (stageZeroIso C s))
  rw [show (stageLeg C s).mapQ.map
      ((stageStructure C s).qIsoOfIso (stageZeroIso C s)).hom =
      ((finiteCategoryExactStructure C).qIsoOfIso
        ((stageLeg C s).toFunctor.mapIso (stageZeroIso C s))).hom from hi]
  rw [he]

lemma stageKMap_eq_raw (s : StageIndex.{u, v} I) (n : ℕ)
    (a : (stageStructure C s).K n) :
    (stageLeg C s).KMap n a =
      piMap n (classifyingSpaceMap (stageLeg C s).mapQ).hom
        (commonPoint_leg C s) (pathTransportMulEquiv (stageZeroPath C s) n a) := by
  rw [(stageLeg C s).KMap_eq_pathTransport]
  change pathTransportMulEquiv (stageLeg C s).qZeroBasePath n
    (piMap n (classifyingSpaceMap (stageLeg C s).mapQ).hom rfl a) = _
  rw [stageLeg_zeroPath]
  change pathTransport
    (((stageZeroPath C s).map (classifyingSpaceMap (stageLeg C s).mapQ).hom.continuous).cast
      rfl (commonPoint_leg C s).symm) (n + 1)
    (HomotopyGroup.map (classifyingSpaceMap (stageLeg C s).mapQ).hom rfl a) = _
  have haux (y : (finiteCategoryExactStructure C).KSpace)
      (hy : classifyingSpaceMap (stageLeg C s).mapQ (commonPoint C s) = y) :
      pathTransport
        (((stageZeroPath C s).map (classifyingSpaceMap (stageLeg C s).mapQ).hom.continuous).cast
          rfl hy.symm) (n + 1)
        (HomotopyGroup.map (classifyingSpaceMap (stageLeg C s).mapQ).hom rfl a) =
      HomotopyGroup.map (classifyingSpaceMap (stageLeg C s).mapQ).hom hy
        (pathTransport (stageZeroPath C s) (n + 1) a) := by
    subst y
    simpa only [Path.cast_rfl_rfl] using pathTransport_naturality
      (classifyingSpaceMap (stageLeg C s).mapQ).hom (stageZeroPath C s) (n + 1) a
  exact haux _ (commonPoint_leg C s)

/-- Every class comes from a finite stage by the original normalized K-map. -/
theorem KMap_jointlySurjective (n : ℕ) (a : (finiteCategoryExactStructure C).K n) :
    ∃ s : StageIndex.{u, v} I, ∃ b : (stageStructure C s).K n,
      (stageLeg C s).KMap n b = a := by
  obtain ⟨s, b, hb⟩ := rawPiMap_jointlySurjective C n a
  refine ⟨s, (pathTransportMulEquiv (stageZeroPath C s) n).symm b, ?_⟩
  rw [stageKMap_eq_raw, MulEquiv.apply_symm_apply]
  exact hb

end CategoryTheory.Pi.FiniteSupport
