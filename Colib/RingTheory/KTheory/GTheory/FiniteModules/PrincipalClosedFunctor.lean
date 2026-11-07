/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.FGModuleCat.PrincipalClosedSupport
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.PrincipalSupport

/-!
# Small exact models of principal quotient restriction

For a commutative noetherian ring, actual quotient-ring restriction gives an exact equivalence
onto the killed objects of the supported small category, retaining the canonical support
factorization.

Adapted from `Quillen/Aglib/Algebra/Category/FGModuleCat/ClosedSupportSmallModel.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat.Localization

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (f : R)

omit [IsNoetherianRing R] in
lemma killedBy_of_iso {M N : FGModuleCat.{v} R} (e : M ≅ N) (hM : killedBy f M) :
    killedBy f N := by
  intro n
  obtain ⟨m, rfl⟩ := (FGModuleCat.isoToLinearEquiv e).surjective n
  rw [← map_smul, hM m, map_zero]

/-- The canonical small-model quotient-ring restriction, with no changed choices. -/
abbrev smallClosedFunctor : SmallModel.{u} (FGModuleCat.{v} (ClosedRing f)) ⥤
    SmallModel.{u} (FGModuleCat.{v} R) :=
  (closedRestrictionExact.{u, v} f).smallModel.toFunctor

lemma smallClosedFunctor_killed (M : SmallModel.{u} (FGModuleCat.{v} (ClosedRing f))) :
    killedBy f ((equivSmallModel (FGModuleCat.{v} R)).inverse.obj
      ((smallClosedFunctor.{u, v} f).obj M)) := by
  apply killedBy_of_iso f
    ((equivSmallModel (FGModuleCat.{v} R)).unitIso.app
      ((closedRestriction.{u, v} f).obj
        ((equivSmallModel (FGModuleCat.{v} (ClosedRing f))).inverse.obj M)))
  exact closedRestriction_killed f _

instance smallClosedFunctor_full : (smallClosedFunctor.{u, v} f).Full := by
  change (((equivSmallModel (FGModuleCat.{v} (ClosedRing f))).inverse ⋙
    closedRestriction.{u, v} f) ⋙ (equivSmallModel (FGModuleCat.{v} R)).functor).Full
  infer_instance

instance smallClosedFunctor_faithful : (smallClosedFunctor.{u, v} f).Faithful := by
  change (((equivSmallModel (FGModuleCat.{v} (ClosedRing f))).inverse ⋙
    closedRestriction.{u, v} f) ⋙ (equivSmallModel (FGModuleCat.{v} R)).functor).Faithful
  infer_instance

variable [Small.{v, u} R]

/-- The actual closed pushforward lands in modules supported on V(f). -/
def smallClosedToSupport :
    SmallModel.{u} (FGModuleCat.{v} (ClosedRing f)) ⥤ PrincipalSupport.{u, v} f :=
  ObjectProperty.lift _ (smallClosedFunctor.{u, v} f) (fun M ↦ by
    rw [supported_powers_iff]
    refine ⟨1, ?_⟩
    intro m
    simpa only [pow_one] using smallClosedFunctor_killed f M m)

/-- Its further factorization lands exactly in the killed-by-f objects. -/
def smallClosedToKilled : SmallModel.{u} (FGModuleCat.{v} (ClosedRing f)) ⥤
    (principalKilled.{u, v} f).FullSubcategory :=
  ObjectProperty.lift _ (smallClosedToSupport.{u, v} f) (fun M ↦
    (principalKilled_iff f _).2 (smallClosedFunctor_killed f M))

instance smallClosedToKilled_full : (smallClosedToKilled.{u, v} f).Full where
  map_surjective {M N} a := by
    obtain ⟨b, hb⟩ := (smallClosedFunctor.{u, v} f).map_surjective a.hom.hom
    exact ⟨b, ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ hb)⟩

instance smallClosedToKilled_faithful : (smallClosedToKilled.{u, v} f).Faithful where
  map_injective h := (smallClosedFunctor.{u, v} f).map_injective
    (congrArg (fun a ↦ a.hom.hom) h)

/-- Every killed support object comes from an actual finite quotient-ring module. -/
instance smallClosedToKilled_essSurj : (smallClosedToKilled.{u, v} f).EssSurj where
  mem_essImage M := by
    let N : (killedBy f).FullSubcategory :=
      ⟨(principalRepresentation.{u, v} f).obj M.obj, (principalKilled_iff f M.obj).1 M.property⟩
    let L := (closedEquivalence.{u, v} f).inverse.obj N
    let e : (closedRestriction.{u, v} f).obj L ≅ N.obj :=
      (killedBy f).ι.mapIso ((closedEquivalence.{u, v} f).counitIso.app N)
    let Q := (equivSmallModel (FGModuleCat.{v} (ClosedRing f)))
    let A := (equivSmallModel (FGModuleCat.{v} R))
    refine ⟨Q.functor.obj L, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact A.functor.mapIso ((closedRestriction.{u, v} f).mapIso (Q.unitIso.app L).symm ≪≫ e) ≪≫
      A.counitIso.app M.obj.obj

instance smallClosedToKilled_isEquivalence : (smallClosedToKilled.{u, v} f).IsEquivalence := {}

instance smallClosedToKilled_additive : (smallClosedToKilled.{u, v} f).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (smallClosedFunctor.{u, v} f).map_add

/-- The actual small restriction functor is an equivalence onto the killed objects. -/
def smallClosedEquivalence : SmallModel.{u} (FGModuleCat.{v} (ClosedRing f)) ≌
    (principalKilled.{u, v} f).FullSubcategory := (smallClosedToKilled.{u, v} f).asEquivalence

/-- This equivalence uses the original transported exact structure on its source. -/
def smallClosedToKilledExact :
    ExactFunctor (abelianExactStructure (FGModuleCat.{v} (ClosedRing f))).smallModel
      (abelianExactStructure (principalKilled.{u, v} f).FullSubcategory) where
  toFunctor := smallClosedToKilled.{u, v} f
  map_conflation S h := by
    rw [show (abelianExactStructure (FGModuleCat.{v} (ClosedRing f))).smallModel =
      abelianExactStructure (SmallModel.{u} (FGModuleCat.{v} (ClosedRing f))) from
      abelianExactStructure_smallModel _] at h
    exact h.map_of_exact _

instance smallClosedToKilledExact_isEquivalence :
    (smallClosedToKilledExact.{u, v} f).toFunctor.IsEquivalence :=
  smallClosedToKilled_isEquivalence f

/-- Actual closed restriction of scalars with codomain in the supported category. -/
def smallClosedToSupportExact :
    ExactFunctor (abelianExactStructure (FGModuleCat.{v} (ClosedRing f))).smallModel
      (abelianExactStructure (supported (Submonoid.powers f)).FullSubcategory) :=
  (smallClosedToKilledExact.{u, v} f).comp
    (CategoryTheory.ObjectProperty.exactInclusion (principalKilled.{u, v} f))

end FGModuleCat.Localization
