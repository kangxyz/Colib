/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionProjection
public import Colib.CategoryTheory.ExactCategory.ExtensionCartesianPredicate
public import Colib.CategoryTheory.GroupCompletion.Monomorphisms

/-!
Implementation provenance:
`Quillen/KTheory/Plus/ProjectiveExtensionCartesian.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Cartesian lifts in the actual localized extension category -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
attribute [local instance] MonoidalLeftAction.trivial extensionProjectionLinear
attribute [local instance] extensionPairProjectionLinear

/-- An original extension arrow with its projective denominator fixed. -/
def localizedExtensionOriginalHom (A : IsoCategory R)
    {x y : (exactStructure R).ExtensionTotal} (f : x ⟶ y) :
    localizedExtensionPair R A x ⟶ localizedExtensionPair R A y :=
  GroupCompletion.ActionLocalization.ofHom
    (C := IsoCategory R) (D := IsoCategory R × (exactStructure R).ExtensionTotal)
    (X := (A, x)) (Y := (A, y)) (𝟙 A, f)

@[simp]
theorem localizedExtensionProjection_originalHom (A : IsoCategory R)
    {x y : (exactStructure R).ExtensionTotal} (f : x ⟶ y) :
    (localizedExtensionProjection R).map (localizedExtensionOriginalHom R A f) =
      (exactStructure R).extensionProjectionQMap f := by
  dsimp only [localizedExtensionProjection, localizedExtensionOriginalHom, Functor.comp_map]
  rw [GroupCompletion.ActionLocalization.mapFunctor_ofHom,
    GroupCompletion.ActionLocalization.TrivialAction.forgetFunctor_map_ofHom]
  rfl

instance localizedExtensionOriginalHom_mono (A : IsoCategory R)
    {x y : (exactStructure R).ExtensionTotal} (f : x ⟶ y) :
    Mono (localizedExtensionOriginalHom R A f) := by
  change Mono (GroupCompletion.ActionLocalization.ofHom
    (C := IsoCategory R) (D := IsoCategory R × (exactStructure R).ExtensionTotal)
    (X := (A, x)) (Y := (A, y)) (𝟙 A, f))
  let : Mono f := (exactStructure R).extensionHom_mono f
  let m : ((A, x) : IsoCategory R × (exactStructure R).ExtensionTotal) ⟶ (A, y) :=
    (𝟙 A, f)
  let : Mono m := by
    constructor
    intro Z g h w
    change (g.1 ≫ 𝟙 A, g.2 ≫ f) = (h.1 ≫ 𝟙 A, h.2 ≫ f) at w
    exact Prod.ext (by simpa using congrArg _root_.Prod.fst w)
      ((cancel_mono f).1 (congrArg _root_.Prod.snd w))
  exact GroupCompletion.ActionLocalization.ofHom_mono m

/-- Original cartesian lifts remain cartesian after simultaneous localization.
The proof uses the actual denominator representatives and their quotient relation. -/
theorem existsUnique_localizedExtensionFactor (A : IsoCategory R)
    {x y : (exactStructure R).ExtensionTotal} (f : x ⟶ y)
    (z : LocalizedExtensionCategory R)
    (g : z ⟶ localizedExtensionPair R A y)
    (w : (localizedExtensionProjection R).obj z ⟶
      (localizedExtensionProjection R).obj (localizedExtensionPair R A x))
    (hw : (localizedExtensionProjection R).map g =
      w ≫ (localizedExtensionProjection R).map (localizedExtensionOriginalHom R A f)) :
    ∃! h : z ⟶ localizedExtensionPair R A x,
      (localizedExtensionProjection R).map h = w ∧
        h ≫ localizedExtensionOriginalHom R A f = g := by
  obtain ⟨r, rfl⟩ := Quotient.exists_rep g
  let e := (exactStructure R).qIsoOfIso
    (directSumExtensionQuotientIso R r.denom z.obj.2)
  change e.inv ≫ (exactStructure R).extensionProjectionQMap r.map.2 = _ at hw
  rw [localizedExtensionProjection_originalHom] at hw
  have hw' : (exactStructure R).extensionProjectionQMap r.map.2 =
      (e.hom ≫ w) ≫ (exactStructure R).extensionProjectionQMap f := by
    rw [Category.assoc, ← hw]
    simp
  obtain ⟨k, hk, _⟩ := (exactStructure R).existsUnique_extensionFactor f r.map.2 (e.hom ≫ w) hw'
  let h : z ⟶ localizedExtensionPair R A x :=
    GroupCompletion.ActionLocalization.mkHom ⟨r.denom, (r.map.1, k)⟩
  have hp : (localizedExtensionProjection R).map h = w := by
    change e.inv ≫ (exactStructure R).extensionProjectionQMap k = w
    rw [hk.1]
    simp
  have hc : h ≫ localizedExtensionOriginalHom R A f =
      GroupCompletion.ActionLocalization.mkHom r := by
    change GroupCompletion.ActionLocalization.mkHom _ ≫
      GroupCompletion.ActionLocalization.ofHom
        (C := IsoCategory R) (D := IsoCategory R × (exactStructure R).ExtensionTotal)
        (X := (A, x)) (Y := (A, y)) (𝟙 A, f) = _
    rw [GroupCompletion.ActionLocalization.mkHom_comp_ofHom]
    apply congrArg GroupCompletion.ActionLocalization.mkHom
    change GroupCompletion.ActionLocalization.HomRep.mk r.denom
      (r.map.1 ≫ 𝟙 A, k ≫ f) = r
    rw [Category.comp_id, hk.2]
    rfl
  refine ⟨h, ⟨hp, hc⟩, ?_⟩
  intro h' hh'
  exact (cancel_mono (localizedExtensionOriginalHom R A f)).1 (hh'.2.trans hc.symm)

/-- The selected original-arrow lifts satisfy the standard strong cartesian predicate. -/
instance localizedExtensionOriginalHom_stronglyCartesian (A : IsoCategory R)
    {x y : (exactStructure R).ExtensionTotal} (f : x ⟶ y) :
    (localizedExtensionProjection R).IsStronglyCartesian
      ((localizedExtensionProjection R).map (localizedExtensionOriginalHom R A f))
      (localizedExtensionOriginalHom R A f) where
  universal_property' {z} w g _ := by
    have hw := (IsHomLift.eq_of_isHomLift (localizedExtensionProjection R)
      (w ≫ (localizedExtensionProjection R).map (localizedExtensionOriginalHom R A f)) g).symm
    obtain ⟨h, hh, hu⟩ := existsUnique_localizedExtensionFactor R A f z g w hw
    refine ⟨h, ⟨?_, hh.2⟩, ?_⟩
    · rw [← hh.1]
      exact IsHomLift.map (localizedExtensionProjection R) h
    · intro h' hh'
      let := hh'.1
      exact hu h' ⟨(IsHomLift.eq_of_isHomLift (localizedExtensionProjection R) w h').symm,
        hh'.2⟩

/-- Every original-Q arrow has a strong cartesian lift in the actual localized
extension category, with the chosen source identified by an explicit isomorphism. -/
theorem exists_localizedExtensionLift (y : LocalizedExtensionCategory R)
    (b : QConstruction (exactStructure R).deflation (exactStructure R).inflation)
    (g : b ⟶ (localizedExtensionProjection R).obj y) :
    ∃ (x : LocalizedExtensionCategory R)
      (e : b ≅ (localizedExtensionProjection R).obj x) (f : x ⟶ y),
      e.hom ≫ (localizedExtensionProjection R).map f = g ∧
        (localizedExtensionProjection R).IsStronglyCartesian
          ((localizedExtensionProjection R).map f) f := by
  obtain ⟨X⟩ := b
  obtain ⟨x, e, f, hf⟩ := (exactStructure R).exists_extensionLift y.obj.2 g
  refine ⟨localizedExtensionPair R y.obj.1 x, ((exactStructure R).qIsoOfIso e).symm,
    localizedExtensionOriginalHom R y.obj.1 f, ?_, inferInstance⟩
  rw [localizedExtensionProjection_originalHom, hf]
  simp

end ModuleCat.FiniteProjective
