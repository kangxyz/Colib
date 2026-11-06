/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Equivalence
public import Colib.KTheory.Quillen.Map.HomotopyEquivalence
public import Colib.Topology.ClassifyingSpace.Adjunction

/-!
# Exact equivalences induce canonical K-group equivalences

Full faithfulness and essential surjectivity of the Q-functor are proved by
lifting actual admissible spans. Rebasing at zero preserves the categorical
equivalence, so its canonical K-map is the forward map of the K equivalence.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v₁ v₂ u₁ u₂ v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactFunctor
section Mixed
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- An ordinary fully faithful exact functor induces a faithful Q-functor. -/
theorem mapQ_faithful_of_fullyFaithful [F.toFunctor.Full] [F.toFunctor.Faithful] :
    F.mapQ.Faithful where
  map_injective := by
    rintro X Y ⟨s⟩ ⟨t⟩ h
    change QConstruction.mkHom _ _ (F.toQCompatibleFunctor.mapSpan s) =
      QConstruction.mkHom _ _ (F.toQCompatibleFunctor.mapSpan t) at h
    obtain ⟨e, hl, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ _ _).1 h
    apply QConstruction.mkHom_eq_of_apexIso _ _ s t (F.toFunctor.preimageIso e)
    · apply F.toFunctor.map_injective
      simpa only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage] using
        (show e.hom ≫ F.toFunctor.map t.l = F.toFunctor.map s.l from hl)
    · apply F.toFunctor.map_injective
      simpa only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage] using
        (show e.hom ≫ F.toFunctor.map t.r = F.toFunctor.map s.r from hr)

/-- An exact functor whose underlying functor is essentially surjective has
an essentially surjective Q-functor. -/
theorem mapQ_essSurj_of_essSurj [F.toFunctor.EssSurj] : F.mapQ.EssSurj where
  mem_essImage X := by
    let Y := F.toFunctor.objPreimage X.obj.of
    exact ⟨QConstruction.of _ _ Y, ⟨ED.qIsoOfIso (F.toFunctor.objObjPreimageIso X.obj.of)⟩⟩

/-- Lift a span through an equivalence that reflects the two admissibility
classes. This is a construction of its apex and legs, not a Q-level assumption. -/
def equivalenceLiftSpan [F.toFunctor.IsEquivalence]
    (hi : ∀ {X Y : C} (i : X ⟶ Y), ED.inflation (F.toFunctor.map i) → EC.inflation i)
    (hp : ∀ {X Y : C} (p : X ⟶ Y), ED.deflation (F.toFunctor.map p) → EC.deflation p)
    {X Y : C}
    (s : Span ED.deflation ED.inflation (F.toFunctor.obj X) (F.toFunctor.obj Y)) :
    Span EC.deflation EC.inflation X Y where
  apex := F.toFunctor.objPreimage s.apex
  l := F.toFunctor.preimage ((F.toFunctor.objObjPreimageIso s.apex).hom ≫ s.l)
  r := F.toFunctor.preimage ((F.toFunctor.objObjPreimageIso s.apex).hom ≫ s.r)
  wl := hp _ (by
    rw [F.toFunctor.map_preimage]
    exact ED.deflation_comp _ _ (ED.deflation_of_iso _) s.wl)
  wr := hi _ (by
    rw [F.toFunctor.map_preimage]
    exact ED.inflation_comp _ _ (ED.inflation_of_iso _) s.wr)

/-- Fullness of the Q-map follows by lifting the span apex and both legs. -/
theorem mapQ_full_of_equivalence [F.toFunctor.IsEquivalence]
    (hi : ∀ {X Y : C} (i : X ⟶ Y), ED.inflation (F.toFunctor.map i) → EC.inflation i)
    (hp : ∀ {X Y : C} (p : X ⟶ Y), ED.deflation (F.toFunctor.map p) → EC.deflation p) :
    F.mapQ.Full where
  map_surjective := by
    rintro X Y ⟨s⟩
    refine ⟨QConstruction.mkHom _ _ (F.equivalenceLiftSpan hi hp s), ?_⟩
    apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ (F.toFunctor.objObjPreimageIso s.apex)
    · exact (F.toFunctor.map_preimage _).symm
    · exact (F.toFunctor.map_preimage _).symm

/-- A genuine exact equivalence induces a categorical equivalence on Q. -/
theorem mapQ_isEquivalence_of_equivalence [F.toFunctor.IsEquivalence]
    (hi : ∀ {X Y : C} (i : X ⟶ Y), ED.inflation (F.toFunctor.map i) → EC.inflation i)
    (hp : ∀ {X Y : C} (p : X ⟶ Y), ED.deflation (F.toFunctor.map p) → EC.deflation p) :
    F.mapQ.IsEquivalence := by
  let := F.mapQ_faithful_of_fullyFaithful
  let := F.mapQ_essSurj_of_essSurj
  let := F.mapQ_full_of_equivalence hi hp
  exact { }
end Mixed

section CommonUniverse
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- Normalizing an equivalence of Q-categories at the chosen zero object
retains its genuine categorical equivalence. -/
theorem normalizedQ_isEquivalence [F.mapQ.IsEquivalence] : F.normalizedQ.IsEquivalence :=
  Functor.isEquivalence_of_iso
    (rebaseFunctorIso F.mapQ (QConstruction.of _ _ (0 : C)) (QConstruction.of _ _ (0 : D))
      (ED.qIsoOfIso F.toFunctor.mapZeroObject))

/-- The zero-normalized, original K-map of an exact equivalence is bijective. -/
theorem KMap_bijective_of_mapQ_isEquivalence [F.mapQ.IsEquivalence] (n : ℕ) :
    Function.Bijective (F.KMap n) := by
  let := F.normalizedQ_isEquivalence
  exact F.KMap_bijective_of_homotopyEquiv
    (classifyingHomotopyEquivOfIsEquivalence F.normalizedQ) rfl n

/-- The canonical K-equivalence, with exactly the original K-map forward. -/
def KEquivOfMapQIsEquivalence [F.mapQ.IsEquivalence] (n : ℕ) : EC.K n ≃* ED.K n :=
  MulEquiv.ofBijective (F.KMap n) (F.KMap_bijective_of_mapQ_isEquivalence n)

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem KEquivOfMapQIsEquivalence_coe [F.mapQ.IsEquivalence] (n : ℕ) :
    (↑(F.KEquivOfMapQIsEquivalence n) : EC.K n →* ED.K n) = F.KMap n := rfl

end CommonUniverse
end CategoryTheory.ExactCategory.ExactFunctor
