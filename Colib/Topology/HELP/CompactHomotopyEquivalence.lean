/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.CompactRealizationLifting
public import Colib.Topology.Realization.Coproduct
public import Colib.Topology.Realization.HomotopyBridge
public import Colib.Topology.DeformationRetract.Basic

/-!
# Compact HELP gives actual homotopy equivalences between realizations

Mapping-path lifting over the empty inclusion gives an actual global
homotopy inverse. Lifting over the realized simplicial cylinder endpoint
monomorphism supplies its other inverse homotopy. No Whitehead theorem or
based inverse data is assumed.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HELP/CompactHomotopyEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, homotopies,
hypotheses and universes are retained; imports use native lower owners. -/
@[expose] public section

noncomputable section
open TopCat Topology SSet CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet

/-- Both endpoints of a simplicial cylinder, as an explicit coproduct map. -/
def simplicialCylinderEndpoints (X : SSet.{u}) :
    SSet.simplicialSigma (fun _ : ULift.{u} Bool ↦ X) ⟶ X ⊗ Δ[1] where
  app p := ↾fun z ↦ if z.1.down then (SSet.ι₁ (X := X)).app p z.2 else (SSet.ι₀ (X := X)).app p z.2
  naturality p q α := by
    ext ⟨⟨b⟩, x⟩ : 3
    cases b
    · exact ConcreteCategory.congr_hom (SSet.ι₀.naturality α) x
    · exact ConcreteCategory.congr_hom (SSet.ι₁.naturality α) x

@[simp]
theorem simplicialCylinderEndpoints_zero (X : SSet.{u}) :
    SSet.simplicialSigmaι (fun _ : ULift.{u} Bool ↦ X) ⟨false⟩ ≫
      simplicialCylinderEndpoints X =
      SSet.ι₀ := rfl

@[simp]
theorem simplicialCylinderEndpoints_one (X : SSet.{u}) :
    SSet.simplicialSigmaι (fun _ : ULift.{u} Bool ↦ X) ⟨true⟩ ≫
      simplicialCylinderEndpoints X =
      SSet.ι₁ := rfl

/-- The two endpoint copies are disjoint and each is simplicially embedded. -/
instance simplicialCylinderEndpoints_mono (X : SSet.{u}) : Mono (simplicialCylinderEndpoints X)
    := by
  apply (NatTrans.mono_iff_mono_app _).2
  intro p
  apply (CategoryTheory.mono_iff_injective _).2
  rintro ⟨⟨b⟩, x⟩ ⟨⟨c⟩, y⟩ h
  have hx : x = y := by cases b <;> cases c <;> exact congrArg Prod.fst h
  subst y
  have hb := congrArg (fun z : (X ⊗ Δ[1]).obj p ↦ z.2.down.toOrderHom 0) h
  cases b <;> cases c
  · rfl
  · exact False.elim (by change (0 : Fin 2) = 1 at hb; norm_num at hb)
  · exact False.elim (by change (1 : Fin 2) = 0 at hb; norm_num at hb)
  · rfl

end SSet

namespace TopCat

/-- Right lifting of a map against the realized endpoint monomorphism gives
an actual homotopy between two maps over the same fixed base map. -/
def homotopyOfRealizedEndpointLifting {E B : TopCat.{u}} (p : E ⟶ B)
    (X : SSet.{u})
    (hp : HasLiftingProperty (SSet.toTop.map (simplicialCylinderEndpoints X)) p)
    (a₀ a₁ : |X| ⟶ E) (b : |X| ⟶ B) (h₀ : a₀ ≫ p = b) (h₁ : a₁ ≫ p = b) :
    TopCat.Homotopy a₀ a₁ := by
  let a := Cofan.IsColimit.desc (SSet.realizedSigmaIsColimit (fun _ : ULift.{u} Bool
    ↦ X))
    (fun t ↦ if t.down then a₁ else a₀)
  have ha (t : ULift.{u} Bool) : SSet.toTop.map (SSet.simplicialSigmaι (fun _ :
    ULift.{u} Bool ↦ X)
    t) ≫ a =
      if t.down then a₁ else a₀ := Cofan.IsColimit.fac
        (SSet.realizedSigmaIsColimit (fun _ : ULift.{u} Bool ↦ X))
        (fun t ↦ if t.down then a₁ else a₀) t
  let q := SSet.toTop.map (fst X Δ[1]) ≫ b
  have sq : CommSq a (SSet.toTop.map (simplicialCylinderEndpoints X)) p q := by
    constructor
    apply (SSet.realizedSigmaIsColimit (fun _ : ULift.{u} Bool ↦ X)).hom_ext
    intro ⟨⟨t⟩⟩
    change SSet.toTop.map (SSet.simplicialSigmaι (fun _ : ULift.{u} Bool ↦ X) ⟨t⟩) ≫
      a ≫ p = _
    rw [← Category.assoc, ha]
    change _ = SSet.toTop.map (SSet.simplicialSigmaι (fun _ : ULift.{u} Bool ↦ X)
      ⟨t⟩) ≫
      SSet.toTop.map (simplicialCylinderEndpoints X) ≫ SSet.toTop.map (fst X Δ[1]) ≫ b
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    cases t
    · simpa using h₀
    · simpa using h₁
  letI : HasLiftingProperty (SSet.toTop.map (simplicialCylinderEndpoints X)) p := hp
  let L := sq.lift
  have hL₀ : SSet.toTop.map (SSet.ι₀ (X := X)) ≫ L = a₀ := by
    rw [← simplicialCylinderEndpoints_zero X, Functor.map_comp, Category.assoc, sq.fac_left, ha]
    simp
  have hL₁ : SSet.toTop.map (SSet.ι₁ (X := X)) ≫ L = a₁ := by
    rw [← simplicialCylinderEndpoints_one X, Functor.map_comp, Category.assoc, sq.fac_left, ha]
    simp
  exact TopCat.homotopyOfCylinder ((realizationCylinderIso X).inv ≫ L)
    (by rw [← Category.assoc, realizationCylinderIso_inv_zero, hL₀])
    (by rw [← Category.assoc, realizationCylinderIso_inv_one, hL₁])

end TopCat

namespace Topology

/-- Compact HELP is enough for an actual homotopy equivalence between
actual simplicial realizations. The forward continuous map is unchanged. -/
def homotopyEquivOfCompactHELP {X Y : SSet.{u}} (f : C(|X|, |Y|))
    (hf : CompactHomotopyExtensionLiftingProperty f) :
    ContinuousMap.HomotopyEquiv |X| |Y| := by
  let i := (⊥ : Y.Subcomplex).ι
  let a : |((⊥ : Y.Subcomplex) : SSet.{u})| ⟶ TopCat.of (MappingPath f) :=
    TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩
  let p := TopCat.ofHom (MappingPath.endpoint f)
  letI : HasLiftingProperty (SSet.toTop.map i) p :=
    MappingPath.endpoint_hasLiftingProperty_realization_mono f hf i
  have sq : CommSq a (SSet.toTop.map i) p (𝟙 |Y|) := ⟨by ext x; exact isEmptyElim x⟩
  let s := sq.lift
  have hs : s ≫ p = 𝟙 |Y| := sq.fac_right
  let g : C(|Y|, |X|) := (MappingPath.source f).comp s.hom
  let K : (f.comp g).Homotopy (ContinuousMap.id |Y|) := {
    toFun z := (s z.2).1.2 z.1
    continuous_toFun := by fun_prop
    map_zero_left x := (s x).2
    map_one_left x := ConcreteCategory.congr_hom hs x }
  let a₀ : |X| ⟶ TopCat.of (MappingPath f) := TopCat.ofHom f ≫ s
  let a₁ : |X| ⟶ TopCat.of (MappingPath f) := TopCat.ofHom (MappingPath.inclusion f)
  have h₀ : a₀ ≫ p = TopCat.ofHom f := by rw [Category.assoc, hs, Category.comp_id]
  have h₁ : a₁ ≫ p = TopCat.ofHom f := rfl
  let H := homotopyOfRealizedEndpointLifting p X
    (MappingPath.endpoint_hasLiftingProperty_realization_mono f hf (simplicialCylinderEndpoints X))
    a₀ a₁ (TopCat.ofHom f) h₀ h₁
  exact {
    toFun := f
    invFun := g
    left_inv := ⟨((ContinuousMap.Homotopy.refl (MappingPath.source f)).comp H).cast rfl rfl⟩
    right_inv := ⟨K⟩ }

@[simp]
theorem homotopyEquivOfCompactHELP_toFun {X Y : SSet.{u}} (f : C(|X|, |Y|))
    (hf : CompactHomotopyExtensionLiftingProperty f) :
    (homotopyEquivOfCompactHELP f hf).toFun = f := rfl

end Topology
