/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.CartesianProducts
public import Colib.Topology.Realization.CartesianDomainGeometry
public import Colib.Topology.HomotopyPullback.PushoutDomain
public import Colib.Topology.HomotopyPullback.Coproducts

/-!
# Cartesian descent on finite-dimensional enriched simplicial domains

The domain is an actual realized simplicial set with a fixed simplicial
coefficient. Canonical characteristic charts are tested against one fixed
target map. Their comparisons assemble along the genuine finite skeletal
pushouts.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/Realization/Cartesian/Domains.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving actual domains and structural maps. -/
@[expose] public section

open CategoryTheory.TheoremA SSet Topology Topology.HomotopyPullback TopCat


noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.Realization.CartesianDomains
open TheoremA

/-- The actual enriched-domain projection, regarded as a topological map. -/
abbrev domainProjection (X K : SSet.{u}) :
    (realizedOuterProductFunctor X).obj K ⟶ |K| :=
  SSet.toTop.map (outerProjection K X)

/-- Domain inclusions and arbitrary simplicial maps preserve the actual projection. -/
theorem domainProjection_naturality (X : SSet.{u}) {K L : SSet.{u}} (f : K ⟶ L) :
    (realizedOuterProductFunctor X).map f ≫ domainProjection X L =
      domainProjection X K ≫ SSet.toTop.map f := by
  change SSet.toTop.map _ ≫ SSet.toTop.map _ = SSet.toTop.map _ ≫ SSet.toTop.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

variable {E T : TopCat.{u}} (q : E ⟶ T) (X K : SSet.{u})
  (s : |K| ⟶ T) (t : (realizedOuterProductFunctor X).obj K ⟶ E)
  (w : t ≫ q = domainProjection X K ≫ s)

include w in
/-- The exact square on a restricted simplicial domain. -/
theorem domainMap_square {L : SSet.{u}} (f : L ⟶ K) :
    ((realizedOuterProductFunctor X).map f ≫ t) ≫ q =
      domainProjection X L ≫ (SSet.toTop.map f ≫ s) := by
  rw [Category.assoc, w, ← Category.assoc, domainProjection_naturality, Category.assoc]

/-- Every simplex characteristic chart has its prescribed canonical
comparison to the same actual target pullback. -/
def domainChartsCartesian : Prop :=
  ∀ (n : ℕ) (f : (Δ[n] : SSet.{u}) ⟶ K),
    Cartesian (domainProjection X Δ[n]).hom q.hom
      ((realizedOuterProductFunctor X).map f ≫ t).hom (SSet.toTop.map f ≫ s).hom
      (congrArg TopCat.Hom.hom (domainMap_square q X K s t w f))

/-- A map of domains inherits all the genuine simplex chart comparisons. -/
theorem domainChartsCartesian_map (h : domainChartsCartesian q X K s t w)
    {L : SSet.{u}} (f : L ⟶ K) :
    domainChartsCartesian q X L (SSet.toTop.map f ≫ s)
      ((realizedOuterProductFunctor X).map f ≫ t) (domainMap_square q X K s t w f) := by
  intro n g
  have hh := h n (g ≫ f)
  simpa only [Functor.map_comp, Category.assoc] using hh

/-- Empty actual domains have an empty actual homotopy pullback. -/
theorem emptyDomain_cartesian [IsEmpty |K|]
    [IsEmpty ((realizedOuterProductFunctor X).obj K)] :
    Cartesian (domainProjection X K).hom q.hom t.hom s.hom
      (congrArg TopCat.Hom.hom w) := by
  let : IsEmpty (HomotopyPullback q.hom s.hom) :=
    ⟨fun z ↦ isEmptyElim z.1.1⟩
  refine ⟨(Homeomorph.empty).toHomotopyEquiv, ?_⟩
  ext x
  exact isEmptyElim x

/-- Fixed-target cartesian comparisons descend through an actual simplicial
pushout after enriching its source with any fixed coefficient. -/
theorem domainPushout_cartesian
    {A B C : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ K} {j : C ⟶ K}
    (sq : IsPushout f g i j)
    (hg : TopCat.HomotopyExtensionProperty ((realizedOuterProductFunctor X).map g))
    (hg' : TopCat.HomotopyExtensionProperty (SSet.toTop.map g))
    (hA : Cartesian (domainProjection X A).hom q.hom
      ((realizedOuterProductFunctor X).map (g ≫ j) ≫ t).hom
      (SSet.toTop.map (g ≫ j) ≫ s).hom
      (congrArg TopCat.Hom.hom (domainMap_square q X K s t w (g ≫ j))))
    (hB : Cartesian (domainProjection X B).hom q.hom
      ((realizedOuterProductFunctor X).map i ≫ t).hom
      (SSet.toTop.map i ≫ s).hom
      (congrArg TopCat.Hom.hom (domainMap_square q X K s t w i)))
    (hC : Cartesian (domainProjection X C).hom q.hom
      ((realizedOuterProductFunctor X).map j ≫ t).hom
      (SSet.toTop.map j ≫ s).hom
      (congrArg TopCat.Hom.hom (domainMap_square q X K s t w j))) :
    Cartesian (domainProjection X K).hom q.hom t.hom s.hom
      (congrArg TopCat.Hom.hom w) := by
  have hA' : Cartesian (domainProjection X A).hom q.hom
      ((realizedOuterProductFunctor X).map g ≫ (realizedOuterProductFunctor X).map j ≫ t).hom
      (SSet.toTop.map g ≫ SSet.toTop.map j ≫ s).hom
      (congrArg TopCat.Hom.hom
        (CartesianDomainPushout.sourceSquare (domainProjection X A) (domainProjection X C)
          (domainProjection X K) (domainProjection_naturality X g)
          (domainProjection_naturality X j) q s t w)) := by
    simpa only [Functor.map_comp, Category.assoc] using hA
  exact ⟨CartesianDomainPushout.homotopyEquiv
    (sq.map (realizedOuterProductFunctor X)).flip (sq.map SSet.toTop).flip
    (domainProjection X A) (domainProjection X C) (domainProjection X B)
    (domainProjection X K) (domainProjection_naturality X g)
    (domainProjection_naturality X f) (domainProjection_naturality X j)
    (domainProjection_naturality X i) q s t w hg hg'
    hA'.equiv hA'.equiv_toFun hC.equiv hC.equiv_toFun hB.equiv hB.equiv_toFun, rfl⟩

/-- Canonical comparisons on the summands descend to the actual realized
simplicial coproduct, preserving its given map into the ambient domain. -/
theorem domainMapCoproduct_cartesian {ι : Type u} (L : ι → SSet.{u}) (f : (∐ L) ⟶ K)
    (h : ∀ a, Cartesian (domainProjection X (L a)).hom q.hom
      ((realizedOuterProductFunctor X).map (Sigma.ι L a ≫ f) ≫ t).hom
      (SSet.toTop.map (Sigma.ι L a ≫ f) ≫ s).hom
      (congrArg TopCat.Hom.hom (domainMap_square q X K s t w (Sigma.ι L a ≫ f)))) :
    Cartesian (domainProjection X (∐ L)).hom q.hom
      ((realizedOuterProductFunctor X).map f ≫ t).hom
      (SSet.toTop.map f ≫ s).hom
      (congrArg TopCat.Hom.hom (domainMap_square q X K s t w f)) := by
  apply cartesianCofanFixedTarget
    (fun a ↦ (realizedOuterProductFunctor X).obj (L a)) (fun a ↦ |L a|)
    (Cofan.mk ((realizedOuterProductFunctor X).obj (∐ L))
      (fun a ↦ (realizedOuterProductFunctor X).map (Sigma.ι L a)))
    (Cofan.mk |(∐ L)| (fun a ↦ SSet.toTop.map (Sigma.ι L a)))
    (realizedOuterProductSigmaIsColimit X L) (realizationDomainSigmaIsColimit L)
    q (domainProjection X (∐ L)) ((realizedOuterProductFunctor X).map f ≫ t)
    (SSet.toTop.map f ≫ s) (domainMap_square q X K s t w f)
    (fun a ↦ domainProjection X (L a))
    (fun a ↦ (realizedOuterProductFunctor X).map (Sigma.ι L a ≫ f) ≫ t)
    (fun a ↦ SSet.toTop.map (Sigma.ι L a ≫ f) ≫ s)
    (fun a ↦ domainMap_square q X K s t w (Sigma.ι L a ≫ f))
  · exact fun a ↦ domainProjection_naturality X (Sigma.ι L a)
  · intro a
    change (realizedOuterProductFunctor X).map (Sigma.ι L a) ≫
      (realizedOuterProductFunctor X).map f ≫ t = _
    rw [Functor.map_comp, Category.assoc]
  · intro a
    change SSet.toTop.map (Sigma.ι L a) ≫ SSet.toTop.map f ≫ s = _
    rw [Functor.map_comp, Category.assoc]
  · exact h

/-- Genuine finite-dimensional simplicial-domain descent. The only
cartesian inputs are the actual characteristic-simplex comparisons into a
fixed target. Boundary comparisons are derived by dimension induction on
actual standard boundaries, including all their degenerate faces. -/
theorem finiteDomain_cartesian (N : ℕ) [K.HasDimensionLT N]
    (h : domainChartsCartesian q X K s t w) :
    Cartesian (domainProjection X K).hom q.hom t.hom s.hom
      (congrArg TopCat.Hom.hom w) := by
  induction N generalizing K with
  | zero => exact emptyDomain_cartesian q X K s t w
  | succ n ih =>
    apply domainPushout_cartesian q X K s t w (finiteDomainSkeleton_isPushout K n)
      (homotopyExtensionProperty_realizedDomainCellsBoundary X K n)
      (homotopyExtensionProperty_realizationDomainCellsBoundary K n)
    · apply domainMapCoproduct_cartesian q X K s t w
        (fun _ : DomainCell K n ↦ (∂Δ[n] : SSet.{u}))
        (domainCellsBoundaryι K n ≫ domainCellsMap K n)
      intro c
      exact ih (∂Δ[n] : SSet.{u}) _ _ _
        (domainChartsCartesian_map q X K s t w h
          (Sigma.ι (fun _ : DomainCell K n ↦ (∂Δ[n] : SSet.{u})) c ≫
            (domainCellsBoundaryι K n ≫ domainCellsMap K n)))
    · exact ih (K.skeleton n : SSet.{u}) _ _ _
        (domainChartsCartesian_map q X K s t w h (K.skeleton n).ι)
    · apply domainMapCoproduct_cartesian q X K s t w
        (fun _ : DomainCell K n ↦ (Δ[n] : SSet.{u})) (domainCellsMap K n)
      intro c
      simpa only [domainCellsMap, Sigma.ι_comp_desc] using h n c.map

end Topology.Realization.CartesianDomains
