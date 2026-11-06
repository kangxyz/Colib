/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.WeakCalculus
public import Colib.Topology.HomotopyPullback.WeakCoproducts
public import Colib.Topology.HomotopyPullback.WeakPushoutDomain
public import Colib.Topology.Realization.CartesianDomainGeometry

/-!
# Weak cartesian descent on two-coefficient finite simplicial domains

A genuine coefficient morphism X → Y supplies both enriched domains over
any simplicial parameter K. Weak canonical simplex comparisons into one
fixed target assemble through the actual skeletal pushouts and coproducts.
The target coefficient Y is arbitrary; it is not replaced by a point.


Implementation provenance:
`Quillen/Topology/Realization/Cartesian/WeakDomains.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA


noncomputable section
open Topology TopCat SSet Topology.HomotopyPullback
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.Realization.CartesianDomains
open TheoremA

/-- The existing actual coefficient transformation on an enriched domain. -/
abbrev coefficientDomainMap {X Y : SSet.{u}} (r : X ⟶ Y) (K : SSet.{u}) :
    (realizedOuterProductFunctor X).obj K ⟶ (realizedOuterProductFunctor Y).obj K :=
  (realizedOuterProductCoefficientNatTrans r).app K

/-- Domain maps commute with the original coefficient transformation. -/
theorem coefficientDomainMap_naturality {X Y K L : SSet.{u}}
    (r : X ⟶ Y) (f : K ⟶ L) :
    (realizedOuterProductFunctor X).map f ≫ coefficientDomainMap r L =
      coefficientDomainMap r K ≫ (realizedOuterProductFunctor Y).map f :=
  (realizedOuterProductCoefficientNatTrans r).naturality f

variable {E T : TopCat.{u}} (q : E ⟶ T) {X Y : SSet.{u}} (r : X ⟶ Y) (K : SSet.{u})
  (s : ((realizedOuterProductFunctor Y).obj K) ⟶ T) (t : (realizedOuterProductFunctor X).obj K ⟶ E)
  (w : t ≫ q = coefficientDomainMap r K ≫ s)

include w in
/-- The exact square on a restricted simplicial domain. -/
theorem coefficientDomainMap_square {L : SSet.{u}} (f : L ⟶ K) :
    ((realizedOuterProductFunctor X).map f ≫ t) ≫ q =
      coefficientDomainMap r L ≫ ((realizedOuterProductFunctor Y).map f ≫ s) := by
  rw [Category.assoc, w, ← Category.assoc, coefficientDomainMap_naturality, Category.assoc]

/-- Every simplex characteristic chart has its prescribed canonical
comparison to the same actual target pullback. -/
def coefficientDomainChartsWeakCartesian : Prop :=
  ∀ (n : ℕ) (f : (Δ[n] : SSet.{u}) ⟶ K),
    WeakCartesian (coefficientDomainMap r Δ[n]).hom q.hom
      ((realizedOuterProductFunctor X).map f ≫ t).hom ((realizedOuterProductFunctor Y).map f ≫
        s).hom
      (congrArg TopCat.Hom.hom (coefficientDomainMap_square q r K s t w f))

/-- A map of domains inherits all the genuine simplex chart comparisons. -/
theorem coefficientDomainChartsWeakCartesian_map (h : coefficientDomainChartsWeakCartesian q r K
    s t w)
    {L : SSet.{u}} (f : L ⟶ K) :
    coefficientDomainChartsWeakCartesian q r L ((realizedOuterProductFunctor Y).map f ≫ s)
      ((realizedOuterProductFunctor X).map f ≫ t) (coefficientDomainMap_square q r K s t w f) := by
  intro n g
  have hh := h n (g ≫ f)
  simpa only [Functor.map_comp, Category.assoc] using hh

/-- Empty actual domains have an empty actual homotopy pullback. -/
theorem emptyCoefficientDomain_weakCartesian [IsEmpty ((realizedOuterProductFunctor Y).obj K)]
    [IsEmpty ((realizedOuterProductFunctor X).obj K)] :
    WeakCartesian (coefficientDomainMap r K).hom q.hom t.hom s.hom
      (congrArg TopCat.Hom.hom w) := by
  let : IsEmpty (HomotopyPullback q.hom s.hom) :=
    ⟨fun z ↦ isEmptyElim z.1.1⟩
  exact { component_surjective := fun z ↦ isEmptyElim z
          homotopy_bijective := fun x _ ↦ isEmptyElim x }

/-- Fixed-target cartesian comparisons descend through an actual simplicial
pushout after enriching its source with any fixed coefficient. -/
theorem coefficientDomainPushout_weakCartesian
    {A B C : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ K} {j : C ⟶ K}
    (sq : IsPushout f g i j)
    (hg : TopCat.HomotopyExtensionProperty ((realizedOuterProductFunctor X).map g))
    (hg' : TopCat.HomotopyExtensionProperty ((realizedOuterProductFunctor Y).map g))
    (hA : WeakCartesian (coefficientDomainMap r A).hom q.hom
      ((realizedOuterProductFunctor X).map (g ≫ j) ≫ t).hom
      ((realizedOuterProductFunctor Y).map (g ≫ j) ≫ s).hom
      (congrArg TopCat.Hom.hom (coefficientDomainMap_square q r K s t w (g ≫ j))))
    (hB : WeakCartesian (coefficientDomainMap r B).hom q.hom
      ((realizedOuterProductFunctor X).map i ≫ t).hom
      ((realizedOuterProductFunctor Y).map i ≫ s).hom
      (congrArg TopCat.Hom.hom (coefficientDomainMap_square q r K s t w i)))
    (hC : WeakCartesian (coefficientDomainMap r C).hom q.hom
      ((realizedOuterProductFunctor X).map j ≫ t).hom
      ((realizedOuterProductFunctor Y).map j ≫ s).hom
      (congrArg TopCat.Hom.hom (coefficientDomainMap_square q r K s t w j))) :
    WeakCartesian (coefficientDomainMap r K).hom q.hom t.hom s.hom
      (congrArg TopCat.Hom.hom w) := by
  have hA' : WeakCartesian (coefficientDomainMap r A).hom q.hom
      ((realizedOuterProductFunctor X).map g ≫ (realizedOuterProductFunctor X).map j ≫ t).hom
      ((realizedOuterProductFunctor Y).map g ≫ (realizedOuterProductFunctor Y).map j ≫ s).hom
      (congrArg TopCat.Hom.hom
        (CartesianDomainPushout.sourceSquare (coefficientDomainMap r A) (coefficientDomainMap r C)
          (coefficientDomainMap r K) (coefficientDomainMap_naturality r g)
          (coefficientDomainMap_naturality r j) q s t w)) := by
    simpa only [Functor.map_comp, Category.assoc] using hA
  exact CartesianDomainPushout.comparison_isWeakHomotopyEquivalence
    (sq.map (realizedOuterProductFunctor X)).flip (sq.map (realizedOuterProductFunctor Y)).flip
    (coefficientDomainMap r A) (coefficientDomainMap r C) (coefficientDomainMap r B)
    (coefficientDomainMap r K) (coefficientDomainMap_naturality r g)
    (coefficientDomainMap_naturality r f) (coefficientDomainMap_naturality r j)
    (coefficientDomainMap_naturality r i) q s t w hg hg'
    hA' hC hB

/-- Canonical comparisons on the summands descend to the actual realized
simplicial coproduct, preserving its given map into the ambient domain. -/
theorem coefficientDomainMapCoproduct_weakCartesian {ι : Type u} (L : ι → SSet.{u}) (f : (∐ L) ⟶ K)
    (h : ∀ a, WeakCartesian (coefficientDomainMap r (L a)).hom q.hom
      ((realizedOuterProductFunctor X).map (Sigma.ι L a ≫ f) ≫ t).hom
      ((realizedOuterProductFunctor Y).map (Sigma.ι L a ≫ f) ≫ s).hom
      (congrArg TopCat.Hom.hom (coefficientDomainMap_square q r K s t w (Sigma.ι L a ≫ f)))) :
    WeakCartesian (coefficientDomainMap r (∐ L)).hom q.hom
      ((realizedOuterProductFunctor X).map f ≫ t).hom
      ((realizedOuterProductFunctor Y).map f ≫ s).hom
      (congrArg TopCat.Hom.hom (coefficientDomainMap_square q r K s t w f)) := by
  apply weakCartesianCofanFixedTarget
    (fun a ↦ (realizedOuterProductFunctor X).obj (L a)) (fun a ↦ ((realizedOuterProductFunctor
      Y).obj (L a)))
    (Cofan.mk ((realizedOuterProductFunctor X).obj (∐ L))
      (fun a ↦ (realizedOuterProductFunctor X).map (Sigma.ι L a)))
    (Cofan.mk ((realizedOuterProductFunctor Y).obj (∐ L)) (fun a ↦ (realizedOuterProductFunctor
      Y).map (Sigma.ι L a)))
    (realizedOuterProductSigmaIsColimit X L) (realizedOuterProductSigmaIsColimit Y L)
    q (coefficientDomainMap r (∐ L)) ((realizedOuterProductFunctor X).map f ≫ t)
    ((realizedOuterProductFunctor Y).map f ≫ s) (coefficientDomainMap_square q r K s t w f)
    (fun a ↦ coefficientDomainMap r (L a))
    (fun a ↦ (realizedOuterProductFunctor X).map (Sigma.ι L a ≫ f) ≫ t)
    (fun a ↦ (realizedOuterProductFunctor Y).map (Sigma.ι L a ≫ f) ≫ s)
    (fun a ↦ coefficientDomainMap_square q r K s t w (Sigma.ι L a ≫ f))
  · exact fun a ↦ coefficientDomainMap_naturality r (Sigma.ι L a)
  · intro a
    change (realizedOuterProductFunctor X).map (Sigma.ι L a) ≫
      (realizedOuterProductFunctor X).map f ≫ t = _
    rw [Functor.map_comp, Category.assoc]
  · intro a
    change (realizedOuterProductFunctor Y).map (Sigma.ι L a) ≫ (realizedOuterProductFunctor
      Y).map f ≫ s = _
    rw [Functor.map_comp, Category.assoc]
  · exact h

/-- Genuine finite-dimensional simplicial-domain descent. The only
cartesian inputs are the actual characteristic-simplex comparisons into a
fixed target. Boundary comparisons are derived by dimension induction on
actual standard boundaries, including all their degenerate faces. -/
theorem finiteCoefficientDomain_weakCartesian (N : ℕ) [K.HasDimensionLT N]
    (h : coefficientDomainChartsWeakCartesian q r K s t w) :
    WeakCartesian (coefficientDomainMap r K).hom q.hom t.hom s.hom
      (congrArg TopCat.Hom.hom w) := by
  induction N generalizing K with
  | zero => exact emptyCoefficientDomain_weakCartesian q r K s t w
  | succ n ih =>
    apply coefficientDomainPushout_weakCartesian q r K s t w (finiteDomainSkeleton_isPushout K n)
      (homotopyExtensionProperty_realizedDomainCellsBoundary X K n)
      (homotopyExtensionProperty_realizedDomainCellsBoundary Y K n)
    · apply coefficientDomainMapCoproduct_weakCartesian q r K s t w
        (fun _ : DomainCell K n ↦ (∂Δ[n] : SSet.{u}))
        (domainCellsBoundaryι K n ≫ domainCellsMap K n)
      intro c
      exact ih (∂Δ[n] : SSet.{u}) _ _ _
        (coefficientDomainChartsWeakCartesian_map q r K s t w h
          (Sigma.ι (fun _ : DomainCell K n ↦ (∂Δ[n] : SSet.{u})) c ≫
            (domainCellsBoundaryι K n ≫ domainCellsMap K n)))
    · exact ih (K.skeleton n : SSet.{u}) _ _ _
        (coefficientDomainChartsWeakCartesian_map q r K s t w h (K.skeleton n).ι)
    · apply coefficientDomainMapCoproduct_weakCartesian q r K s t w
        (fun _ : DomainCell K n ↦ (Δ[n] : SSet.{u})) (domainCellsMap K n)
      intro c
      simpa only [domainCellsMap, Sigma.ι_desc] using h n c.map

end Topology.Realization.CartesianDomains
