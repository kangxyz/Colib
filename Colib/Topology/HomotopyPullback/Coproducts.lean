/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Cartesian
public import Colib.Topology.Homotopy.Equiv.Sigma
public import Mathlib.Topology.Category.TopCat.Limits.Products

/-! # Canonical cartesian comparison assembly over actual coproducts

A homotopy pullback commutes homeomorphically with coproducts in its
parameter. This uses the open coproduct summands and the compact-open path
coordinate, without imposing a discrete topology on any summand.
-/
/-! Implementation source: `Quillen/Topology/Realization/Cartesian/Coproducts.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual coproduct topologies and canonical
constant-path comparisons are retained. -/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.HomotopyPullback

variable {ι : Type u} {X A : ι → Type u} [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (A i)]

/-- The actual coproduct of a family of continuous maps, preserving indices. -/
def sigmaMap (p : ∀ i, C(X i, A i)) : C((Σ i, X i), Σ i, A i) :=
  ⟨fun z ↦ ⟨z.1, p z.1 z.2⟩, continuous_sigma fun i ↦ continuous_sigmaMk.comp (p i).continuous⟩

variable {E T : Type u} [TopologicalSpace E] [TopologicalSpace T]
  (q : C(E, T)) (s : ∀ i, C(A i, T))

/-- The canonical coproduct-parameter map on homotopy pullbacks. -/
def sigmaPullbackMap : C((Σ i, HomotopyPullback q (s i)),
    HomotopyPullback q (ContinuousMap.sigma s)) where
  toFun z := ⟨(⟨z.1, z.2.1.1⟩, z.2.1.2), z.2.2⟩
  continuous_toFun := continuous_sigma fun i ↦ by
    apply Continuous.subtype_mk
    exact (continuous_sigmaMk.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)

/-- Homotopy pullback over an arbitrary coproduct parameter is the actual
coproduct of its homotopy pullbacks, with both topologies unchanged. -/
def sigmaPullbackHomeomorph : (Σ i, HomotopyPullback q (s i)) ≃ₜ
    HomotopyPullback q (ContinuousMap.sigma s) := by
  have hind : IsInducing (sigmaPullbackMap q s) := by
    apply inducing_sigma.mpr
    constructor
    · intro i
      exact (((IsEmbedding.sigmaMk (i := i)).isInducing.prodMap IsInducing.id).comp
        (show IsInducing (Subtype.val : HomotopyPullback q (s i) → A i × (E × C(unitInterval, T)))
          from IsInducing.subtypeVal)).codRestrict
            (s := {z : (Σ i, A i) × (E × C(unitInterval, T)) |
              z.2.2 0 = q z.2.1 ∧ z.2.2 1 = (ContinuousMap.sigma s) z.1})
            (fun z ↦ z.2)
    · intro i
      refine ⟨(HomotopyPullback.baseProjection q (ContinuousMap.sigma s)) ⁻¹'
        Set.range (Sigma.mk i), isOpen_range_sigmaMk.preimage (by fun_prop), ?_⟩
      rintro ⟨j, z⟩
      change (∃ x, Sigma.mk i x = Sigma.mk j z.1.1) ↔ j = i
      constructor
      · rintro ⟨x, hx⟩
        exact (congrArg Sigma.fst hx).symm
      · intro h
        subst j
        exact ⟨z.1.1, rfl⟩
  have hinj : Function.Injective (sigmaPullbackMap q s) := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hij : i = j := congrArg (fun z : HomotopyPullback q (ContinuousMap.sigma s) ↦ z.1.1.1) h
    subst j
    have hxy : x = y := by
      apply Subtype.ext
      apply Prod.ext
      · have hb := congrArg (fun z : HomotopyPullback q (ContinuousMap.sigma s) ↦ z.1.1) h
        exact eq_of_heq (Sigma.mk.inj_iff.mp hb).2
      · exact congrArg (fun z : HomotopyPullback q (ContinuousMap.sigma s) ↦ z.1.2) h
    subst y
    rfl
  apply (IsEmbedding.mk hind hinj).toHomeomorphOfSurjective
  rintro ⟨⟨⟨i, a⟩, y⟩, hy⟩
  exact ⟨⟨i, ⟨(a, y), hy⟩⟩, rfl⟩

@[simp] theorem sigmaPullbackHomeomorph_toMap :
    (sigmaPullbackHomeomorph q s : C(_, _)) = sigmaPullbackMap q s := rfl

variable (p : ∀ i, C(X i, A i)) (t : ∀ i, C(X i, E))
  (w : ∀ i, q.comp (t i) = (s i).comp (p i))

include w in
theorem sigmaFixedSquare : q.comp (ContinuousMap.sigma t) = (ContinuousMap.sigma s).comp
    (sigmaMap p) := by
  ext z
  exact ContinuousMap.congr_fun (w z.1) z.2

/-- Canonical fixed-target homotopy-cartesian comparisons assemble over
arbitrary coproducts, without a discreteness assumption on their bases. -/
theorem cartesianSigmaFixedTarget
    (h : ∀ i, Cartesian (p i) q (t i) (s i) (w i)) :
    Cartesian (sigmaMap p) q (ContinuousMap.sigma t) (ContinuousMap.sigma s)
      (sigmaFixedSquare q s p t w) := by
  refine ⟨(ContinuousMap.sigmaHomotopyEquiv (fun i ↦ (h i).equiv)).trans
    (sigmaPullbackHomeomorph q s).toHomotopyEquiv, ?_⟩
  apply ContinuousMap.ext
  rintro ⟨i, x⟩
  change sigmaPullbackMap q s ⟨i, (h i).equiv.toFun x⟩ = _
  rw [(h i).equiv_toFun]
  rfl

section Colimits
variable {ι : Type u} (W A : ι → TopCat.{u}) (cW : Cofan W) (cA : Cofan A)
  (hW : IsColimit cW) (hA : IsColimit cA)

/-- Any actual topological coproduct has the canonical sigma coordinates. -/
def cofanHomeomorph : (Σ i, W i) ≃ₜ cW.pt :=
  TopCat.homeoOfIso ((TopCat.sigmaCofanIsColimit W).coconePointUniqueUpToIso hW)

@[simp] theorem cofanHomeomorph_apply (i : ι) (x : W i) :
    cofanHomeomorph W cW hW ⟨i, x⟩ = cW.inj i x :=
  ConcreteCategory.congr_hom ((TopCat.sigmaCofanIsColimit W).comp_coconePointUniqueUpToIso_hom
    hW ⟨i⟩) x

/-- Maps compatible with actual coproduct injections have exactly the
componentwise sigma map in their canonical coproduct coordinates. -/
theorem cofanMap_coordinates (m : cW.pt ⟶ cA.pt) (ms : ∀ i, W i ⟶ A i)
    (hm : ∀ i, cW.inj i ≫ m = ms i ≫ cA.inj i) :
    (sigmaMap (fun i ↦ (ms i).hom)).comp
        ((cofanHomeomorph W cW hW).symm : C(cW.pt, Σ i, W i)) =
      ((cofanHomeomorph A cA hA).symm : C(cA.pt, Σ i, A i)).comp m.hom := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨⟨i, x⟩, rfl⟩ := (cofanHomeomorph W cW hW).surjective z
  apply (cofanHomeomorph A cA hA).injective
  change cofanHomeomorph A cA hA (sigmaMap (fun i ↦ (ms i).hom)
    ((cofanHomeomorph W cW hW).symm (cofanHomeomorph W cW hW ⟨i, x⟩))) =
      cofanHomeomorph A cA hA ((cofanHomeomorph A cA hA).symm (m (cofanHomeomorph W cW hW ⟨i, x⟩)))
  rw [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
  change cofanHomeomorph A cA hA ⟨i, ms i x⟩ = m (cofanHomeomorph W cW hW ⟨i, x⟩)
  rw [cofanHomeomorph_apply, cofanHomeomorph_apply]
  exact (ConcreteCategory.congr_hom (hm i) x).symm

variable {E T : TopCat.{u}} (q : E ⟶ T)
  (p : cW.pt ⟶ cA.pt) (t : cW.pt ⟶ E) (s : cA.pt ⟶ T)
  (wtotal : t ≫ q = p ≫ s)
  (ps : ∀ i, W i ⟶ A i) (ts : ∀ i, W i ⟶ E) (ss : ∀ i, A i ⟶ T)
  (ws : ∀ i, ts i ≫ q = ps i ≫ ss i)
  (wp : ∀ i, cW.inj i ≫ p = ps i ≫ cA.inj i)
  (wt : ∀ i, cW.inj i ≫ t = ts i)
  (wb : ∀ i, cA.inj i ≫ s = ss i)

include hW hA wp wt wb in
/-- Fixed-target cartesian descent for arbitrary actual topological
coproduct cocones, with no preferred coordinate presentation required. -/
theorem cartesianCofanFixedTarget
    (h : ∀ i, Cartesian (ps i).hom q.hom (ts i).hom (ss i).hom (congrArg TopCat.Hom.hom (ws i))) :
    Cartesian p.hom q.hom t.hom s.hom (congrArg TopCat.Hom.hom wtotal) := by
  let eW := cofanHomeomorph W cW hW
  let eA := cofanHomeomorph A cA hA
  apply cartesianOfCoordinates p.hom q.hom t.hom s.hom (congrArg TopCat.Hom.hom wtotal)
    (sigmaMap (fun i ↦ (ps i).hom)) q.hom (ContinuousMap.sigma (fun i ↦ (ts i).hom))
    (ContinuousMap.sigma (fun i ↦ (ss i).hom))
    (sigmaFixedSquare q.hom (fun i ↦ (ss i).hom) (fun i ↦ (ps i).hom) (fun i ↦ (ts i).hom)
      (fun i ↦ congrArg TopCat.Hom.hom (ws i)))
    eW.symm (Homeomorph.refl E) eA.symm (Homeomorph.refl T)
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, x⟩, rfl⟩ := eW.surjective z
    apply eA.injective
    change eA (sigmaMap (fun i ↦ (ps i).hom) (eW.symm (eW ⟨i, x⟩))) = eA (eA.symm (p (eW ⟨i, x⟩)))
    rw [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
    change eA ⟨i, ps i x⟩ = p (eW ⟨i, x⟩)
    rw [cofanHomeomorph_apply, cofanHomeomorph_apply]
    exact (ConcreteCategory.congr_hom (wp i) x).symm
  · rfl
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, x⟩, rfl⟩ := eW.surjective z
    change (ContinuousMap.sigma (fun i ↦ (ts i).hom)) (eW.symm (eW ⟨i, x⟩)) = t (eW ⟨i, x⟩)
    rw [Homeomorph.symm_apply_apply]
    change ts i x = t (eW ⟨i, x⟩)
    rw [cofanHomeomorph_apply]
    exact (ConcreteCategory.congr_hom (wt i) x).symm
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, x⟩, rfl⟩ := eA.surjective z
    change (ContinuousMap.sigma (fun i ↦ (ss i).hom)) (eA.symm (eA ⟨i, x⟩)) = s (eA ⟨i, x⟩)
    rw [Homeomorph.symm_apply_apply]
    change ss i x = s (eA ⟨i, x⟩)
    rw [cofanHomeomorph_apply]
    exact (ConcreteCategory.congr_hom (wb i) x).symm
  · exact cartesianSigmaFixedTarget q.hom (fun i ↦ (ss i).hom) (fun i ↦ (ps i).hom)
      (fun i ↦ (ts i).hom) (fun i ↦ congrArg TopCat.Hom.hom (ws i)) h
include wtotal in
theorem cofanFixedSquare (i : ι)
    (hp : ps i ≫ cA.inj i = cW.inj i ≫ p) :
    (cW.inj i ≫ t) ≫ q = ps i ≫ cA.inj i ≫ s := by
  rw [Category.assoc, wtotal, ← Category.assoc, ← hp, Category.assoc]

include hW hA in
/-- Streamlined fixed-target assembly when each local map is the actual
restriction of the two maps on the coproduct vertices. -/
theorem cartesianCofanFixedTargetOfInclusions
    (hp : ∀ i, ps i ≫ cA.inj i = cW.inj i ≫ p)
    (h : ∀ i, Cartesian (ps i).hom q.hom (cW.inj i ≫ t).hom (cA.inj i ≫ s).hom
      (congrArg TopCat.Hom.hom (cofanFixedSquare W A cW cA q p t s wtotal ps i (hp i)))) :
    Cartesian p.hom q.hom t.hom s.hom (congrArg TopCat.Hom.hom wtotal) :=
  cartesianCofanFixedTarget W A cW cA hW hA q p t s wtotal ps
    (fun i ↦ cW.inj i ≫ t) (fun i ↦ cA.inj i ≫ s)
    (fun i ↦ cofanFixedSquare W A cW cA q p t s wtotal ps i (hp i))
    (fun i ↦ (hp i).symm) (fun _ ↦ rfl) (fun _ ↦ rfl) h

end Colimits

end Topology.HomotopyPullback
