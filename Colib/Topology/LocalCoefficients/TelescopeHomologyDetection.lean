/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FilteredTriangleHomology
public import Colib.Topology.LocalCoefficients.TelescopeTransitions
public import Colib.Topology.LocalCoefficients.FiniteTelescope
public import Colib.Topology.LocalCoefficients.FilteredHomologyElements
public import Colib.Topology.ClassifyingSpace.Naturality

/-!
Adapted from `Quillen/Topology/LocalCoefficients/TelescopeHomologyDetection.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining original transition maps.

 # Eventual vanishing under the original telescope stage maps -/

@[expose] public section

open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory
universe u
namespace CategoryTheory.Grothendieck.Telescope
open FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (F : ℕ ⥤ Cat.{u, u})

/-- The exact original stage-to-prefix triangle. -/
theorem stagePrefix_triangle (n : ℕ) :
    (classifyingSpaceMap (Grothendieck.ι F n)).hom =
      (classifyingSpaceMap (prefixInclusion F n)).hom.comp
        (classifyingSpaceMap
          (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n (Fin.last n))).hom :=
  (congrArg TopCat.Hom.hom (fiber_prefix_classifying F n (Fin.last n))).symm

/-- Include the original stage in its prefix, retaining the canonical coefficient identification. -/
def stageToPrefixHomology (n : ℕ) (A : System.{u, u} (ClassifyingSpace (Model F)))
    (k : ℕ) :=
  triangleHomologyMap
    (classifyingSpaceMap
      (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n (Fin.last n))).hom
    (classifyingSpaceMap (Grothendieck.ι F n)).hom
    (classifyingSpaceMap (prefixInclusion F n)).hom (stagePrefix_triangle F n) A k

/-- The genuine last-stage homotopy equivalence gives an actual homology isomorphism. -/
theorem stageToPrefixHomology_isIso (n : ℕ)
    (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ) :
    IsIso (stageToPrefixHomology F n A k) := by
  let := finiteTelescopeLastInclusion_isIso F n
    (pullback (classifyingSpaceMap (prefixInclusion F n)).hom A) k
  exact triangleHomologyMap_isIso _ _ _ _ _ _

/-- The specified original stabilization homotopy already takes place in the larger prefix. -/
def finiteStageTransitionClassifyingHomotopy {n m : ℕ} (h : n ≤ m) :
    ((classifyingSpaceMap (prefixTransition F h)).hom.comp
      (classifyingSpaceMap
        (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n (Fin.last n))).hom).Homotopy
    ((classifyingSpaceMap
      (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F m (Fin.last m))).hom.comp
      (classifyingSpaceMap (F.map (homOfLE h)).toFunctor).hom) := by
  simpa only [classifyingSpaceMap_comp, TopCat.hom_comp] using
    classifyingSpaceNaturalTransformationHomotopy (finiteStageTransitionNatTrans F h)

private theorem homotopy_eq_mp_apply {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f g f' g' : C(X, Y)}
    (hf : f = f') (hg : g = g') (e : f.Homotopy g = f'.Homotopy g')
    (H : f.Homotopy g) (z : unitInterval × X) : e.mp H z = H z := by
  subst f'
  subst g'
  rfl

/-- Postcomposition retains the original stabilization track and parametrization. -/
theorem finiteStageTransitionClassifyingHomotopy_infinite {n m : ℕ} (h : n ≤ m)
    (a : unitInterval) (x : ClassifyingSpace (F.obj n)) :
    stageTransitionClassifyingHomotopy F h (a, x) =
      classifyingSpaceMap (prefixInclusion F m)
        (finiteStageTransitionClassifyingHomotopy F h (a, x)) := by
  simp only [stageTransitionClassifyingHomotopy, finiteStageTransitionClassifyingHomotopy]
  rw [homotopy_eq_mp_apply rfl
    (congrArg TopCat.Hom.hom (classifyingSpaceMap_comp _ _))]
  rw [homotopy_eq_mp_apply
    (congrArg TopCat.Hom.hom (classifyingSpaceMap_comp _ _))
    (congrArg TopCat.Hom.hom (classifyingSpaceMap_comp _ _))]
  rw [← finiteStageTransitionNatTrans_infinite]
  exact classifyingSpaceNaturalTransformationHomotopy_whiskerRight _ _ _ _

/-- The strict original prefix triangle. -/
theorem prefixTransition_triangle {n m : ℕ} (h : n ≤ m) :
    (classifyingSpaceMap (prefixInclusion F n)).hom =
      (classifyingSpaceMap (prefixInclusion F m)).hom.comp
        (classifyingSpaceMap (prefixTransition F h)).hom := by
  change _ = (classifyingSpaceMap (prefixTransition F h) ≫
    classifyingSpaceMap (prefixInclusion F m)).hom
  rw [← classifyingSpaceMap_comp, prefixTransition_inclusion]

/-- Original finite-prefix transition with coefficients pulled back from the infinite model. -/
def prefixHomologyTransition {n m : ℕ} (h : n ≤ m)
    (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ) :=
  triangleHomologyMap (classifyingSpaceMap (prefixTransition F h)).hom
    (classifyingSpaceMap (prefixInclusion F n)).hom
    (classifyingSpaceMap (prefixInclusion F m)).hom (prefixTransition_triangle F h) A k

/-- The original stage transition corresponds to the genuine filtered-prefix map,
with its specified stabilization transport rather than an arbitrary coefficient isomorphism. -/
@[reassoc]
theorem stageToPrefixHomology_transition {n m : ℕ} (h : n ≤ m)
    (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ) :
    stageToPrefixHomology F n A k ≫ prefixHomologyTransition F h A k =
      stageHomologyTransition F h A k ≫ stageToPrefixHomology F m A k := by
  let i := (classifyingSpaceMap
    (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n (Fin.last n))).hom
  let j := (classifyingSpaceMap
    (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F m (Fin.last m))).hom
  let t := (classifyingSpaceMap (prefixTransition F h)).hom
  let f := (classifyingSpaceMap (F.map (homOfLE h)).toFunctor).hom
  let p := (classifyingSpaceMap (prefixInclusion F m)).hom
  let s := (classifyingSpaceMap (Grothendieck.ι F n)).hom
  let r := (classifyingSpaceMap (Grothendieck.ι F m)).hom
  have wi : s = p.comp (t.comp i) := by
    rw [← ContinuousMap.comp_assoc, ← prefixTransition_triangle F h]
    exact stagePrefix_triangle F n
  have wj : r.comp f = p.comp (j.comp f) := by
    rw [← ContinuousMap.comp_assoc, ← stagePrefix_triangle F m]
  unfold stageToPrefixHomology prefixHomologyTransition
  rw [triangleHomologyMap_comp i t _ _ p _ _ wi]
  rw [triangleHomologyMap_homotopy (finiteStageTransitionClassifyingHomotopy F h)
    s (r.comp f) p wi wj (stageTransitionClassifyingHomotopy F h)
    (finiteStageTransitionClassifyingHomotopy_infinite F h)]
  rw [← triangleHomologyMap_comp f j (r.comp f) r p rfl (stagePrefix_triangle F m) wj]
  simp only [stageHomologyTransition, stagePullbackIso, Iso.trans_hom,
    coefficientHomologyMap_comp, triangleHomologyMap, eqToHom_refl,
    coefficientHomologyMap_id, Category.id_comp, Category.assoc]
  rfl

/-- The actual filtered diagram map agrees with the original prefix triangle map. -/
theorem filteredHomology_prefix_map
    (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ)
    {n m : PrefixIndex.{u}} (a : n ⟶ m) :
    (filteredHomologyDiagram (prefixDiagram F ⋙ nerveFunctor)
      (nerveFunctor.mapCocone (prefixCocone F)) A k).map a =
      prefixHomologyTransition F (leOfHom (AsSmall.down.map a)) A k := by
  rw [filteredHomologyDiagram_map_triangle]
  rfl

/-- Vanishing in the infinite model is detected by one original sequence map,
with exactly its specified stabilization-track coefficient conversion. -/
theorem localHomology_stage_eq_zero_iff (n : ℕ)
    (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ)
    (x : homology (pullback (classifyingSpaceMap (Grothendieck.ι F n)).hom A) k) :
    pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι F n)).hom A k x = 0 ↔
      ∃ (m : ℕ) (h : n ≤ m), stageHomologyTransition F h A k x = 0 := by
  constructor
  · intro hx
    let z := stageToPrefixHomology F n A k x
    have hz : pushforwardHomologyMap (classifyingSpaceMap (prefixInclusion F n)).hom A k z = 0 := by
      change (stageToPrefixHomology F n A k ≫
        pushforwardHomologyMap (classifyingSpaceMap (prefixInclusion F n)).hom A k) x = 0
      rw [stageToPrefixHomology, triangleHomologyMap_to_target]
      exact hx
    obtain ⟨m, a, ha⟩ := (filteredHomology_eq_zero_iff
      (prefixDiagram F ⋙ nerveFunctor) (nerveFunctor.mapCocone (prefixCocone F))
      (nerveCoconeIsColimit F) A k (j := AsSmall.up.obj n) z).mp hz
    rw [filteredHomology_prefix_map] at ha
    let h : n ≤ AsSmall.down.obj m := leOfHom (AsSmall.down.map a)
    refine ⟨AsSmall.down.obj m, h, ?_⟩
    let := stageToPrefixHomology_isIso F (AsSmall.down.obj m) A k
    apply (ModuleCat.mono_iff_injective
      (stageToPrefixHomology F (AsSmall.down.obj m) A k)).mp inferInstance
    rw [map_zero]
    change (stageHomologyTransition F h A k ≫
      stageToPrefixHomology F (AsSmall.down.obj m) A k) x = 0
    rw [← stageToPrefixHomology_transition]
    exact ha
  · rintro ⟨m, h, hx⟩
    have he := congrArg (fun f ↦ f x) (stageHomologyTransition_to_infinite F h A k)
    change pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι F m)).hom A k
      (stageHomologyTransition F h A k x) = _ at he
    rw [hx, map_zero] at he
    exact he.symm

/-- Equality of two original-stage classes is likewise detected by an original later transition. -/
theorem localHomology_stage_eq_iff (n : ℕ)
    (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ)
    (x y : homology (pullback (classifyingSpaceMap (Grothendieck.ι F n)).hom A) k) :
    pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι F n)).hom A k x =
        pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι F n)).hom A k y ↔
      ∃ (m : ℕ) (h : n ≤ m), stageHomologyTransition F h A k x =
        stageHomologyTransition F h A k y := by
  simpa only [map_sub, sub_eq_zero] using localHomology_stage_eq_zero_iff F n A k (x - y)

end CategoryTheory.Grothendieck.Telescope
