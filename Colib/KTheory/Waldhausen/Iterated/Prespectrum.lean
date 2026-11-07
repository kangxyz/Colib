/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Stages
public import Colib.KTheory.Waldhausen.Iterated.Functoriality
public import Colib.KTheory.Waldhausen.AsSmall.Basic
public import Colib.Topology.Prespectrum.Loop

/-!
# The genuine sequential Waldhausen S-prespectrum

Every finite simplicial stage is realized, with the original cylinder giving its continuous
based loop structure map. These maps assemble into an actual functor on zero-preserving exact
functors. The zero space is literally the loop space of the first S-realization; the accepted
small-model comparison identifies its homotopy sets with the original K-groups and retains
the original K-map. In positive zero-space degree this is a group isomorphism.

This is a prespectrum construction. No assertion that its higher structure maps are weak
equivalences, no spectrum-level localization theorem, and no nonconnective Bass tower is made.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/Prespectrum.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, assumptions,
chosen zero objects and universe parameters are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
  MonoidalCategory SSet Topology
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory

/-- The realization of the specified iterated S-construction stage. -/
def stageSpace (r : ℕ) (W : WideSubcategory preservesZero.{u}) : TopCat.{u} :=
  SSet.toTop.obj ((stages r).obj W)
/-- The realized zero-object vertex of the iterated stage. -/
def stagePoint (r : ℕ) (W : WideSubcategory preservesZero.{u}) : stageSpace r W :=
  realizationPoint (stageVertex r W)

/-- The based simplicial self-homotopy of the next-stage constant zero map. -/
def stageHomotopy (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    SSet.Homotopy (SSet.const (X := (stages r).obj W) (stageVertex (r+1) W))
      (SSet.const (X := (stages r).obj W) (stageVertex (r+1) W)) where
  h := stageCylinder r W
  h₀ := by ext n A : 4; exact stageCylinder_endpoint r W n A 0
  h₁ := by ext n A : 4; exact stageCylinder_endpoint r W n A 1
  rel := by ext n z; exact z.1.property.elim

/-- Actual continuous loop structure maps in every degree, with both endpoints proved. -/
def stageLoopMap (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    C(stageSpace r W, Path (stagePoint (r+1) W) (stagePoint (r+1) W)) where
  toFun x :=
    { toFun t := realizationSimplicialHomotopy (stageHomotopy r W) (t,x)
      continuous_toFun := (realizationSimplicialHomotopy (stageHomotopy r W)).continuous.comp
        (continuous_id.prodMk continuous_const)
      source' := ((realizationSimplicialHomotopy (stageHomotopy r W)).apply_zero x).trans
        (realization_const_apply _ x)
      target' := ((realizationSimplicialHomotopy (stageHomotopy r W)).apply_one x).trans
        (realization_const_apply _ x) }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (realizationSimplicialHomotopy (stageHomotopy r W)).continuous.comp
      (continuous_snd.prodMk continuous_fst)

lemma stageLoopMap_point (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    stageLoopMap r W (stagePoint r W) = Path.refl (stagePoint (r+1) W) := by
  ext t
  exact realizationSimplicialHomotopy_fixed_vertex (stageHomotopy r W)
    (stageVertex r W) (stageVertex (r+1) W) (stageCylinder_fixed_vertex r W) t

lemma stageMap_point (r : ℕ) {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    SSet.toTop.map ((stages r).map F) (stagePoint r V) = stagePoint r W := by
  change SSet.toTop.map ((stages r).map F) (realizationPoint (stageVertex r V)) = _
  rw [realizationPoint_naturality]
  exact congrArg realizationPoint (stageVertex_naturality r F)

lemma stageLoopMap_naturality (r : ℕ) {V W : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (x : stageSpace r V) :
    basedLoopMap (SSet.toTop.map ((stages (r+1)).map F)).hom (stageMap_point (r+1) F)
      (stageLoopMap r V x) = stageLoopMap r W (SSet.toTop.map ((stages r).map F) x) := by
  ext t
  exact realizationSimplicialHomotopy_square (stageHomotopy r V) (stageHomotopy r W)
    ((stages r).map F) ((stages (r+1)).map F) (stageCylinder_naturality r F).symm t x

/-- The genuine sequential prespectrum built from all finite S-constructions.
Its zero space is the original loop K-space. No structure map is declared an equivalence. -/
def prespectrum (W : WideSubcategory preservesZero.{u}) : LoopPrespectrum.{u} where
  space n := Nat.casesOn n (TopCat.of (Path (stagePoint 0 W) (stagePoint 0 W)))
    (fun r ↦ stageSpace r W)
  point n := by
    cases n with
    | zero => exact Path.refl (stagePoint 0 W)
    | succ r => exact stagePoint r W
  structureMap n := by
    cases n with
    | zero => exact ContinuousMap.id _
    | succ r => exact stageLoopMap r W
  map_point n := by
    cases n with
    | zero => rfl
    | succ r => exact stageLoopMap_point r W

/-- Every original zero-preserving exact functor gives an actual prespectrum map. -/
def prespectrumMap {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    (prespectrum V).Hom (prespectrum W) where
  map n := Nat.casesOn n
    (basedLoopMap (SSet.toTop.map ((stages 0).map F)).hom (stageMap_point 0 F))
    (fun r ↦ (SSet.toTop.map ((stages r).map F)).hom)
  map_point n := by
    cases n with
    | zero => exact basedLoopMap_refl _ _
    | succ r => exact stageMap_point r F
  comm n x := by
    cases n with
    | zero => ext t; rfl
    | succ r => exact stageLoopMap_naturality r F x

/-- The original independently constructed first loop map is unchanged. -/
lemma stageLoopMap_zero (W : WideSubcategory preservesZero.{u}) :
    stageLoopMap 0 W = loopStructureMap W.obj.waldhausen := rfl

/-- The zero-space homotopy sets recover the original K-groups by actual loop currying. -/
def zeroSpaceHomotopyEquiv (W : WideSubcategory preservesZero.{u}) (n : ℕ) :
    W.obj.waldhausen.K n ≃ HomotopyGroup.Pi n ((prespectrum W).space 0) ((prespectrum W).point 0) :=
  loopShiftEquiv n

/-- The complete constructed prespectrum is an actual functor on the original
zero-preserving exact category. -/
def prespectrumFunctor : WideSubcategory preservesZero.{u} ⥤ LoopPrespectrum.{u} where
  obj := prespectrum
  map := prespectrumMap
  map_id W := by
    apply LoopPrespectrum.Hom.ext
    funext n
    cases n with
    | zero =>
      change basedLoopMap (SSet.toTop.map ((stages 0).map (𝟙 W))).hom (stageMap_point 0 (𝟙 W)) =
        ContinuousMap.id _
      ext x t
      change SSet.toTop.map ((stages 0).map (𝟙 W)) (x t) = x t
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl
    | succ r =>
      change (SSet.toTop.map ((stages r).map (𝟙 W))).hom = ContinuousMap.id _
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl
  map_comp F G := by
    apply LoopPrespectrum.Hom.ext
    funext n
    cases n with
    | zero =>
      change basedLoopMap (SSet.toTop.map ((stages 0).map (F ≫ G))).hom (stageMap_point 0 (F ≫ G)) =
        (basedLoopMap (SSet.toTop.map ((stages 0).map G)).hom (stageMap_point 0 G)).comp
          (basedLoopMap (SSet.toTop.map ((stages 0).map F)).hom (stageMap_point 0 F))
      ext x t
      change SSet.toTop.map ((stages 0).map (F ≫ G)) (x t) = _
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      rfl
    | succ r =>
      change (SSet.toTop.map ((stages r).map (F ≫ G))).hom =
        (SSet.toTop.map ((stages r).map G)).hom.comp (SSet.toTop.map ((stages r).map F)).hom
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      rfl

section OriginalUniverses
universe u₀ v₀
variable {C : Type u₀} [Category.{v₀} C] (W : Structure C)

/-- Original categories in independent universes use the proved genuine small model. -/
def originalPrespectrum : LoopPrespectrum.{max u₀ v₀} := prespectrum (asSmallCategory W)

/-- Its zero-space homotopy sets are identified with the unchanged original K-groups. -/
def originalZeroSpaceEquiv (n : ℕ) :
    W.K n ≃ HomotopyGroup.Pi n ((originalPrespectrum W).space 0) ((originalPrespectrum W).point
      0) :=
  (W.asSmallKEquiv n).toEquiv.trans (zeroSpaceHomotopyEquiv (asSmallCategory W) n)

/-- In positive zero-space degree the same comparison preserves the actual group law. -/
def originalZeroSpaceMulEquiv (n : ℕ) :
    W.K (n+1) ≃* HomotopyGroup.Pi (n+1)
      ((originalPrespectrum W).space 0) ((originalPrespectrum W).point 0) :=
  (W.asSmallKEquiv (n+1)).trans (loopShiftMulEquiv n)

variable {D : Type u₀} [Category.{v₀} D] (V : Structure D) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F) (h0 : F.obj W.zero = V.zero)

/-- The original exact functor is lifted through the actual small-model equivalences. -/
def asSmallCategoryMap : asSmallCategory W ⟶ asSmallCategory V :=
  ⟨⟨asSmallFunctor F, hF.asSmall⟩, congrArg AsSmall.up.obj h0⟩

/-- The original categories have a genuine spectrum-level precursor map. -/
def originalPrespectrumMap : originalPrespectrum W ⟶ originalPrespectrum V :=
  prespectrumMap (asSmallCategoryMap W V hF h0)

lemma originalZeroSpaceEquiv_naturality (n : ℕ) (a : W.K n) :
    originalZeroSpaceEquiv V n (KMap hF n a) =
      HomotopyGroup.map ((originalPrespectrumMap W V hF h0).map 0)
        ((originalPrespectrumMap W V hF h0).map_point 0) (originalZeroSpaceEquiv W n a) := by
  have h := DFunLike.congr_fun (asSmallKEquiv_naturality_of_zeroEq hF h0 n) a
  change V.asSmallKEquiv n (KMap hF n a) =
    KMap hF.asSmall n (W.asSmallKEquiv n a) at h
  change loopShiftEquiv n (V.asSmallKEquiv n (KMap hF n a)) = _
  rw [h, KMap_eq_piMap_of_zeroEq hF.asSmall (congrArg AsSmall.up.obj h0)]
  exact loopShiftEquiv_natural n (deloopingMap hF.asSmall).hom
    (stageMap_point 0 (asSmallCategoryMap W V hF h0)) (W.asSmallKEquiv n a)
end OriginalUniverses

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0276"]
  CategoryTheory.Waldhausen.IteratedS.prespectrumFunctor
  CategoryTheory.Waldhausen.IteratedS.originalZeroSpaceEquiv
  CategoryTheory.Waldhausen.IteratedS.originalZeroSpaceMulEquiv
  CategoryTheory.Waldhausen.IteratedS.originalZeroSpaceEquiv_naturality

attribute [colib_tag "COL-0276",
  colib_ref "ThomasonTrobaugh1990" "Section 1.5.3, p. 260" "background"
    "Iterated S-construction background; no Omega-equivalence is asserted here"]
  CategoryTheory.Waldhausen.IteratedS.originalPrespectrum
