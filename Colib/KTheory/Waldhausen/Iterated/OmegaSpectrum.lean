/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.FiberComparison
public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.RelativeTime
public import Colib.Topology.HomotopyFiber.CylinderComparison
public import Colib.Topology.HomotopyFiber.ContractibleSource
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceHomotopy
public import Colib.Topology.Prespectrum.Omega

/-!
# The actual Waldhausen Omega-spectrum

Every canonical higher cylinder lifts into the genuine contractible added-initial-row path
object. Its tail is literally the original stage cylinder. The explicit remaining-path
homotopy identifies loop inclusion composed with that exact structure map with the proved
original total-fiber comparison. Cancellation proves complete weakness of every unchanged
structure map. These proofs enhance the existing exact-functor prespectrum to a genuine
Omega-spectrum functor, with its original small-model and independent-universe interfaces.

This constructs the connective S-spectrum. It does not construct the Bass nonconnective
tower, polynomial/Laurent fundamental theorem, or negative K-groups.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/OmegaSpectrum.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps,
complete weak-equivalence statements, fiber paths and independent original universes are
  retained. -/
@[expose] public section

open CategoryTheory.TheoremA
open CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.Fibration.RelativeRows



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
  SSet Topology
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory
open Fibration Fibration.RelativeRows TheoremA

/-- The augmented row insertion indexed by the simplicial time map. -/
def rowTime (W : WideSubcategory preservesZero.{u}) {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    W ⟶ (rows (addInitial.obj n)).obj W := (insertion (relativeTime τ)).app W

lemma rowTime_reindex (W : WideSubcategory preservesZero.{u}) {m n : SimplexCategory} (α : m ⟶ n)
  (τ : n ⟶ ⦋1⦌) :
    rowTime W (α ≫ τ) = rowTime W τ ≫ (rowsReindex (addInitial.map α)).app W := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  change suspensionRow W.obj.waldhausen (relativeTime (α ≫ τ)) =
    suspensionRow W.obj.waldhausen (relativeTime τ) ⋙ QuotientRows.reindex W.obj.waldhausen
      (addInitial.map α)
  rw [← suspensionRow_reindex, relativeTime_reindex]

lemma rowTime_tail (W : WideSubcategory preservesZero.{u}) {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    rowTime W τ ≫ rowTail W n = (insertion τ).app W := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  change suspensionRow W.obj.waldhausen (relativeTime τ) ⋙
    QuotientRows.reindex W.obj.waldhausen (tail.app n) = suspensionRow W.obj.waldhausen τ
  rw [← suspensionRow_reindex, relativeTime_tail]

lemma rowTime_zero (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    rowTime W (n.const ⦋1⦌ 0) = zeroHom W ((rows (addInitial.obj n)).obj W) := by
  unfold rowTime
  rw [relativeTime_zero]
  exact insertion_const W (addInitial.obj n) 0

lemma rowTime_one (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) : rowTime W
  (n.const ⦋1⦌ 1) = rowFiber W
    n := rfl

/-- This is the actual lift of every original iterated-S cylinder, including its time parameter. -/
def stageRelativeCylinder (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    (stages r).obj W ⊗ Δ[1] ⟶ diagonalSSet (pathDiagram W ⋙ stages r) where
  app n := ↾fun z ↦ ((stages r).map (rowTime W z.2.down)).app n z.1
  naturality n m α := by
    ext z : 3
    change ((stages r).map (rowTime W (α.unop ≫ z.2.down))).app m
      (((stages r).obj W).map α z.1) =
      ((stages r).obj ((rows (addInitial.obj m.unop)).obj W)).map α
        (((stages r).map ((rowsReindex (addInitial.map α.unop)).app W)).app n
          (((stages r).map (rowTime W z.2.down)).app n z.1))
    rw [rowTime_reindex, CategoryTheory.Functor.map_comp]
    exact ConcreteCategory.congr_hom
      (((stages r).map (rowTime W z.2.down) ≫
        (stages r).map ((rowsReindex (addInitial.map α.unop)).app W)).naturality α) z.1

/-- The zero vertex of the diagonal stage path diagram. -/
def stagePathVertex (r : ℕ) (W : WideSubcategory preservesZero.{u}) : (diagonalSSet (pathDiagram
  W ⋙ stages r)).obj (op
    ⦋0⦌) :=
  stageVertex r ((rows (addInitial.obj ⦋0⦌)).obj W)

/-- The realization of the zero vertex in the stage path diagram. -/
def stagePathPoint (r : ℕ) (W : WideSubcategory preservesZero.{u}) : |diagonalSSet (pathDiagram W
  ⋙ stages r)| :=
  realizationPoint (stagePathVertex r W)

lemma stageRelativeCylinder_zero (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    SSet.ι₀ ≫ stageRelativeCylinder r W = SSet.const (stagePathVertex r W) := by
  ext n A : 4
  change ((stages r).map (rowTime W (n.unop.const ⦋1⦌ 0))).app n A =
    ((stages r).obj ((rows (addInitial.obj n.unop)).obj W)).map (n.unop.const ⦋0⦌ 0).op
      (((stages r).map ((rowsReindex (addInitial.map (n.unop.const ⦋0⦌ 0))).app W)).app (op ⦋0⦌)
        (stageVertex r ((rows (addInitial.obj ⦋0⦌)).obj W)))
  rw [rowTime_zero]
  erw [stages_map_zeroHom]
  rw [stageVertex_naturality]
  rfl

lemma stageRelativeCylinder_one (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    SSet.ι₁ ≫ stageRelativeCylinder r W = stageTotalFiberInclusion r W := by
  ext n A : 4
  rfl

lemma stageRelativeCylinder_tail (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    stageRelativeCylinder r W ≫ diagonalMap (stagePathProjection r W) = stageCylinder r W := by
  ext n z : 4
  have h := congrArg (fun f ↦ ((stages r).map f).app n) (rowTime_tail W z.2.down)
  rw [CategoryTheory.Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h z.1

lemma stageTotalTailMap_point (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    stageTotalTailMap r W (stagePathPoint r W) = stagePoint (r+1) W := by
  change SSet.toTop.map (diagonalMap (stagePathProjection r W))
    (realizationPoint (stagePathVertex r W)) = _
  rw [realizationPoint_naturality]
  exact congrArg realizationPoint (stageVertex_naturality r (rowTail W ⦋0⦌))

/-- The simplicial homotopy from the constant zero map to the total stage-fiber inclusion. -/
def stageRelativeHomotopy (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    SSet.Homotopy (SSet.const (X := (stages r).obj W) (stagePathVertex r W))
      (stageTotalFiberInclusion r W) where
  h := stageRelativeCylinder r W
  h₀ := stageRelativeCylinder_zero r W
  h₁ := stageRelativeCylinder_one r W
  rel := by ext n z; exact z.1.property.elim

/-- The realized homotopy from the constant zero map to the total stage-fiber inclusion. -/
def stageRelativeTopHomotopy (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    (ContinuousMap.const (stageSpace r W) (stagePathPoint r W)).Homotopy
      (SSet.toTop.map (stageTotalFiberInclusion r W)).hom where
  toContinuousMap := (realizationSimplicialHomotopy (stageRelativeHomotopy r W)).toContinuousMap
  map_zero_left x := ((realizationSimplicialHomotopy (stageRelativeHomotopy r W)).apply_zero
    x).trans
    (realization_const_apply _ x)
  map_one_left x := (realizationSimplicialHomotopy (stageRelativeHomotopy r W)).apply_one x

lemma stageCylinderLoop_eq (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    HomotopyFiber.cylinderLoop (stageTotalTailMap r W) (stagePoint (r+1) W)
      (stagePathPoint r W) (stageTotalTailMap_point r W)
      (SSet.toTop.map (stageTotalFiberInclusion r W)).hom
      (stageTotalTailMap_fiberInclusion r W) (stageRelativeTopHomotopy r W) = stageLoopMap r W := by
  ext x t
  change SSet.toTop.map (diagonalMap (stagePathProjection r W))
      (realizationSimplicialHomotopy (stageRelativeHomotopy r W) (t,x)) =
    realizationSimplicialHomotopy (stageHomotopy r W) (t,x)
  have h := realizationSimplicialHomotopy_square (stageRelativeHomotopy r W) (stageHomotopy r W)
    (𝟙 _) (diagonalMap (stagePathProjection r W)) (by
      change stageRelativeCylinder r W ≫ diagonalMap (stagePathProjection r W) =
        (𝟙 _ ▷ Δ[1]) ≫ stageCylinder r W
      simpa using stageRelativeCylinder_tail r W) t x
  simp only [CategoryTheory.Functor.map_id, TopCat.id_app] at h
  exact h

/-- Every specific constructed higher structure map is a complete weak equivalence. -/
theorem stageLoopMap_weak (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
  IsWeakHomotopyEquivalence (stageLoopMap r W)
    := by
  let := pathStage_contractible r W
  have H := HomotopyFiber.cylinderFiberHomotopy (stageTotalTailMap r W) (stagePoint (r+1) W)
    (stagePathPoint r W) (stageTotalTailMap_point r W)
    (SSet.toTop.map (stageTotalFiberInclusion r W)).hom
    (stageTotalTailMap_fiberInclusion r W) (stageRelativeTopHomotopy r W)
  rw [stageCylinderLoop_eq] at H
  have hc := (stageTotalFiberComparison_weak r W).of_homotopy H.symm
  have hi := isWeakHomotopyEquivalence_of_homotopyEquiv
    (HomotopyFiber.loopInclusionEquivOfContractibleSource (stageTotalTailMap r W)
      (stagePoint (r+1) W) (stagePathPoint r W) (stageTotalTailMap_point r W))
  rw [HomotopyFiber.loopInclusionEquivOfContractibleSource_toFun] at hi
  exact hc.of_comp_right hi

universe v

/-- The constructed S-prespectrum is an Omega-prespectrum, for its unchanged original maps. -/
theorem prespectrum_isOmega (W : WideSubcategory preservesZero.{u}) : (prespectrum W).IsOmega := by
  intro n
  cases n with
  | zero => exact isWeakHomotopyEquivalence_id _
  | succ r => exact stageLoopMap_weak r W

/-- Independent original universes retain the same actual small-model prespectrum. -/
theorem originalPrespectrum_isOmega {C : Type u} [Category.{v} C] (W : Structure C) :
    (originalPrespectrum W).IsOmega := prespectrum_isOmega (asSmallCategory W)

/-- Actual exact zero-preserving functors act on the constructed Omega-spectrum. -/
def omegaSpectrumFunctor : WideSubcategory preservesZero.{u} ⥤ LoopPrespectrum.OmegaSpectrum.{u} :=
  ObjectProperty.lift (LoopPrespectrum.IsOmega : ObjectProperty LoopPrespectrum.{u})
    prespectrumFunctor
    prespectrum_isOmega

/-- The spectrum belonging to an original category in independent universes. -/
def originalOmegaSpectrum {C : Type u} [Category.{v} C] (W : Structure C) :
    LoopPrespectrum.OmegaSpectrum.{max u v} := ⟨originalPrespectrum W,
      originalPrespectrum_isOmega W⟩

/-- The original exact-functor map is unchanged by the proved Omega-spectrum enhancement. -/
def originalOmegaSpectrumMap {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) {F : C ⥤ D}
    (hF : IsExact W.cof W.weq V.cof V.weq F) (h0 : F.obj W.zero = V.zero) :
    originalOmegaSpectrum W ⟶ originalOmegaSpectrum V :=
  ObjectProperty.homMk (originalPrespectrumMap W V hF h0)


end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0282",
  colib_ref "ThomasonTrobaugh1990" "Section 1.5.3, p. 260" "background"
    "The actual iterated S-construction has weakly equivalent loop structure maps"]
  CategoryTheory.Waldhausen.IteratedS.stageLoopMap_weak

attribute [colib_tag "COL-0282"]
  CategoryTheory.Waldhausen.IteratedS.prespectrum_isOmega
  CategoryTheory.Waldhausen.IteratedS.originalPrespectrum_isOmega
  CategoryTheory.Waldhausen.IteratedS.omegaSpectrumFunctor
  CategoryTheory.Waldhausen.IteratedS.originalOmegaSpectrum
  CategoryTheory.Waldhausen.IteratedS.originalOmegaSpectrumMap
