/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Realization.Boundary
public import Colib.Topology.Realization.SimplexAttachmentFullness
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# Actual skeletal attachments and compact path reduction

Extracted from Quillen/Topology/Realization/EdgePathPresentation/Skeleton.lean,
commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual cocone maps,
relative skeleta, inclusions and hypotheses are retained. Namespace/import
ownership and the finite-simplex coordinate adapter are the only changes.
-/
@[expose] public noncomputable section
open CategoryTheory Limits Topology _root_.stdSimplex TopCat
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat

/-- The product of a discrete index space with a space is its constant coproduct. -/
def discreteProductCofan (ι : Type u) (Y : TopCat.{u}) : Cofan (fun _ : ι ↦ Y) :=
  Cofan.mk (TopCat.of ((TopCat.discrete.obj ι) × Y))
    (fun i ↦ TopCat.ofHom ⟨fun y ↦ (i, y), continuous_const.prodMk continuous_id⟩)

/-- Universal property of the explicit discrete-index product. -/
def discreteProductCofanIsColimit (ι : Type u) (Y : TopCat.{u}) :
    IsColimit (discreteProductCofan ι Y) :=
  Cofan.IsColimit.mk _
    (fun s ↦ TopCat.ofHom ⟨fun p ↦ s.inj p.1 p.2,
      continuous_prod_of_discrete_left.mpr (fun i ↦ (s.inj i).hom.continuous)⟩)
    (by intro s i; rfl)
    (by
      intro s m hm
      ext ⟨i, y⟩
      exact ConcreteCategory.congr_hom (hm i) y)

end TopCat

namespace SSet

/-- Realization of the categorical coproduct is the explicit discrete product. -/
def realizationCoproductDiscreteProductIso (ι : Type u) (Y : SSet.{u}) :
    |(∐ fun _ : ι ↦ Y)| ≅ TopCat.of ((TopCat.discrete.obj ι) × |Y|) :=
  (isColimitCofanMkObjOfIsColimit SSet.toTop (fun _ : ι ↦ Y)
    (Sigma.ι (fun _ : ι ↦ Y)) (coproductIsCoproduct _)).coconePointUniqueUpToIso
      (discreteProductCofanIsColimit ι |Y|)

@[reassoc (attr := simp)]
theorem realizationCoproductDiscreteProductIso_ι (ι : Type u) (Y : SSet.{u}) (i : ι) :
    SSet.toTop.map (Sigma.ι (fun _ : ι ↦ Y) i) ≫
        (realizationCoproductDiscreteProductIso ι Y).hom =
      (discreteProductCofan ι |Y|).inj i :=
  (isColimitCofanMkObjOfIsColimit SSet.toTop (fun _ : ι ↦ Y)
    (Sigma.ι (fun _ : ι ↦ Y)) (coproductIsCoproduct _)).comp_coconePointUniqueUpToIso_hom
      (discreteProductCofanIsColimit ι |Y|) ⟨i⟩

section RelativeSkeleton

variable {A X : SSet.{u}} (i : A ⟶ X) (n : ℕ)

/-- The discrete indexing space of nondegenerate cells attached at stage `n`. -/
abbrev skeletalCellIndex : TopCat.{u} :=
  TopCat.discrete.obj (SSet.relativeCellComplexOfMono.Cell i n)

/-- Actual realized categorical simplex coproduct in geometric coordinates. -/
def realizedSkeletalCellsIso :
    |SSet.relativeCellComplexOfMono.sigmaStdSimplex i n| ≅
      TopCat.of (skeletalCellIndex i n × _root_.stdSimplex ℝ (Fin (n + 1))) :=
  realizationCoproductDiscreteProductIso _ (Δ[n] : SSet.{u}) ≪≫
    TopCat.isoOfHomeo ((Homeomorph.refl _).prodCongr (SimplexCategory.toTopHomeo ⦋n⦌))

/-- Actual realized categorical boundary coproduct in geometric coordinates. -/
def realizedSkeletalBoundariesIso :
    |SSet.relativeCellComplexOfMono.sigmaBoundary i n| ≅
      TopCat.of (skeletalCellIndex i n × _root_.stdSimplex.boundary n) :=
  realizationCoproductDiscreteProductIso _ (∂Δ[n] : SSet.{u}) ≪≫
    TopCat.isoOfHomeo ((Homeomorph.refl _).prodCongr (realizationBoundaryHomeomorph n))

@[reassoc (attr := simp)]
theorem realizedSkeletalCellsIso_ι (a : SSet.relativeCellComplexOfMono.Cell i n) :
    SSet.toTop.map a.ιSigmaStdSimplex ≫ (realizedSkeletalCellsIso i n).hom =
      TopCat.ofHom (Y := TopCat.of (skeletalCellIndex i n × _root_.stdSimplex ℝ (Fin (n + 1))))
        ⟨fun x ↦ (a, SimplexCategory.toTopHomeo ⦋n⦌ x), by fun_prop⟩ := by
  dsimp only [realizedSkeletalCellsIso, Iso.trans_hom]
  rw [← Category.assoc, realizationCoproductDiscreteProductIso_ι]
  rfl

@[reassoc (attr := simp)]
theorem realizedSkeletalBoundariesIso_ι (a : SSet.relativeCellComplexOfMono.Cell i n) :
    SSet.toTop.map a.ιSigmaBoundary ≫ (realizedSkeletalBoundariesIso i n).hom =
      TopCat.ofHom (Y := TopCat.of (skeletalCellIndex i n × _root_.stdSimplex.boundary n))
        ⟨fun x ↦ (a, realizationBoundaryHomeomorph n x), by fun_prop⟩ := by
  dsimp only [realizedSkeletalBoundariesIso, Iso.trans_hom]
  rw [← Category.assoc, realizationCoproductDiscreteProductIso_ι]
  rfl

/-- Realizing the categorical coproduct of boundary maps gives the genuine
parameterized geometric boundary inclusion under these isomorphisms. -/
theorem realizedSkeletalBoundary_square :
    SSet.toTop.map (SSet.relativeCellComplexOfMono.l i n) ≫
        (realizedSkeletalCellsIso i n).hom =
      (realizedSkeletalBoundariesIso i n).hom ≫
        TopCat.parameterizedSimplexBoundaryInclusion (skeletalCellIndex i n) n := by
  apply (isColimitCofanMkObjOfIsColimit SSet.toTop
    (fun _ : SSet.relativeCellComplexOfMono.Cell i n ↦ (∂Δ[n] : SSet.{u}))
    (Sigma.ι _) (coproductIsCoproduct _)).hom_ext
  intro ⟨a⟩
  change SSet.toTop.map a.ιSigmaBoundary ≫ _ = SSet.toTop.map a.ιSigmaBoundary ≫ _
  rw [← Category.assoc, ← SSet.toTop.map_comp, a.ι_l, SSet.toTop.map_comp,
    Category.assoc, realizedSkeletalCellsIso_ι, realizedSkeletalBoundariesIso_ι_assoc]
  rfl

/-- The attaching map on actual geometric boundaries. -/
def realizedSkeletalAttaching :
    TopCat.of (skeletalCellIndex i n × _root_.stdSimplex.boundary n) ⟶
      |(SSet.skeletonOfMono i n : SSet.{u})| :=
  (realizedSkeletalBoundariesIso i n).inv ≫
    SSet.toTop.map (SSet.relativeCellComplexOfMono.t i n)

/-- The characteristic map on actual geometric simplices. -/
def realizedSkeletalCharacteristic :
    TopCat.of (skeletalCellIndex i n × _root_.stdSimplex ℝ (Fin (n + 1))) ⟶
      |(SSet.skeletonOfMono i (n + 1) : SSet.{u})| :=
  (realizedSkeletalCellsIso i n).inv ≫
    SSet.toTop.map (SSet.relativeCellComplexOfMono.b i n)

/-- The actual geometric cell-attachment pushout for a simplicial skeleton. -/
theorem realizedSkeletal_isPushout :
    IsPushout (TopCat.parameterizedSimplexBoundaryInclusion (skeletalCellIndex i n) n)
      (realizedSkeletalAttaching i n) (realizedSkeletalCharacteristic i n)
      (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i n)) := by
  apply ((SSet.relativeCellComplexOfMono.isPushout i n).flip.map SSet.toTop).of_iso
    (realizedSkeletalBoundariesIso i n) (realizedSkeletalCellsIso i n)
    (Iso.refl _) (Iso.refl _)
  · exact realizedSkeletalBoundary_square i n
  · simp [realizedSkeletalAttaching]
  · simp [realizedSkeletalCharacteristic]
  · simp

/-- Realization of every successor inclusion is a closed embedding. -/
theorem realizedSkeletal_transition_isClosedEmbedding :
    IsClosedEmbedding (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i n)) :=
  simplexAttachment_old_isClosedEmbedding (skeletalCellIndex i n) n
    (realizedSkeletal_isPushout i n)

/-- Cells of dimension at least two add no path generators to a skeleton. -/
theorem realizedSkeletal_transition_fundamentalGroupoid_full (hn : 2 ≤ n) :
    (FundamentalGroupoid.map
      (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i n)).hom).Full :=
  simplexAttachment_fundamentalGroupoid_full (skeletalCellIndex i n) n
    (realizedSkeletal_isPushout i n) hn

end RelativeSkeleton

end SSet
