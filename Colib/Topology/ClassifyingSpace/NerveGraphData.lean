/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.CharacteristicPoints
public import Colib.Topology.ClassifyingSpace.GroupoidCompletion
public import Colib.Topology.Realization.GraphAttachmentAnchors

/-!
# Original categorical data in the actual nerve graph attachment

The first nonempty skeletal attachment of a nerve has its original object
vertices and its original nondegenerate arrow cells. These define the canonical
vertex and edge data for the actual geometric pushout, with no path-generation
or presentation assumption.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/ClassifyingSpace/NerveGraphData.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, endpoint equalities,
path classes and independent universe parameters are retained. Native namespace
ownership and the established finite-simplex adapter replace source ownership.
-/
@[expose] public section

open Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Convexity Convexity.StdSimplex SSet TopCat
open scoped Simplicial Topology unitInterval
universe u v w
namespace CategoryTheory.NerveGraphData
attribute [local instance] Localization.groupoid
variable (C : Type u) [Category.{v} C]

/-- The actual empty-subcomplex inclusion into the original nerve. -/
abbrev emptyMap := (⊥ : (nerve C).Subcomplex).ι

/-- The actual nondegenerate one-cell index space. -/
abbrev Index : TopCat.{max u v} := skeletalCellIndex (emptyMap C) 1

/-- The actual relative zero-dimensional stage. -/
abbrev Old : TopCat.{max u v} :=
  |(SSet.skeletonOfMono (emptyMap C) 1 : SSet.{max u v})|

/-- The actual relative one-dimensional stage. -/
abbrev Stage : TopCat.{max u v} :=
  |(SSet.skeletonOfMono (emptyMap C) 2 : SSet.{max u v})|

/-- Its original boundary attachment. -/
abbrev attaching := realizedSkeletalAttaching (emptyMap C) 1

/-- Its original cell characteristic map. -/
abbrev characteristic := realizedSkeletalCharacteristic (emptyMap C) 1

/-- Its original old-stage inclusion. -/
abbrev transition := SSet.toTop.map (SSet.relativeCellComplexOfMono.r (emptyMap C) 1)

/-- Its genuine geometric pushout square. -/
theorem pushout : IsPushout (parameterizedSimplexBoundaryInclusion (Index C) 1)
    (attaching C) (characteristic C) (transition C) :=
  realizedSkeletal_isPushout (emptyMap C) 1

/-- Its original inclusion into the full classifying space. -/
def inclusion : C(Stage C, ClassifyingSpace C) :=
  (SSet.toTop.map (SSet.skeletonOfMono (emptyMap C) 2).ι).hom

/-- The actual old stage is the discrete original object space. -/
def oldHomeomorph : Old C ≃ₜ TopCat.discrete.obj C :=
  (TopCat.homeoOfIso (realizedSkeletonStageIso (nerve C) 1)).trans
    nerveZeroSkeletonHomeomorph

instance old_discreteTopology : DiscreteTopology (Old C) :=
  (oldHomeomorph C).isEmbedding.discreteTopology

/-- The original object represented by an actual old-stage point. -/
def oldObject (x : Old C) : C := oldHomeomorph C x

/-- The original point formula for every old-stage point. -/
theorem oldObject_point (x : Old C) :
    classifyingSpacePoint (oldObject C x) = inclusion C (transition C x) := by
  have hp : nerveZeroSkeletonPoint (oldObject C x) =
      (realizedSkeletonStageIso (nerve C) 1).hom x := by
    apply (nerveZeroSkeletonHomeomorph (C := C)).injective
    rw [nerveZeroSkeletonHomeomorph_point]
    rfl
  have hs := congrArg (SSet.toTop.map ((nerve C).skeleton 1).ι) hp
  rw [nerveZeroSkeletonPoint_inclusion] at hs
  have hi := ConcreteCategory.congr_hom (realizedSkeletonStageIso_hom_ι (nerve C) 1) x
  refine hs.trans (hi.trans ?_)
  change SSet.toTop.map (SSet.skeletonOfMono (emptyMap C) 1).ι x =
    (SSet.toTop.map (SSet.relativeCellComplexOfMono.r (emptyMap C) 1) ≫
      SSet.toTop.map (SSet.skeletonOfMono (emptyMap C) 2).ι) x
  rw [← Functor.map_comp]
  rfl

/-- The original localization object represented by an old-stage point. -/
def vertex (x : Old C) : (⊤ : MorphismProperty C).Localization :=
  (⊤ : MorphismProperty C).Q.obj (oldObject C x)

@[simp] theorem oldObject_oldHomeomorph_symm (c : C) :
    oldObject C ((oldHomeomorph C).symm c) = c :=
  (oldHomeomorph C).apply_symm_apply c

@[simp] theorem vertex_oldHomeomorph_symm (c : C) :
    vertex C ((oldHomeomorph C).symm c) = (⊤ : MorphismProperty C).Q.obj c :=
  congrArg (⊤ : MorphismProperty C).Q.obj (oldObject_oldHomeomorph_symm C c)

@[simp] theorem inclusion_transition_oldHomeomorph_symm (c : C) :
    inclusion C (transition C ((oldHomeomorph C).symm c)) = classifyingSpacePoint c := by
  simpa only [oldObject_oldHomeomorph_symm] using
    (oldObject_point C ((oldHomeomorph C).symm c)).symm

/-- Actual old-stage points match the original completion comparison on objects. -/
def vertexIdentification (x : Old C) :
    (classifyingGroupoidCompletionFunctor C).obj (vertex C x) ≅
      FundamentalGroupoid.mk (inclusion C (transition C x)) :=
  eqToIso (congrArg FundamentalGroupoid.mk (oldObject_point C x))

/-- The geometric coordinate of the original realized interval parameter. -/
lemma realizationInterval_geometric (t : unitInterval) :
    FiniteSimplexAdapter.toTopHomeomorph ⦋1⦌ (realizationInterval.{w} t) =
      StdSimplex.homeomorphI.symm t := by
  apply StdSimplex.homeomorphI.injective
  rw [Homeomorph.apply_symm_apply]
  have h := FiniteSimplexAdapter.realization_interval_compat (realizationInterval.{w} t)
  have hi : SSet.stdSimplex.toTopObjIsoI.hom (realizationInterval.{w} t) = ULift.up t :=
    ConcreteCategory.congr_hom SSet.stdSimplex.toTopObjIsoI.inv_hom_id _
  exact congrArg ULift.down (h.trans hi)

/-- Each full characteristic map is the original arrow path at every parameter. -/
theorem characteristic_path (a : Index C) (t : unitInterval) :
    inclusion C (characteristic C (a, StdSimplex.homeomorphI.symm t)) =
      classifyingSpacePath (a.simplex.map' 0 1) t := by
  have h := realizedNerveOneCell_original_path a t
  rw [realizationInterval_geometric.{max u v}] at h
  exact h

/-- Actual source boundary attachment retains the original source object. -/
theorem oldObject_source (a : Index C) :
    oldObject C (attaching C (a, boundaryZero)) = a.simplex.obj 0 := by
  apply classifyingSpacePoint_injective
  rw [oldObject_point]
  have hw := congrArg (inclusion C) (ConcreteCategory.congr_hom (pushout C).w
    (a, boundaryZero))
  have hs : inclusion C (characteristic C (a, StdSimplex.single 0)) =
      classifyingSpacePoint (a.simplex.obj 0) := by
    have h := realizedNerveOneCell_original_source a
    rw [realizationInterval_geometric.{max u v}, StdSimplex.homeomorphI_symm_zero] at h
    exact h
  change inclusion C (characteristic C (a, StdSimplex.single 0)) =
    inclusion C (transition C (attaching C (a, boundaryZero))) at hw
  exact hw.symm.trans hs

/-- Actual target boundary attachment retains the original target object. -/
theorem oldObject_target (a : Index C) :
    oldObject C (attaching C (a, boundaryOne)) = a.simplex.obj 1 := by
  apply classifyingSpacePoint_injective
  rw [oldObject_point]
  have hw := congrArg (inclusion C) (ConcreteCategory.congr_hom (pushout C).w
    (a, boundaryOne))
  have hs : inclusion C (characteristic C (a, StdSimplex.single 1)) =
      classifyingSpacePoint (a.simplex.obj 1) := by
    have h := realizedNerveOneCell_original_target a
    rw [realizationInterval_geometric.{max u v}, StdSimplex.homeomorphI_symm_one] at h
    exact h
  change inclusion C (characteristic C (a, StdSimplex.single 1)) =
    inclusion C (transition C (attaching C (a, boundaryOne))) at hw
  exact hw.symm.trans hs

/-- The original categorical edge, with exactly its actual attached endpoint objects. -/
def originalEdge (a : Index C) :
    oldObject C (attaching C (a, boundaryZero)) ⟶
      oldObject C (attaching C (a, boundaryOne)) :=
  eqToHom (oldObject_source C a) ≫ a.simplex.map' 0 1 ≫ eqToHom (oldObject_target C a).symm

/-- The corresponding original edge in the genuine groupoid localization. -/
def edge (a : Index C) :
    vertex C (attaching C (a, boundaryZero)) ⟶ vertex C (attaching C (a, boundaryOne)) :=
  (⊤ : MorphismProperty C).Q.map (originalEdge C a)

/-- The canonical traversal of the geometric one-simplex. -/
def intervalPath : Path (StdSimplex.single (0 : Fin 2) : StdSimplex ℝ (Fin 2))
    (StdSimplex.single 1) where
  toFun t := StdSimplex.homeomorphI.symm t
  continuous_toFun := StdSimplex.homeomorphI.symm.continuous
  source' := StdSimplex.homeomorphI_symm_zero
  target' := StdSimplex.homeomorphI_symm_one

/-- The actual boundary point equality underlying the graph vertex isomorphism. -/
theorem vertexPoint (a : Index C) (b : simplexBoundary 1) :
    classifyingSpacePoint (oldObject C (attaching C (a, b))) =
      inclusion C (characteristic C (a, b.1)) :=
  (oldObject_point C (attaching C (a, b))).trans
    (congrArg (inclusion C) (ConcreteCategory.congr_hom (pushout C).w (a, b))).symm

/-- The graph vertex isomorphism is the equality of the actual original points. -/
theorem vertexIso_hom (a : Index C) (b : simplexBoundary 1) :
    (GraphAttachment.vertexIso (Index C) (pushout C) (inclusion C)
      (classifyingGroupoidCompletionFunctor C) (vertex C) (vertexIdentification C) a b).hom =
        eqToHom (congrArg FundamentalGroupoid.mk (vertexPoint C a b)) := by
  simp only [GraphAttachment.vertexIso, vertexIdentification, Iso.trans_hom,
    eqToIso.hom, eqToHom_trans]

/-- The genuine localization edge maps to the actual original categorical edge class. -/
theorem edge_image (a : Index C) :
    (classifyingGroupoidCompletionFunctor C).map (edge C a) =
      (classifyingFundamentalGroupoidFunctor C).map (originalEdge C a) := by
  simpa only [edge, Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
    Functor.congr_hom (toClassifyingGroupoidCompletionFunctor C) (originalEdge C a)

/-- Changing categorical endpoints has exactly the original path-class endpoint transport. -/
theorem originalEdge_image (a : Index C) :
    (classifyingFundamentalGroupoidFunctor C).map (originalEdge C a) =
      (Path.Homotopic.Quotient.mk (classifyingSpacePath (a.simplex.map' 0 1))).cast
        (congrArg classifyingSpacePoint (oldObject_source C a))
        (congrArg classifyingSpacePoint (oldObject_target C a)) := by
  simp only [originalEdge, Functor.map_comp, eqToHom_map]
  exact FundamentalGroupoid.conj_eqToHom
    (congrArg classifyingSpacePoint (oldObject_source C a))
    (congrArg classifyingSpacePoint (oldObject_target C a))

/-- The actual full geometric edge class, with original endpoint transport,
is the original categorical edge class. -/
theorem cell_path_class (a : Index C) :
    eqToHom (congrArg FundamentalGroupoid.mk (vertexPoint C a boundaryZero)) ≫
      (⟦(PathConnectedSpace.somePath (StdSimplex.single (0 : Fin 2))
          (StdSimplex.single 1)).map
        ((inclusion C).comp (simplexAttachmentCellMap (Index C) 1
          (g := characteristic C) a)).continuous⟧ :
        FundamentalGroupoid.mk (inclusion C (characteristic C (a, StdSimplex.single 0))) ⟶
          FundamentalGroupoid.mk (inclusion C (characteristic C (a, StdSimplex.single 1)))) ≫
      eqToHom (congrArg FundamentalGroupoid.mk (vertexPoint C a boundaryOne).symm) =
        (classifyingFundamentalGroupoidFunctor C).map (originalEdge C a) := by
  let k := (inclusion C).comp (simplexAttachmentCellMap (Index C) 1
    (g := characteristic C) a)
  have hq : Path.Homotopic.Quotient.mk
      ((PathConnectedSpace.somePath (StdSimplex.single (0 : Fin 2))
        (StdSimplex.single 1)).map k.continuous) =
      Path.Homotopic.Quotient.mk (intervalPath.map k.continuous) :=
    _root_.Quotient.sound ((Convexity.StdSimplex.paths_homotopic _ intervalPath).map k)
  change eqToHom (congrArg FundamentalGroupoid.mk (vertexPoint C a boundaryZero)) ≫
    Path.Homotopic.Quotient.mk
      ((PathConnectedSpace.somePath (StdSimplex.single (0 : Fin 2))
        (StdSimplex.single 1)).map k.continuous) ≫
    eqToHom (congrArg FundamentalGroupoid.mk (vertexPoint C a boundaryOne).symm) = _
  rw [hq, FundamentalGroupoid.conj_eqToHom
    (vertexPoint C a boundaryZero) (vertexPoint C a boundaryOne), originalEdge_image]
  change Path.Homotopic.Quotient.mk ((intervalPath.map k.continuous).cast
    (vertexPoint C a boundaryZero) (vertexPoint C a boundaryOne)) =
    Path.Homotopic.Quotient.mk ((classifyingSpacePath (a.simplex.map' 0 1)).cast
      (congrArg classifyingSpacePoint (oldObject_source C a))
      (congrArg classifyingSpacePoint (oldObject_target C a)))
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact characteristic_path C a t

/-- The source spoke across each whole actual edge agrees with the original
localization arrow, with the actual target vertex isomorphism. -/
theorem edge_spoke (a : Index C) :
    GraphAttachment.spoke (Index C) (pushout C) (inclusion C)
      (classifyingGroupoidCompletionFunctor C) (vertex C) (vertexIdentification C) a
        (StdSimplex.single 1) =
      (classifyingGroupoidCompletionFunctor C).map (edge C a) ≫
        (GraphAttachment.vertexIso (Index C) (pushout C) (inclusion C)
          (classifyingGroupoidCompletionFunctor C) (vertex C) (vertexIdentification C) a
            boundaryOne).hom := by
  dsimp only [GraphAttachment.spoke]
  rw [vertexIso_hom, vertexIso_hom, edge_image]
  change eqToHom (congrArg FundamentalGroupoid.mk (vertexPoint C a boundaryZero)) ≫
    (⟦(PathConnectedSpace.somePath (StdSimplex.single (0 : Fin 2))
        (StdSimplex.single 1)).map
      ((inclusion C).comp (simplexAttachmentCellMap (Index C) 1
        (g := characteristic C) a)).continuous⟧ :
      FundamentalGroupoid.mk (inclusion C (characteristic C (a, StdSimplex.single 0))) ⟶
        FundamentalGroupoid.mk (inclusion C (characteristic C (a, StdSimplex.single 1)))) =
    (classifyingFundamentalGroupoidFunctor C).map (originalEdge C a) ≫
      eqToHom (congrArg FundamentalGroupoid.mk (vertexPoint C a boundaryOne))
  apply (cancel_mono (eqToHom
    (congrArg FundamentalGroupoid.mk (vertexPoint C a boundaryOne).symm))).mp
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
    cell_path_class C a

end CategoryTheory.NerveGraphData
