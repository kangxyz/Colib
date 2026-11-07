/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.PathHomotopy
public import Colib.Topology.Realization.ZeroSkeleton
public import Colib.Topology.ClassifyingSpace.CharacteristicPoints
public import Colib.Topology.Realization.GraphAttachmentFullness

/-! # The actual graph attachment of an arbitrary simplicial set

The actual zero-skeleton is the discrete original vertex set. The actual
one-cells are the original nondegenerate simplices, and their characteristic
paths are exactly the original realized edges, with unchanged endpoints.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/Realization/EdgePathPresentation/SimplicialGraph.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, vertex and edge
identifications, path classes, proofs and universe parameters are retained.
Native namespace ownership and the pinned standard simplex replace source ownership.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Convexity Convexity.StdSimplex Topology TopCat
open scoped Simplicial Topology unitInterval
universe u v w
namespace SSet

/-- Distinct original vertices remain distinct points of the actual realization. -/
theorem realizationPoint_injective (X : SSet.{u}) :
    Function.Injective (realizationPoint (X := X)) := by
  intro x y h
  have hs : zeroSkeletonPoint X x = zeroSkeletonPoint X y :=
    (realization_skeleton_isClosedEmbedding X 1).injective
      ((zeroSkeletonPoint_inclusion X x).trans (h.trans
        (zeroSkeletonPoint_inclusion X y).symm))
  have he := congrArg (zeroSkeletonHomeomorph X) hs
  simpa only [zeroSkeletonHomeomorph, TopCat.homeoOfIso_apply,
    zeroSkeletonRealizationIso_point] using he

namespace SimplicialGraph
variable (X : SSet.{u})

/-- The original empty-subcomplex inclusion. -/
abbrev emptyMap := (⊥ : X.Subcomplex).ι
/-- The actual nondegenerate one-cell index space. -/
abbrev Index : TopCat.{u} := skeletalCellIndex (emptyMap X) 1
/-- The actual relative zero-dimensional stage. -/
abbrev Old : TopCat.{u} := |(SSet.skeletonOfMono (emptyMap X) 1 : SSet.{u})|
/-- The actual relative one-dimensional stage. -/
abbrev Stage : TopCat.{u} := |(SSet.skeletonOfMono (emptyMap X) 2 : SSet.{u})|
/-- The original boundary attachment. -/
abbrev attaching := realizedSkeletalAttaching (emptyMap X) 1
/-- The original cell characteristic map. -/
abbrev characteristic := realizedSkeletalCharacteristic (emptyMap X) 1
/-- The original old-stage inclusion. -/
abbrev transition := SSet.toTop.map (SSet.relativeCellComplexOfMono.r (emptyMap X) 1)

/-- The genuine geometric pushout square. -/
theorem pushout : IsPushout (parameterizedSimplexBoundaryInclusion (Index X) 1)
    (attaching X) (characteristic X) (transition X) := realizedSkeletal_isPushout (emptyMap X) 1

/-- The original inclusion into the full realization. -/
def inclusion : C(Stage X, |X|) :=
  (SSet.toTop.map (SSet.skeletonOfMono (emptyMap X) 2).ι).hom

/-- The actual old stage is the discrete original vertex set. -/
def oldHomeomorph : Old X ≃ₜ TopCat.discrete.obj (X _⦋0⦌) :=
  (TopCat.homeoOfIso (realizedSkeletonStageIso X 1)).trans (zeroSkeletonHomeomorph X)

instance old_discreteTopology : DiscreteTopology (Old X) :=
  (oldHomeomorph X).isEmbedding.discreteTopology

/-- The original vertex represented by an actual old-stage point. -/
def oldVertex (x : Old X) : X _⦋0⦌ := oldHomeomorph X x

/-- The actual point formula for every old-stage point. -/
theorem oldVertex_point (x : Old X) :
    realizationPoint (oldVertex X x) = inclusion X (transition X x) := by
  have hp : zeroSkeletonPoint X (oldVertex X x) = (realizedSkeletonStageIso X 1).hom x := by
    apply (zeroSkeletonHomeomorph X).injective
    change (zeroSkeletonRealizationIso X).hom (zeroSkeletonPoint X (oldVertex X x)) = _
    rw [zeroSkeletonRealizationIso_point]
    rfl
  have hs := congrArg (SSet.toTop.map (X.skeleton 1).ι) hp
  rw [zeroSkeletonPoint_inclusion] at hs
  have hi := ConcreteCategory.congr_hom (realizedSkeletonStageIso_hom_ι X 1) x
  refine hs.trans (hi.trans ?_)
  change SSet.toTop.map (SSet.skeletonOfMono (emptyMap X) 1).ι x =
    (SSet.toTop.map (SSet.relativeCellComplexOfMono.r (emptyMap X) 1) ≫
      SSet.toTop.map (SSet.skeletonOfMono (emptyMap X) 2).ι) x
  rw [← Functor.map_comp]
  rfl

@[simp] theorem oldVertex_oldHomeomorph_symm (x : X _⦋0⦌) :
    oldVertex X ((oldHomeomorph X).symm x) = x := (oldHomeomorph X).apply_symm_apply x

/-- An original one-simplex as an edge with its original face vertices. -/
def simplexEdge (a : Index X) : X.Edge (X.δ 1 a.simplex) (X.δ 0 a.simplex) :=
  ⟨a.simplex, rfl, rfl⟩

/-- The geometric coordinate of the original realized interval parameter. -/
lemma realizationInterval_geometric (t : unitInterval) :
    SimplexCategory.toTopHomeo ⦋1⦌ (realizationInterval.{u} t) =
      StdSimplex.homeomorphI.symm t := by
  apply StdSimplex.homeomorphI.injective
  rw [Homeomorph.apply_symm_apply]
  have hi : SSet.stdSimplex.toTopObjIsoI.hom (realizationInterval.{u} t) = ULift.up t :=
    ConcreteCategory.congr_hom SSet.stdSimplex.toTopObjIsoI.inv_hom_id _
  exact congrArg ULift.down hi

/-- The characteristic traversal is the exact original simplex path. -/
theorem characteristic_path (a : Index X) (t : unitInterval) :
    inclusion X (characteristic X (a, StdSimplex.homeomorphI.symm t)) =
      realizationEdgePath (simplexEdge X a) t := by
  have h := realizedSkeletalCharacteristic_inclusion (emptyMap X) 1 a
    (realizationInterval.{u} t)
  rw [realizationInterval_geometric] at h
  exact h

/-- Original attached source vertices retain their exact simplicial faces. -/
theorem oldVertex_source (a : Index X) :
    oldVertex X (attaching X (a, boundaryZero)) = X.δ 1 a.simplex := by
  apply realizationPoint_injective X
  rw [oldVertex_point]
  have hw := congrArg (inclusion X) (ConcreteCategory.congr_hom (pushout X).w
    (a, boundaryZero))
  have hs : inclusion X (characteristic X (a, StdSimplex.single 0)) =
      realizationPoint (X.δ 1 a.simplex) := by
    have h := characteristic_path X a 0
    rw [StdSimplex.homeomorphI_symm_zero] at h
    exact h.trans (realizationEdgePath (simplexEdge X a)).source
  exact hw.symm.trans hs

/-- Original attached target vertices retain their exact simplicial faces. -/
theorem oldVertex_target (a : Index X) :
    oldVertex X (attaching X (a, boundaryOne)) = X.δ 0 a.simplex := by
  apply realizationPoint_injective X
  rw [oldVertex_point]
  have hw := congrArg (inclusion X) (ConcreteCategory.congr_hom (pushout X).w
    (a, boundaryOne))
  have hs : inclusion X (characteristic X (a, StdSimplex.single 1)) =
      realizationPoint (X.δ 0 a.simplex) := by
    have h := characteristic_path X a 1
    rw [StdSimplex.homeomorphI_symm_one] at h
    exact h.trans (realizationEdgePath (simplexEdge X a)).target
  exact hw.symm.trans hs

/-- The original simplex with precisely its original attached endpoint vertices. -/
def originalEdge (a : Index X) :
    X.Edge (oldVertex X (attaching X (a, boundaryZero)))
      (oldVertex X (attaching X (a, boundaryOne))) where
  edge := a.simplex
  src_eq := (oldVertex_source X a).symm
  tgt_eq := (oldVertex_target X a).symm

/-- The genuine boundary identification as an equality of original realization points. -/
theorem vertexPoint (a : Index X) (b : Convexity.StdSimplex.boundary 1) :
    realizationPoint (oldVertex X (attaching X (a, b))) =
      inclusion X (characteristic X (a, b.1)) :=
  (oldVertex_point X (attaching X (a, b))).trans
    (congrArg (inclusion X) (ConcreteCategory.congr_hom (pushout X).w (a, b))).symm

/-- The canonical traversal of the actual geometric interval. -/
def intervalPath : Path (StdSimplex.single (0 : Fin 2) : StdSimplex ℝ (Fin 2))
    (StdSimplex.single 1) where
  toFun t := StdSimplex.homeomorphI.symm t
  continuous_toFun := StdSimplex.homeomorphI.symm.continuous
  source' := StdSimplex.homeomorphI_symm_zero
  target' := StdSimplex.homeomorphI_symm_one

/-- The actual full cell path agrees with its original simplicial edge, including endpoints. -/
theorem cell_path_class (a : Index X) :
    eqToHom (congrArg FundamentalGroupoid.mk (vertexPoint X a boundaryZero)) ≫
      (⟦(PathConnectedSpace.somePath (StdSimplex.single (0 : Fin 2))
          (StdSimplex.single 1)).map
        ((inclusion X).comp (simplexAttachmentCellMap (Index X) 1
          (g := characteristic X) a)).continuous⟧ :
        FundamentalGroupoid.mk (inclusion X (characteristic X (a, StdSimplex.single 0))) ⟶
          FundamentalGroupoid.mk (inclusion X (characteristic X (a, StdSimplex.single 1)))) ≫
      eqToHom (congrArg FundamentalGroupoid.mk
        (vertexPoint X a boundaryOne).symm) =
        (⟦realizationEdgePath (originalEdge X a)⟧ :
          FundamentalGroupoid.mk
            (realizationPoint (oldVertex X (attaching X (a, boundaryZero)))) ⟶
          FundamentalGroupoid.mk
            (realizationPoint (oldVertex X (attaching X (a, boundaryOne))))) := by
  let k := (inclusion X).comp (simplexAttachmentCellMap (Index X) 1 (g := characteristic X) a)
  have hq : Path.Homotopic.Quotient.mk
      ((PathConnectedSpace.somePath (StdSimplex.single (0 : Fin 2))
        (StdSimplex.single 1)).map k.continuous) =
      Path.Homotopic.Quotient.mk (intervalPath.map k.continuous) :=
    _root_.Quotient.sound ((Convexity.StdSimplex.paths_homotopic _ intervalPath).map k)
  change eqToHom (congrArg FundamentalGroupoid.mk
      (vertexPoint X a boundaryZero)) ≫
    Path.Homotopic.Quotient.mk
      ((PathConnectedSpace.somePath (StdSimplex.single (0 : Fin 2))
        (StdSimplex.single 1)).map k.continuous) ≫
    eqToHom (congrArg FundamentalGroupoid.mk
      (vertexPoint X a boundaryOne).symm) = _
  rw [hq, FundamentalGroupoid.conj_eqToHom
    (vertexPoint X a boundaryZero) (vertexPoint X a boundaryOne)]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact characteristic_path X a t

end SimplicialGraph
end SSet
