/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Congruence

public import Colib.CategoryTheory.TheoremB.ReplacementVertex
public import Colib.CategoryTheory.TheoremB.ReplacementProjectionTower
public import Colib.CategoryTheory.TheoremB.ReplacementSkeletonCompact
public import Colib.Topology.HomotopyFiber.DiscreteWeakComparison
public import Colib.Topology.HomotopyPullback.Fibration

/-!
# From finite cartesian skeleta to the actual vertex homotopy fiber

The first base skeleton is discrete. Weak cartesian assembly therefore
restricts to each vertex fiber, including in degree zero. All total spaces,
base changes, coproduct coordinates and forward comparison maps are actual
realizations and compact-open path spaces.
-/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/VertexWeakAssembly.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, paths and identity
basepoints are retained under native namespace and dependency ownership. -/
@[expose] public section

open CategoryTheory.TheoremA

noncomputable section
open SSet TopCat Topology CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremB
open TheoremA Topology.HomotopyPullback.Sequential
variable {D : Type u} [SmallCategory D]

variable (H : D ⥤ SSet.{u})

/-- The stage-one projection to the actual discrete point stage. -/
abbrev replacementStageOneProjection := (replacementProjectionTowerMap H).app 1 |>.hom

/-- The induced colimit map is exactly the realized canonical base map. -/
theorem replacementBaseSkeleton_colimitMap :
    (realizedReplacementSkeletonIsColimit H).map replacementBaseSkeletonCocone
      (replacementProjectionTowerMap H) = SSet.toTop.map (replacementBaseMap H) := by
  have hm : (realizedReplacementSkeletonIsColimit H).map replacementBaseSkeletonCocone
      (replacementProjectionTowerMap H) =
      (realizedReplacementSkeletonIsColimit H).map
        (realizedReplacementSkeletonCocone pointDiagram) (replacementProjectionTowerMap H) ≫
          (replacementPointRealizationIso (D := D)).hom := by
    apply (realizedReplacementSkeletonIsColimit H).hom_ext
    intro n
    rw [(realizedReplacementSkeletonIsColimit H).ι_map,
      ← Category.assoc, (realizedReplacementSkeletonIsColimit H).ι_map]
    rfl
  rw [hm, realizedReplacementSkeleton_colimitMap]
  change SSet.toTop.map (diagonalMap (simplicialReplacementMap (replacementPointAugmentation H))) ≫
    SSet.toTop.map ((diagonalMap replacementPointIso.hom) ≫ (diagonalBaseIso D).hom) = _
  rw [← Functor.map_comp]
  exact congrArg SSet.toTop.map (targetAugmentation_diagonal H)

/-- Point-augmentation maps preserve the index in actual coproduct coordinates. -/
theorem replacementStageOneProjection_vertex (d : D) (x : |H.obj d|) :
    replacementStageOneProjection H (realizedReplacementStageOneHomeomorph H ⟨d, x⟩) =
      pointStageOneVertex d := by
  rw [realizedReplacementStageOneHomeomorph_naturality]
  exact congrArg (fun z ↦ realizedReplacementStageOneHomeomorph pointDiagram ⟨d, z⟩)
    (@Subsingleton.elim |(Δ[0] : SSet.{u})| inferInstance _ _)

/-- The full stage-one base square agrees with the coproduct projection. -/
theorem replacementStageOneProjection_coordinates (z : (realizedReplacementSkeleton H).obj 1) :
    pointStageOneHomeomorph (replacementStageOneProjection H z) =
      ((realizedReplacementStageOneHomeomorph H).symm z).1 := by
  obtain ⟨⟨d, x⟩, rfl⟩ := (realizedReplacementStageOneHomeomorph H).surjective z
  rw [replacementStageOneProjection_vertex, Homeomorph.symm_apply_apply]
  exact pointStageOneHomeomorph.apply_symm_apply d

/-- Strict fiber coordinates before selecting the chosen coproduct summand. -/
def stageOneStrictFiberCoordinates (d : D) :
    {z : (realizedReplacementSkeleton H).obj 1 // replacementStageOneProjection H z =
      pointStageOneVertex d} ≃ₜ
      {z : (Σ d : TopCat.discrete.obj D, |H.obj d|) // sigmaProjection (fun d : TopCat.discrete.obj
        D ↦ |H.obj d|) z = d} where
  toFun z := ⟨(realizedReplacementStageOneHomeomorph H).symm z.1,
    (replacementStageOneProjection_coordinates H z.1).symm.trans
      ((congrArg pointStageOneHomeomorph z.2).trans (pointStageOneHomeomorph.apply_symm_apply d))⟩
  invFun z := ⟨realizedReplacementStageOneHomeomorph H z.1, by
    apply pointStageOneHomeomorph.injective
    rw [replacementStageOneProjection_coordinates, Homeomorph.symm_apply_apply]
    exact z.2.trans (pointStageOneHomeomorph.apply_symm_apply d).symm⟩
  left_inv z := Subtype.ext ((realizedReplacementStageOneHomeomorph H).apply_symm_apply z.1)
  right_inv z := Subtype.ext ((realizedReplacementStageOneHomeomorph H).symm_apply_apply z.1)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Each actual stage-one strict fiber is homeomorphic to its diagram value. -/
def stageOneFiberHomeomorph (d : D) : |H.obj d| ≃ₜ
    {z : (realizedReplacementSkeleton H).obj 1 // replacementStageOneProjection H z =
      pointStageOneVertex d} :=
  (sigmaStrictFiberHomeomorph (fun d : TopCat.discrete.obj D ↦ |H.obj d|) d).symm.trans
    (stageOneStrictFiberCoordinates H d).symm

@[simp]
theorem stageOneFiberHomeomorph_val (d : D) (x : |H.obj d|) :
    (stageOneFiberHomeomorph H d x).1 = realizedReplacementStageOneHomeomorph H ⟨d, x⟩ := rfl

/-- Actual homotopy pullback of the full base projection over the first stage. -/
abbrev vertexPullback :=
  ColimitPullback (replacementProjectionTowerMap H)
    (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
    (replacementBaseSkeletonCocone (D := D)) 1

/-- Its canonical stage-one comparison. -/
abbrev vertexPullbackComparison :=
  colimitComparison (replacementProjectionTowerMap H)
    (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
    (replacementBaseSkeletonCocone (D := D)) 1

/-- Projection of the actual homotopy pullback to the discrete first base stage. -/
abbrev vertexPullbackProjection := HomotopyPullback.baseProjection
  ((realizedReplacementSkeletonIsColimit H).map replacementBaseSkeletonCocone
    (replacementProjectionTowerMap H)).hom (replacementBaseSkeletonCocone.ι.app 1).hom

/-- The strict fiber of this actual pullback is the actual homotopy fiber of
the full canonical base projection at the corresponding object vertex. -/
def vertexPullbackFiberHomeomorph (d : D) :
    {z : vertexPullback H // vertexPullbackProjection H z = pointStageOneVertex d} ≃ₜ
      HomotopyFiber (SSet.toTop.map (replacementBaseMap H)).hom (classifyingSpacePoint d) :=
  (HomotopyPullback.strictBaseFiberHomeomorph _ _ (pointStageOneVertex d)).trans
    (HomotopyFiber.congrHomeomorph
      (congrArg TopCat.Hom.hom (replacementBaseSkeleton_colimitMap H))
      (replacementBaseSkeletonCocone_vertex d))

/-- Restrict the actual stage-one comparison to one discrete fiber. -/
abbrev vertexRestrictedComparison (d : D) :=
  discreteStrictFiberMap (replacementStageOneProjection H) (vertexPullbackProjection H)
    (vertexPullbackComparison H) rfl (pointStageOneVertex d)

/-- Canonical constant-path comparison from a diagram value into the actual
homotopy fiber of its replacement's base projection. -/
def vertexFiberComparison (d : D) :
    C(|H.obj d|, HomotopyFiber (SSet.toTop.map (replacementBaseMap H)).hom
      (classifyingSpacePoint d)) where
  toFun x := HomotopyFiber.basepoint _ _ (SSet.toTop.map (replacementVertexInclusion H d) x)
    (replacementVertex_base H d x)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (SSet.toTop.map (replacementVertexInclusion H d)).hom.continuous.prodMk continuous_const

/-- Both source and target fiber identifications retain the prescribed
canonical vertex comparison, including its constant target path. -/
theorem vertexPullbackFiberHomeomorph_comparison (d : D) :
    (vertexPullbackFiberHomeomorph H d : C(_, _)).comp
      ((vertexRestrictedComparison H d).comp (stageOneFiberHomeomorph H d : C(_, _))) =
        vertexFiberComparison H d := by
  ext x
  apply Subtype.ext
  apply Prod.ext
  · exact realizedReplacementStageOneHomeomorph_colimit H d x
  · apply ContinuousMap.ext
    intro t
    change (replacementBaseSkeletonCocone (D := D)).ι.app 1
      (replacementStageOneProjection H (realizedReplacementStageOneHomeomorph H ⟨d, x⟩)) =
        classifyingSpacePoint d
    rw [replacementStageOneProjection_vertex]
    exact replacementBaseSkeletonCocone_vertex d

/-- Finite cartesian comparisons of the first stage with later skeleta give
the genuine canonical vertex-to-homotopy-fiber bijection in every degree.
The first-stage fiber restriction is justified by discreteness, including π₀. -/
theorem vertexFiberComparison_bijective
    (e : ∀ m (h : 1 ≤ m), ContinuousMap.HomotopyEquiv
      ((realizedReplacementSkeleton H).obj 1)
      (StagePullback (replacementProjectionTowerMap H) 1 m h))
    (he : ∀ m h, (e m h).toFun = stageComparison (replacementProjectionTowerMap H) 1 m h)
    (d : D) (x : |H.obj d|) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (vertexFiberComparison H d) (x := x) rfl) :=
      by
  let s := stageOneFiberHomeomorph H d
  let t := vertexPullbackFiberHomeomorph H d
  let f := vertexRestrictedComparison H d
  have htotal := colimitComparison_homotopyGroupMap_bijective (replacementProjectionTowerMap H)
    (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
    replacementBaseSkeletonCocone replacementBaseSkeletonIsColimit
    (realizedReplacementSkeleton_closedEmbeddings H)
    (realizedReplacementSkeleton_closedEmbeddings pointDiagram) 1 e he (s x).1 n
  have hf := homotopyGroupMap_bijective_discreteStrictFiber
    (replacementStageOneProjection H) (vertexPullbackProjection H)
    (vertexPullbackComparison H) rfl (pointStageOneVertex d) (s x) htotal
  have hs := homotopyGroupMap_bijective_of_homotopyEquiv s.toHomotopyEquiv (x := x) rfl n
  have hfs := homotopyGroupMap_bijective_comp (x := x) (y := s x) (z := f (s x))
    s.toHomotopyEquiv.toFun f rfl rfl n hs hf
  have hpoint : t (f (s x)) = vertexFiberComparison H d x :=
    ContinuousMap.congr_fun (vertexPullbackFiberHomeomorph_comparison H d) x
  have ht := homotopyGroupMap_bijective_of_homotopyEquiv t.toHomotopyEquiv hpoint n
  have hall := homotopyGroupMap_bijective_comp (x := x) (y := f (s x))
    (z := vertexFiberComparison H d x) (f.comp s.toHomotopyEquiv.toFun) t.toHomotopyEquiv.toFun
    rfl hpoint n hfs ht
  exact homotopyGroupMap_bijective_of_based_homotopy
    (f := t.toHomotopyEquiv.toFun.comp (f.comp s.toHomotopyEquiv.toFun))
    (g := vertexFiberComparison H d) (x := x) hpoint rfl
    ((ContinuousMap.Homotopy.refl (vertexFiberComparison H d)).cast
      (vertexPullbackFiberHomeomorph_comparison H d).symm rfl)
    (fun _ ↦ rfl) n hall

variable {C : Type u} [SmallCategory C] (F : C ⥤ D)

/-- The complete weak comparison bridge for the comma replacement. The sole
unproved geometric input at this boundary is finite-stage homotopy
cartesianness; compact assembly, the stage-one identification, resolution
transport, and the canonical identity basepoint are all derived. -/
theorem fiberComparison_bijective_of_finiteSkeleta
    (e : ∀ m (h : 1 ≤ m), ContinuousMap.HomotopyEquiv
      ((realizedReplacementSkeleton (commaNerveDiagram F)).obj 1)
      (StagePullback (replacementProjectionTowerMap (commaNerveDiagram F)) 1 m h))
    (he : ∀ m h, (e m h).toFun =
      stageComparison (replacementProjectionTowerMap (commaNerveDiagram F)) 1 m h)
    (c : C) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (fiberComparison F (F.obj c)) (fiberComparison_identity F c)) :=
  fiberComparison_bijective_of_replacement F c n
    (vertexFiberComparison_bijective (commaNerveDiagram F) e he (F.obj c)
      (classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.obj c)))) n)

end CategoryTheory.TheoremB
