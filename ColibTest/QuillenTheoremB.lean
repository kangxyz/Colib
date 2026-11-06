module

public import Colib.CategoryTheory.TheoremB.CartesianProducts
public import Colib.CategoryTheory.TheoremB.StructuredComparison
public import Colib.CategoryTheory.TheoremB.SkeletalBoundary
public import Colib.CategoryTheory.TheoremB.StageOneCartesian
public import Colib.Topology.HomotopyPullback.CoordinateTransport

@[expose] public noncomputable section
universe u
open SSet Topology CategoryTheory CategoryTheory.TheoremA CategoryTheory.TheoremB
open scoped Simplicial Topology

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

example (d : D) :
    (HomotopyFiber.projection (classifyingSpaceMap F).hom (classifyingSpacePoint d)).comp
      (fiberComparison F d) = (classifyingSpaceMap (CostructuredArrow.proj F d)).hom :=
  fiberComparison_projection F d

example (c : C) :
    structuredFiberComparison F (F.obj c)
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) =
    HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
      (classifyingSpacePoint c) (classifyingSpaceMap_point F c) :=
  structuredFiberComparison_identity F c

example (h : StructuredTransitionHomotopyEquivalences F) :
    TransitionHomotopyEquivalences F.op :=
  transitionHomotopyEquivalences_op_of_structured F h

example (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    (realizedCommaRowSquareHomotopyEquiv F h α).toFun =
      realizedCommaRowSquareComparison F α :=
  realizedCommaRowSquareHomotopyEquiv_toFun F h α

example (h : TransitionHomotopyEquivalences F)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q)
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L] (k : C(K, L)) :
    (realizedCommaPrismHomotopyEquiv F h α k).toFun = realizedCommaPrismComparison F α k :=
  realizedCommaPrismHomotopyEquiv_toFun F h α k

example {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A]
    [TopologicalSpace B] (f : C(X, B)) (g : C(A, B)) (hf : HomotopyLiftingProperty f) :
    (HomotopyPullback.strictPullbackHomotopyEquivOfLifting f g hf).toFun =
      HomotopyPullback.strictPullbackInclusion f g := rfl

example (H : D ⥤ SSet.{u}) (n : ℕ) :
    HomotopyPullback.Cartesian
      ((diagonalFunctor ⋙ SSet.toTop).map
        (replacementCellBoundariesMap (replacementPointAugmentation H) n)).hom
      ((diagonalFunctor ⋙ SSet.toTop).map
        (replacementCellsMap (replacementPointAugmentation H) n)).hom
      ((diagonalFunctor ⋙ SSet.toTop).map (replacementCellsBoundaryι H n)).hom
      ((diagonalFunctor ⋙ SSet.toTop).map
        (replacementCellsBoundaryι ((Functor.const D).obj (Δ[0] : SSet.{u})) n)).hom
      (congrArg TopCat.Hom.hom
        (realizedReplacementCellsMap_boundary H (replacementPointAugmentation H) n)) :=
  replacementBoundary_cartesian H n

example {H K : D ⥤ SSet.{u}} (η : H ⟶ K) (d : D) :
    HomotopyPullback.Cartesian (SSet.toTop.map (η.app d)).hom
      ((realizedReplacementSkeletonMap η).app 1).hom
      (SSet.toTop.map (SSet.simplicialSigmaι (fun d ↦ H.obj d) d ≫
        vertexCoproductToStageOne H)).hom
      (SSet.toTop.map (SSet.simplicialSigmaι (fun d ↦ K.obj d) d ≫
        vertexCoproductToStageOne K)).hom
      (congrArg TopCat.Hom.hom (realizedReplacementStageOneVertex_square η d)) :=
  realizedReplacementStageOneVertex_cartesian η d
