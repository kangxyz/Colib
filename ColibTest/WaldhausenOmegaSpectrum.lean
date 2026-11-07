import Colib.KTheory.Waldhausen.Iterated.ExactMaps

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory Opposite MonoidalCategory SSet Topology
open scoped Simplicial Topology unitInterval

universe u v

namespace WaldhausenOmegaSpectrumTests

section ActualStages

variable (r : ℕ) (W : WideSubcategory preservesZero.{u})

example (n : SimplexCategory) : IsRealizationEquivalence (stageFirstTail r W n) :=
  stageFirstTail_equivalence r W n

example : ContractibleSpace |diagonalSSet (pathDiagram W ⋙ stages r)| :=
  pathStage_contractible r W

example : IsWeakHomotopyEquivalence (stageTotalFiberComparison r W) :=
  stageTotalFiberComparison_weak r W

example (x : stageSpace r W) :
    (stageTotalFiberComparison r W x).val.1 =
      SSet.toTop.map (stageTotalFiberInclusion r W) x := rfl

example (x : stageSpace r W) (t : unitInterval) :
    (stageTotalFiberComparison r W x).val.2 t = stagePoint (r + 1) W := rfl

example : stageRelativeCylinder r W ≫ diagonalMap (stagePathProjection r W) =
    stageCylinder r W := stageRelativeCylinder_tail r W

example : HomotopyFiber.cylinderLoop (stageTotalTailMap r W) (stagePoint (r + 1) W)
    (stagePathPoint r W) (stageTotalTailMap_point r W)
    (SSet.toTop.map (stageTotalFiberInclusion r W)).hom
    (stageTotalTailMap_fiberInclusion r W) (stageRelativeTopHomotopy r W) =
      stageLoopMap r W := stageCylinderLoop_eq r W

example : IsWeakHomotopyEquivalence (stageLoopMap r W) := stageLoopMap_weak r W

example (y : Path (stagePoint (r + 1) W) (stagePoint (r + 1) W)) :
    ∃ x : stageSpace r W, Joined (stageLoopMap r W x) y :=
  (stageLoopMap_weak r W).component_surjective y

example (x : stageSpace r W) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (stageLoopMap r W) (x := x) rfl) :=
  (stageLoopMap_weak r W).homotopy_bijective x n

example : (prespectrum W).IsOmega := prespectrum_isOmega W

example : (prespectrum W).structureMap 0 = ContinuousMap.id _ := rfl

example : (prespectrum W).structureMap (r + 1) = stageLoopMap r W := rfl

example : (omegaSpectrumFunctor.obj W).obj = prespectrum W := rfl

variable {V : WideSubcategory preservesZero.{u}} (F : W ⟶ V)

example : (omegaSpectrumFunctor.map F).hom = prespectrumMap F := rfl

end ActualStages

section OriginalUniverses

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F) (h0 : F.obj W.zero = V.zero)

example : LoopPrespectrum.OmegaSpectrum.{max u v} := originalOmegaSpectrum W

example : (originalOmegaSpectrum W).obj = originalPrespectrum W := rfl

example : (originalOmegaSpectrumMap W V hF h0).hom =
    originalPrespectrumMap W V hF h0 := rfl

example : (exactOriginalOmegaSpectrumMap W V hF).hom =
    exactOriginalPrespectrumMap W V hF := rfl

example (n : ℕ) (a : W.K n) :
    originalZeroSpaceEquiv V n (KMap hF n a) =
      HomotopyGroup.map ((exactOriginalPrespectrumMap W V hF).map 0)
        ((exactOriginalPrespectrumMap W V hF).map_point 0) (originalZeroSpaceEquiv W n a) :=
  exactOriginalZeroSpaceEquiv_naturality W V hF n a

end OriginalUniverses

end WaldhausenOmegaSpectrumTests
