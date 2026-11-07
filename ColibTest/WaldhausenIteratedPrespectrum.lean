import Colib.KTheory.Waldhausen.Iterated.Prespectrum
import Colib.KTheory.Waldhausen.KFunctor

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory Opposite MonoidalCategory SSet Topology
open scoped Simplicial Topology unitInterval

universe u v

namespace WaldhausenIteratedPrespectrumTests

section FiniteStages

variable (W : WideSubcategory preservesZero.{u})

-- The restriction is Mathlib's wide subcategory of the single canonical exact category.
example : (wideSubcategoryInclusion preservesZero).obj W = W.obj := rfl

example (r : ℕ) : stages (r + 1) = prolong (stages r) := rfl

example : (stages 0).obj W = sSet W.obj.waldhausen.cof W.obj.waldhausen.weq := rfl

example : (stages 1).obj W ≅ doubleDiagonal W.obj.waldhausen := stagesOneIso W

example (n : SimplexCategory) :
    ((rows n).obj W).obj.Obj = QuotientRows.Obj W.obj.waldhausen n := rfl

example : stageCylinder 0 W ≫ (stagesOneIso W).hom =
    suspensionCylinder W.obj.waldhausen := stageCylinder_zero W

example (r : ℕ) : (stages r).map (zeroHom W W) = SSet.const (stageVertex r W) :=
  stages_map_zeroHom r W W

example (r : ℕ) (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj W).obj n) (c : Fin 2) :
    (stageCylinder r W).app n (A, ⟨SimplexCategory.const n.unop ⦋1⦌ c⟩) =
      (SSet.const (X := (stages r).obj W) (stageVertex (r + 1) W)).app n A :=
  stageCylinder_endpoint r W n A c

example (r : ℕ) :
    SSet.yonedaEquiv.symm (stageVertex r W) ▷ Δ[1] ≫ stageCylinder r W =
      CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
        SSet.yonedaEquiv.symm (stageVertex (r + 1) W) := stageCylinder_fixed_vertex r W

example (r : ℕ) : stageLoopMap r W (stagePoint r W) =
    Path.refl (stagePoint (r + 1) W) := stageLoopMap_point r W

example : stageLoopMap 0 W = loopStructureMap W.obj.waldhausen := stageLoopMap_zero W

example : (prespectrum W).space 0 =
    TopCat.of (Path (stagePoint 0 W) (stagePoint 0 W)) := rfl

example (r : ℕ) : (prespectrum W).space (r + 1) = stageSpace r W := rfl

example : (prespectrum W).structureMap 0 = ContinuousMap.id _ := rfl

example (r : ℕ) : (prespectrum W).structureMap (r + 1) = stageLoopMap r W := rfl

example (n : ℕ) : W.obj.waldhausen.K n ≃
    HomotopyGroup.Pi n ((prespectrum W).space 0) ((prespectrum W).point 0) :=
  zeroSpaceHomotopyEquiv W n

variable {V : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

example (r : ℕ) :
    ((stages r).map F ▷ Δ[1]) ≫ stageCylinder r W =
      stageCylinder r V ≫ (stages (r + 1)).map F := stageCylinder_naturality r F

example (r : ℕ) (x : stageSpace r V) :
    basedLoopMap (SSet.toTop.map ((stages (r + 1)).map F)).hom
      (stageMap_point (r + 1) F) (stageLoopMap r V x) =
        stageLoopMap r W (SSet.toTop.map ((stages r).map F) x) :=
  stageLoopMap_naturality r F x

example : prespectrumFunctor.map F = prespectrumMap F := rfl

example (r : ℕ) : (prespectrumMap F).map (r + 1) =
    (SSet.toTop.map ((stages r).map F)).hom := rfl

example : prespectrumFunctor.map (𝟙 W) = 𝟙 (prespectrum W) := prespectrumFunctor.map_id W

example {U : WideSubcategory preservesZero.{u}} (G : W ⟶ U) :
    prespectrumMap (F ≫ G) =
      LoopPrespectrum.Hom.comp (prespectrumMap F) (prespectrumMap G) :=
  prespectrumFunctor.map_comp F G

end FiniteStages

section OriginalUniverses

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F) (h0 : F.obj W.zero = V.zero)

example : (asSmallCategory W).obj.Obj = AsSmall.{0} C := rfl

example : LoopPrespectrum.{max u v} := originalPrespectrum W

example (n : ℕ) : W.K n ≃ HomotopyGroup.Pi n
    ((originalPrespectrum W).space 0) ((originalPrespectrum W).point 0) :=
  originalZeroSpaceEquiv W n

example (n : ℕ) : W.K (n + 1) ≃* HomotopyGroup.Pi (n + 1)
    ((originalPrespectrum W).space 0) ((originalPrespectrum W).point 0) :=
  originalZeroSpaceMulEquiv W n

example : (asSmallCategoryMap W V hF h0).hom.toFunctor = asSmallFunctor F := rfl

example (n : ℕ) (a : W.K n) :
    originalZeroSpaceEquiv V n (KMap hF n a) =
      HomotopyGroup.map ((originalPrespectrumMap W V hF h0).map 0)
        ((originalPrespectrumMap W V hF h0).map_point 0) (originalZeroSpaceEquiv W n a) :=
  originalZeroSpaceEquiv_naturality W V hF h0 n a

end OriginalUniverses

-- Moving the canonical owner must not restrict its original arbitrary-exact K-functor.
section ArbitraryExact

variable {C D : SmallWaldhausenCategory.{u}} (F : C ⟶ D) (n : ℕ)

example : (KFunctor n).obj C = GrpCat.of (C.waldhausen.K n) := rfl

example : (KFunctor n).map F = GrpCat.ofHom (KMap F.isExact n) := rfl

example : (KFunctor n).map (𝟙 C) = 𝟙 ((KFunctor n).obj C) := (KFunctor n).map_id C

example {E : SmallWaldhausenCategory.{u}} (G : D ⟶ E) :
    (KFunctor n).map (F ≫ G) = (KFunctor n).map F ≫ (KFunctor n).map G :=
  (KFunctor n).map_comp F G

end ArbitraryExact

end WaldhausenIteratedPrespectrumTests
