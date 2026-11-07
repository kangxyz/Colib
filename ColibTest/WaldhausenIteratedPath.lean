module

import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Interchange
import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.RelativeTime
import Colib.KTheory.Waldhausen.Iterated.PathObject

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen.Fibration.RelativeRows SSet Topology
open scoped Simplicial Topology unitInterval

universe u v

section ActualRows
variable (W : WideSubcategory preservesZero.{u}) (m n : SimplexCategory)

example : (rowSwap W m n).hom.hom.toFunctor =
    QuotientRows.transposeRows W.obj.waldhausen m n := rfl

example : (rowSwap W m n).hom.hom.toFunctor.obj
    ((rows m).obj ((rows n).obj W)).obj.waldhausen.zero =
      ((rows n).obj ((rows m).obj W)).obj.waldhausen.zero :=
  (rowSwap W m n).hom.property

example : (rowsInterchange m n).hom.app W = (rowSwap W m n).hom := rfl

example : (rowDiagramInterchange W n).hom.app (op m) = (rowSwap W m n).hom := rfl

example (τ : n ⟶ ⦋1⦌) :
    (rows m).map ((insertion τ).app W) ≫ (rowSwap W m n).hom =
      (insertion τ).app ((rows m).obj W) := insertion_rowSwap W m τ
end ActualRows

section OrdinalParameters
variable {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌)

example : (relativeTime τ).toOrderHom 0 = 0 := rfl
example (i : Fin (n.len + 1)) : (relativeTime τ).toOrderHom i.succ = τ.toOrderHom i := rfl
example : addInitial.map α ≫ relativeTime τ = relativeTime (α ≫ τ) :=
  relativeTime_reindex α τ
example : tail.app n ≫ relativeTime τ = τ := relativeTime_tail τ
example : relativeTime (n.const ⦋1⦌ 0) = (addInitial.obj n).const ⦋1⦌ 0 := relativeTime_zero n
example : relativeTime (n.const ⦋1⦌ 1) = fiberOrdinal n := relativeTime_one n
example : (pathClamp τ).toOrderHom 0 = 0 := rfl
example (i : Fin (n.len + 1)) : (pathClamp τ).toOrderHom i.succ =
    if τ.toOrderHom i = 0 then 0 else i.succ := rfl
example : pathClamp (α ≫ τ) ≫ addInitial.map α = addInitial.map α ≫ pathClamp τ :=
  pathClamp_naturality α τ
end OrdinalParameters

section ActualPath
variable (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
  (W : WideSubcategory preservesZero.{u})

example (n : SimplexCategoryᵒᵖ) :
    ((pathAugmentation W).app n).hom.toFunctor =
      QuotientRows.reindex W.obj.waldhausen (⦋0⦌.const (addInitial.obj n.unop) 0) := rfl

example (n : SimplexCategoryᵒᵖ) :
    ((pathSection W).app n).hom.toFunctor =
      QuotientRows.reindex W.obj.waldhausen ((addInitial.obj n.unop).const ⦋0⦌ 0) := rfl

example (n : SimplexCategoryᵒᵖ)
    (A : (H.obj ((rows (addInitial.obj n.unop)).obj W)).obj n) (τ : n.unop ⟶ ⦋1⦌) :
    (pathCylinder H W).app n (A, ⟨τ⟩) =
      (H.map ((rowsReindex (pathClamp τ)).app W)).app n A := rfl

example : SSet.ι₀ ≫ (pathHomotopy H W).h = pathAugmentationMap H W ≫ pathSectionMap H W :=
  pathCylinder_zero H W
example : SSet.ι₁ ≫ (pathHomotopy H W).h = 𝟙 _ := pathCylinder_one H W
example : (pathRealizationEquiv H W).toFun = (SSet.toTop.map (pathAugmentationMap H W)).hom := rfl
example : (pathRealizationEquiv H W).invFun = (SSet.toTop.map (pathSectionMap H W)).hom := rfl

example (t : unitInterval) (x : |SSet.diagonalSSet (pathDiagram W ⋙ H)|) :
    realizationSimplicialHomotopy (pathHomotopy H W) (t, x) =
      SSet.toTop.map (pathCylinder H W)
        ((realizationCylinderIso (SSet.diagonalSSet (pathDiagram W ⋙ H))).inv
          (x, ULift.up t)) := rfl

example (r : ℕ) (n : SimplexCategory) (τ : n ⟶ ⦋1⦌) :
    (pathCylinder (stages r) W).app (op n)
      (((stages r).obj ((rows (addInitial.obj n)).obj W)).map (n.const ⦋0⦌ 0).op
        (stageVertex r ((rows (addInitial.obj n)).obj W)), ⟨τ⟩) =
      ((stages r).obj ((rows (addInitial.obj n)).obj W)).map (n.const ⦋0⦌ 0).op
        (stageVertex r ((rows (addInitial.obj n)).obj W)) := by
  exact (ConcreteCategory.congr_hom
    (((stages r).map ((rowsReindex (pathClamp τ)).app W)).naturality (n.const ⦋0⦌ 0).op)
    (stageVertex r ((rows (addInitial.obj n)).obj W))).trans
      (congrArg (((stages r).obj ((rows (addInitial.obj n)).obj W)).map (n.const ⦋0⦌ 0).op)
        (stageVertex_naturality r ((rowsReindex (pathClamp τ)).app W)))

example (r : ℕ) : PathConnectedSpace (stageSpace r W) := stageSpace_pathConnected r W
example (r : ℕ) (h : ∀ ⦃A B : W.obj.Obj⦄ (f : A ⟶ B), W.obj.waldhausen.weq f) :
    ContractibleSpace (stageSpace r W) := stageSpace_contractible_of_all_weak r W h
example (r : ℕ) : ContractibleSpace |SSet.diagonalSSet (pathDiagram W ⋙ stages r)| :=
  pathStage_contractible r W
end ActualPath

section IndependentUniverses
variable {C : Type u} [Category.{v} C] (W : Structure C)

example (r : ℕ) : PathConnectedSpace (stageSpace r (asSmallCategory W)) :=
  stageSpace_pathConnected r (asSmallCategory W)
example (r : ℕ) :
    ContractibleSpace |SSet.diagonalSSet (pathDiagram (asSmallCategory W) ⋙ stages r)| :=
  pathStage_contractible r (asSmallCategory W)
end IndependentUniverses
