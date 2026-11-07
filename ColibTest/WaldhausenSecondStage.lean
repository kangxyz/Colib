import Colib.KTheory.Waldhausen.Iterated.Functoriality

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory SSet Topology
open scoped Simplicial Topology unitInterval

universe u v

namespace WaldhausenSecondStageTests

open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS

section Construction

variable {C : Type u} [Category.{v} C] (W : Structure C)

-- The second stage is the existing S-construction of actual quotient rows.
example (n : SimplexCategoryᵒᵖ) :
    (doubleS W).obj n = sSet (QuotientRows.waldhausenStructure W n.unop).cof
      (QuotientRows.waldhausenStructure W n.unop).weq := rfl

example : doubleDiagonal W = SSet.diagonalSSet (doubleS W) := rfl

example {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    suspensionRow W τ = QuotientRows.oneEmbedding W ⋙ QuotientRows.reindex W τ := rfl

example {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    IsExact W.cof W.weq (QuotientRows.waldhausenStructure W n).cof
      (QuotientRows.waldhausenStructure W n).weq (suspensionRow W τ) :=
  suspensionRow_exact W τ

example {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌) :
    suspensionRow W (α ≫ τ) = suspensionRow W τ ⋙ QuotientRows.reindex W α :=
  suspensionRow_reindex W α τ

example (n : SimplexCategory) (c : Fin 2) :
    suspensionRow W (SimplexCategory.const n ⦋1⦌ c) =
      (Functor.const C).obj (QuotientRows.zero W n) := suspensionRow_const W n c

example {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    (suspensionRow W τ).obj W.zero = QuotientRows.zero W n :=
  suspensionRow_zero_obj W τ

example : SSet.ι₀ ≫ suspensionCylinder W = doubleZero W := suspensionCylinder_zero W

example : SSet.ι₁ ≫ suspensionCylinder W = doubleZero W := suspensionCylinder_one W

example : doubleZero W = SSet.const (doubleVertex W) := doubleZero_eq_const W

example :
    SSet.yonedaEquiv.symm (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) ▷ Δ[1] ≫
      suspensionCylinder W =
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (doubleVertex W) :=
  suspensionCylinder_fixed_vertex W

-- These endpoints and basedness concern the actual continuous path-space map.
example : C(W.Delooping, Path (doubleBasepoint W) (doubleBasepoint W)) :=
  loopStructureMap W

example (x : W.Delooping) : loopStructureMap W x 0 = doubleBasepoint W :=
  (loopStructureMap W x).source

example (x : W.Delooping) : loopStructureMap W x 1 = doubleBasepoint W :=
  (loopStructureMap W x).target

example : loopStructureMap W W.kBasepoint = Path.refl (doubleBasepoint W) :=
  loopStructureMap_basepoint W

-- The degree shift is a homomorphism, with no invertibility premise.
example (n : ℕ) :
    W.K n →* HomotopyGroup.Pi (n + 2) (doubleDelooping W) (doubleBasepoint W) :=
  degreeRaisingMap W n

example (n : ℕ) : degreeRaisingMap W n =
    (loopShiftMulEquiv n).symm.toMonoidHom.comp
      (HomotopyGroup.piMap n (loopStructureMap W) (loopStructureMap_basepoint W)) := rfl

end Construction

section ExactFunctors

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

-- No strict-zero condition is needed for the actual double simplicial map.
example : doubleS V ⟶ doubleS W := doubleMap V W hF

example : doubleDiagonalMap V W hF = SSet.diagonalMap (doubleMap V W hF) := rfl

-- Based cylinder and loop naturality retain the original explicit zero equality.
variable (h0 : F.obj V.zero = W.zero)

example :
    (sSetMap hF ▷ Δ[1]) ≫ suspensionCylinder W =
      suspensionCylinder V ≫ doubleDiagonalMap V W hF :=
  suspensionCylinder_naturality V W hF h0

example :
    SSet.toTop.map (doubleDiagonalMap V W hF) (doubleBasepoint V) = doubleBasepoint W :=
  doubleDiagonalMap_basepoint V W hF h0

example (x : V.Delooping) :
    basedLoopMap (SSet.toTop.map (doubleDiagonalMap V W hF)).hom
      (doubleDiagonalMap_basepoint V W hF h0) (loopStructureMap V x) =
        loopStructureMap W (deloopingMap hF x) :=
  loopStructureMap_naturality V W hF h0 x

end ExactFunctors

end WaldhausenSecondStageTests
