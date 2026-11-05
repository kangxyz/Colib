/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Functor.Rebase
public import Colib.CategoryTheory.Waldhausen.Additivity.DiagramIso
public import Colib.CategoryTheory.Waldhausen.Additivity.SumDiagrams

/-! # The common separated endpoint with a strict chosen zero

Implementation provenance: `Quillen/Waldhausen/Additivity/NormalizedSumMap.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
universe u v

namespace CategoryTheory.Waldhausen.Additivity

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
variable {F H : C ⥤ D}
variable (hH : IsExact V.cof V.weq W.cof W.weq H)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The pair-sum of chosen source zeros is genuinely zero. -/
def splitEndpointZeroIso : (splitEndpoint H F).obj (V.zero, V.zero) ≅ W.zero :=
  (coprod_isZero W (hH.zero V.isZero) (hF.zero V.isZero)).iso W.isZero

/-- Normalize the common pair-sum endpoint at the actual pair of zeros. -/
def normalizedSplitEndpoint : C × C ⥤ D :=
  rebaseFunctor (splitEndpoint H F) (V.zero, V.zero) W.zero
    (splitEndpointZeroIso V W hH hF)

/-- The actual natural identification with the unnormalized pair-sum. -/
def normalizedSplitIso : splitEndpoint H F ≅ normalizedSplitEndpoint V W hH hF :=
  rebaseFunctorIso _ _ _ (splitEndpointZeroIso V W hH hF)

@[simp] theorem normalizedSplitEndpoint_obj_zero :
    (normalizedSplitEndpoint V W hH hF).obj (V.zero, V.zero) = W.zero :=
  rebaseFunctor_obj_base _ _ _ _

/-- The two restrictions before their common normalized pair-sum. -/
def separatedPairGrid {n m : SimplexCategory}
    (A : Grid₂ (SSet.OrdinalSubdivision.δ.obj n) m ⥤ C) : Grid₂ n m ⥤ C × C :=
  (gridMap₂ (SSet.OrdinalJoin.left n n) (𝟙 m) ⋙ A).prod'
    (gridMap₂ (SSet.OrdinalJoin.right n n) (𝟙 m) ⋙ A)

/-- The actual chosen-zero common endpoint diagram. -/
def normalizedSumGrid {n m : SimplexCategory}
    (A : Grid₂ (SSet.OrdinalSubdivision.δ.obj n) m ⥤ C) : Grid₂ n m ⥤ D :=
  separatedPairGrid A ⋙ normalizedSplitEndpoint V W hH hF

/-- All genuine diagram conditions survive the normalization isomorphism. -/
theorem normalizedSumGrid_isSimplex₂ {n m : SimplexCategory}
    {A : Grid₂ (SSet.OrdinalSubdivision.δ.obj n) m ⥤ C}
    (hA : IsSimplex₂ V.cof V.weq A) :
    IsSimplex₂ W.cof W.weq (normalizedSumGrid V W hH hF A) :=
  simplex₂_of_iso W
    (sumGrid_isSimplex₂ W
      ((hA.precomp V.cof V.weq _ _).postcomp V.cof V.weq hH)
      ((hA.precomp V.cof V.weq _ _).postcomp V.cof V.weq hF))
    (Functor.isoWhiskerLeft (separatedPairGrid A) (normalizedSplitIso V W hH hF))

/-- Independent reindexing of the actual pair of separated restrictions. -/
theorem separatedPairGrid_reindex {n n' m m' : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m) (A : Grid₂ (SSet.OrdinalSubdivision.δ.obj n) m ⥤ C) :
    separatedPairGrid (gridMap₂ (SSet.OrdinalSubdivision.δ.map α) β ⋙ A) =
      gridMap₂ α β ⋙ separatedPairGrid A := by
  change ((gridMap₂ (SSet.OrdinalJoin.left n' n' ≫ SSet.OrdinalSubdivision.δ.map α) β) ⋙ A).prod'
      ((gridMap₂ (SSet.OrdinalJoin.right n' n' ≫ SSet.OrdinalSubdivision.δ.map α) β) ⋙ A) =
    ((gridMap₂ (α ≫ SSet.OrdinalJoin.left n n) β) ⋙ A).prod'
      ((gridMap₂ (α ≫ SSet.OrdinalJoin.right n n) β) ⋙ A)
  exact congrArg₂ (fun f g ↦ (gridMap₂ f β ⋙ A).prod' (gridMap₂ g β ⋙ A))
    (SSet.OrdinalSubdivision.first.naturality α).symm
      (SSet.OrdinalSubdivision.second.naturality α).symm

/-- The same actual common endpoint works for the original and split sequences. -/
def normalizedSumMap : SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V ⟶ bisimplicialSSet W where
  app n := {
    app m := ↾fun A ↦ ⟨normalizedSumGrid V W hH hF A.1,
      normalizedSumGrid_isSimplex₂ V W hH hF A.2⟩
    naturality _ _ _ := by ext A; rfl }
  naturality n n' μ := by
    ext m A
    apply Subtype.ext
    exact congrArg (fun T ↦ T ⋙ normalizedSplitEndpoint V W hH hF)
      (separatedPairGrid_reindex μ.unop (𝟙 m.unop) A.1)

/-- The common normalized endpoint has exactly the chosen zero at every point
of a constant chosen-zero input grid. -/
theorem normalizedSumGrid_zero_obj {n m : SimplexCategory} (x : Grid₂ n m) :
    (normalizedSumGrid V W hH hF
      ((Functor.const (Grid₂ (SSet.OrdinalSubdivision.δ.obj n) m)).obj V.zero)).obj x = W.zero :=
  normalizedSplitEndpoint_obj_zero V W hH hF

end CategoryTheory.Waldhausen.Additivity
