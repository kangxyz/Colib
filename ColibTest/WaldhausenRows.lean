import Colib.CategoryTheory.Waldhausen.Rows.NerveFunctoriality

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v
namespace WaldhausenRowsTests
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D)

example {n : SimplexCategory} (A : Obj V n) (i : Fin (n.len + 1)) :
    IsZero (A.obj.obj (interval i i le_rfl)) := A.property.zero i

example (n k : SimplexCategory) (A : Grid₂ n k ⥤ C)
    (hA : IsSimplex₂ V.cof V.weq A) :
    weakChainToGrid V (gridToWeakChain V A hA) = A :=
  weakChainToGrid_gridToWeakChain V A hA

example (n k : SimplexCategory) (A : ComposableArrows (WeakRows V n) k.len) :
    gridToWeakChain V (weakChainToGrid V A) (weakChainToGrid_isSimplex₂ V A) = A :=
  gridToWeakChain_weakChainToGrid V A

example (n k : SimplexCategory) (A : ComposableArrows (WeakRows V n) k.len)
    {p q : Grid₂ n k} (f : p ⟶ q) :
    (weakChainToGrid V A).map f =
      (A.obj p.1).obj.obj.map (homOfLE (leOfHom f).2) ≫
        (A.map (homOfLE (leOfHom f).1)).hom.hom.app q.2 := rfl

example : sSet V.cof V.weq ≅ SSet.diagonalSSet (weakRowNerve V) :=
  sSetWeakRowDiagonalIso V

example {F : C ⥤ D} (hF : IsExact V.cof V.weq W.cof W.weq F) :
    sSetMap hF ≫ (sSetWeakRowDiagonalIso W).hom =
      (sSetWeakRowDiagonalIso V).hom ≫ SSet.diagonalMap (weakRowNerveMap V W hF) :=
  sSetWeakRowDiagonalIso_naturality V W hF

end WaldhausenRowsTests
