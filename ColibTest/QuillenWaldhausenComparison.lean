module
import Colib.KTheory.Waldhausen.QuillenComparison.Equivalence

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.QuillenComparison
open scoped Simplicial ZeroObject
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactCategory.ExactStructure C)

example : (ofExactCategory E).cof = E.inflation := rfl
example : (ofExactCategory E).weq = MorphismProperty.isomorphisms C := rfl

example {n : SimplexCategory} (F : Obj (ofExactCategory E) n)
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    E.deflation (rowMap E F (hij.trans hjk) hjk hij le_rfl) :=
  row_deflation E F i j k hij hjk

example {n : SimplexCategory} (F : Obj (ofExactCategory E) n)
    {p q r : NestedInterval n} (hpq : p ≤ q) (hqr : q ≤ r) :
    QConstruction.mkHom E.deflation E.inflation (intervalSpan E F hpq) ≫
      QConstruction.mkHom E.deflation E.inflation (intervalSpan E F hqr) =
        QConstruction.mkHom E.deflation E.inflation (intervalSpan E F (hpq.trans hqr)) :=
  intervalSpan_comp E F hpq hqr

example {n : SimplexCategory} {F G : WeakRows (ofExactCategory E) n} (η : F ⟶ G)
    (p : Interval n) : (weakRowIso E η).hom.app p = η.hom.hom.app p := rfl

example {n : SimplexCategory}
    (F : (sSet E.inflation (MorphismProperty.isomorphisms C)).obj
      (op (SSet.EdgewiseSubdivision.ε.obj n))) (i : Fin (n.len + 1)) :
    (comparisonSimplex E F).obj i =
      QConstruction.of E.deflation E.inflation
        (F.val.obj (grid (upperIndex n i) (lowerIndex n i) (upperIndex n i)
          (lowerIndex_le_upperIndex n i i))) := comparisonSimplex_obj E F i

example : (comparisonMap E).app (op ⦋0⦌) (subdivisionZeroVertex E) =
    nerveVertex (QConstruction.of E.deflation E.inflation (0 : C)) :=
  comparisonMap_zeroVertex E

example (n : ℕ) : (ofExactCategory E).K n →* E.K n := comparisonK E n

example (n : ℕ) :
    (subdivisionKEquiv E n : SubdivisionK E n →* (ofExactCategory E).K n) =
      subdivisionEndpointK E n := subdivisionKEquiv_coe E n

example (n : ℕ) : (comparisonK E n).comp (subdivisionEndpointK E n) =
    subdivisionComparisonK E n := comparisonK_comp_endpoint E n

example (n : ℕ) (f : (ofExactCategory E).K n →* E.K n)
    (h : f.comp (subdivisionEndpointK E n) = subdivisionComparisonK E n) :
    f = comparisonK E n := comparisonK_unique E n f h

example : (lowerIndex ⦋1⦌ 0).val = 1 := rfl
example : (lowerIndex ⦋1⦌ 1).val = 0 := rfl
example : (upperIndex ⦋1⦌ 0).val = 2 := rfl
example : (upperIndex ⦋1⦌ 1).val = 3 := rfl

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
  {E' : ExactCategory.ExactStructure D} (F : ExactCategory.ExactFunctor E E')

example : IsExact (ofExactCategory E).cof (ofExactCategory E).weq
    (ofExactCategory E').cof (ofExactCategory E').weq F.toFunctor := F.waldhausenExact

example :
    SSet.EdgewiseSubdivision.subdivisionFunctor.map (sSetMap F.waldhausenExact) ≫
      comparisonMap E' = comparisonMap E ≫ nerveMap F.mapQ := comparisonMap_naturality F


example (n : ℕ) :
    (comparisonK E' n).comp (Waldhausen.KMap F.waldhausenExact n) =
      (F.KMap n).comp (comparisonK E n) := comparisonK_naturality F n

example :
    (comparisonK E' 0).comp (Waldhausen.KMap F.waldhausenExact 0) =
      (F.KMap 0).comp (comparisonK E 0) := comparisonK_naturality F 0

example : F.zeroNormalized.toFunctor.obj (0 : C) = (0 : D) :=
  F.zeroNormalized_obj_zero

example (n : ℕ) : F.zeroNormalized.KMap n = F.KMap n := F.zeroNormalized_KMap n

example (G : ExactCategory.ExactFunctor E E') (e : F.toFunctor ≅ G.toFunctor) (n : ℕ) :
    F.KMap n = G.KMap n := ExactCategory.ExactFunctor.KMap_eq_of_natIso e n

example :
    subdivisionToRows E ≫ rowsToQ E = comparisonMap E := comparisonMap_factorization E

example : (realizationComparisonHomotopyEquiv E).toFun =
    (realizationComparison E).hom := rfl

example : realizationComparisonHomotopyEquiv E (subdivisionBasepoint E) = E.kBasepoint :=
  realizationComparisonHomotopyEquiv_basepoint E

example : ContinuousMap.HomotopyEquiv (ofExactCategory E).Delooping E.KSpace :=
  deloopingHomotopyEquiv E

example (n : ℕ) : (ofExactCategory E).K n ≃* E.K n := comparisonKEquiv E n

example (n : ℕ) :
    (comparisonKEquiv E n : (ofExactCategory E).K n →* E.K n) = comparisonK E n := rfl

example (n : ℕ) (x : (ofExactCategory E).K n) :
    (comparisonKEquiv E n).symm (comparisonK E n x) = x :=
  (comparisonKEquiv E n).symm_apply_apply x

example (n : ℕ) (y : E.K n) :
    comparisonK E n ((comparisonKEquiv E n).symm y) = y :=
  (comparisonKEquiv E n).apply_symm_apply y

example (n : ℕ) :
    (comparisonKEquiv E' n).toMonoidHom.comp (Waldhausen.KMap F.waldhausenExact n) =
      (F.KMap n).comp (comparisonKEquiv E n).toMonoidHom :=
  comparisonKEquiv_exactFunctor_naturality E F n

example :
    (comparisonKEquiv E' 0).toMonoidHom.comp (Waldhausen.KMap F.waldhausenExact 0) =
      (F.KMap 0).comp (comparisonKEquiv E 0).toMonoidHom :=
  comparisonKEquiv_exactFunctor_naturality E F 0

example {A B : Type u} [SmallCategory A] [SmallCategory B] (G : A ⥤ B) :
    MixedNerve.nerveMap.{u, u, u} G = nerveMap G := rfl

example {A B : Type u} [SmallCategory A] [SmallCategory B] (e : A ≌ B) :
    (MixedNerve.realizationEquivalence.{u, u, u} e).toFun =
      (SSet.toTop.map (nerveMap e.functor)).hom := rfl
