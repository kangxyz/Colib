import Colib.KTheory.Waldhausen.ZeroFunctor
import Colib.KTheory.Waldhausen.Functoriality

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v
namespace WaldhausenZeroFunctorTests
open CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D)

example (X : C) : (zeroFunctor (C := C) W).obj X = W.zero := rfl
example {X Y : C} (f : X ⟶ Y) : (zeroFunctor W).map f = 𝟙 W.zero := rfl
example : IsExact V.cof V.weq W.cof W.weq (zeroFunctor (C := C) W) :=
  zeroFunctor_isExact V W

example : sSetMap (zeroFunctor_isExact V W) =
    SSet.const (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) :=
  sSetMap_zeroFunctor V W

example : (deloopingMap (zeroFunctor_isExact V W)).hom =
    ContinuousMap.const V.Delooping W.kBasepoint := deloopingMap_zeroFunctor V W

example (n : ℕ) (a : V.K n) : KMap (zeroFunctor_isExact V W) n a = 1 := by
  rw [KMap_zeroFunctor]
  rfl

/-- The exact downstream pattern used for truncation-zero endpoints. -/
example {F : C ⥤ D} (hF : IsExact V.cof V.weq W.cof W.weq F)
    (e : F ≅ zeroFunctor W) (n : ℕ) : KMap hF n = 1 :=
  (KMap_eq_of_iso hF (zeroFunctor_isExact V W) e n).trans (KMap_zeroFunctor V W n)

end WaldhausenZeroFunctorTests
