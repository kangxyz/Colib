import Colib.KTheory.Waldhausen.Map

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v
namespace WaldhausenRealizationTests
open CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D)

example (n : ℕ) : Group (W.K n) := inferInstance
example (n : ℕ) : CommGroup (W.K (n + 1)) := inferInstance

example : W.Delooping = SSet.toTop.obj (sSet W.cof W.weq) := rfl

example (n : SimplexCategoryᵒᵖ) :
    (zeroSimplex W.cof W.weq W.zero W.isZero n).val =
      (Functor.const (Grid n.unop)).obj W.zero := rfl

variable {F : C ⥤ D} (hF : IsExact W.cof W.weq V.cof V.weq F)

example : deloopingMap hF = SSet.toTop.map (sSetMap hF) := rfl

example : deloopingMap hF W.kBasepoint =
    basepoint V.cof V.weq (F.obj W.zero) (hF.zero W.isZero) :=
  deloopingMap_basepoint hF W.zero W.isZero

example (n : ℕ) : groupsMap hF W.zero W.isZero n =
    HomotopyGroup.piMap n (deloopingMap hF).hom
      (deloopingMap_basepoint hF W.zero W.isZero) := rfl

example (h : F.obj W.zero = V.zero) (n : ℕ) : W.K n →* V.K n :=
  groupsMapOfZeroEq hF W.zero W.isZero V.zero V.isZero h n

end WaldhausenRealizationTests
