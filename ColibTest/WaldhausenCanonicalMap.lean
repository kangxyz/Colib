import Colib.KTheory.Waldhausen.CanonicalMap

noncomputable section

open CategoryTheory CategoryTheory.Limits
universe u v
namespace WaldhausenCanonicalMapTests
open CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

example (n : ℕ) : V.K n →* W.K n := KMap hF n
example : deloopingMap hF.rebase V.kBasepoint = W.kBasepoint := KMap_basepoint hF
example (n : ℕ) : KMap hF n = HomotopyGroup.piMap n
    (deloopingMap hF.rebase).hom (KMap_basepoint hF) := KMap_eq_piMap hF n
example (n : ℕ) : KMap (IsExact.id V.cof V.weq) n = MonoidHom.id (V.K n) :=
  KMap_id V n

end WaldhausenCanonicalMapTests
