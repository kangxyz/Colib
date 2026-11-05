import Colib.KTheory.Waldhausen.KFunctor

noncomputable section

open CategoryTheory CategoryTheory.Limits
universe u v
namespace WaldhausenKFunctorTests
open CategoryTheory.Waldhausen
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (V : Structure C) (W : Structure D) (U : Structure E)
  {F G : C ⥤ D} {J : D ⥤ E}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hJ : IsExact W.cof W.weq U.cof U.weq J)

example (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X)) (n : ℕ) :
    KMap hF n = KMap hG n := KMap_eq_of_weakNatTrans hF hG η hη n

example (n : ℕ) : (KMap hJ n).comp (KMap hF n) = KMap (hF.comp hJ) n :=
  KMap_comp_KMap hF hJ n

example (n : ℕ) : SmallWaldhausenCategory.{u} ⥤ GrpCat.{u} :=
  SmallWaldhausenCategory.KFunctor n

end WaldhausenKFunctorTests
