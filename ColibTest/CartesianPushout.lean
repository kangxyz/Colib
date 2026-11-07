module

public import Colib.Topology.HomotopyPullback.Pushout
public import Colib.Topology.HomotopyPullback.PushoutDomain
public import Colib.Topology.HomotopyPullback.Cartesian
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianStageCube

@[expose] public noncomputable section
universe u
open CategoryTheory Limits Topology
open scoped Topology

example {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A]
    [TopologicalSpace B] (f : C(X, B)) (g : C(A, B)) (hf : WeakHomotopyLiftingProperty f) :
    (HomotopyPullback.strictPullbackHomotopyEquivOfWeakLifting f g hf).toFun =
      HomotopyPullback.strictPullbackInclusion f g := rfl

example {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace B] (p : C(X, B)) (q : C(Y, B))
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (e : ContinuousMap.HomotopyEquiv X Y) (w : q.comp e.toFun = p) :
    (fiberwiseEquivOfFibrationHomotopyEquiv p q hp hq e w).toMap = e.toFun :=
  fiberwiseEquivOfFibrationHomotopyEquiv_toMap p q hp hq e w

example {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] {p : C(X, A)} {q : C(Y, B)}
    (f : C(X, Y)) (g : C(A, B)) (w : q.comp f = g.comp p)
    (e : ContinuousMap.HomotopyEquiv X (HomotopyPullback q g))
    (he : e.toFun = HomotopyPullback.comparison q g p f w) :
    (MappingPath.strictComparisonHomotopyEquiv f g w e he).toFun =
      MappingPath.strictComparison f g w := rfl

namespace Cube
variable {A B C P A' B' C' P' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ P} {j : C ⟶ P}
  {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ P'} {j' : C' ⟶ P'}
  (sq : IsPushout f g i j) (sq' : IsPushout f' g' i' j')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (wi : i ≫ p = b ≫ i') (wj : j ≫ p = c ≫ j')
  (hf : TopCat.HomotopyExtensionProperty f) (hf' : TopCat.HomotopyExtensionProperty f')
  (EL : ContinuousMap.HomotopyEquiv A (HomotopyPullback b.hom f'.hom))
  (hEL : EL.toFun = HomotopyPullback.comparison b.hom f'.hom a.hom f.hom
    (congrArg TopCat.Hom.hom wf))
  (ER : ContinuousMap.HomotopyEquiv A (HomotopyPullback c.hom g'.hom))
  (hER : ER.toFun = HomotopyPullback.comparison c.hom g'.hom a.hom g.hom
    (congrArg TopCat.Hom.hom wg))

example : HomotopyPullback.Cartesian b.hom p.hom i.hom i'.hom
    (congrArg TopCat.Hom.hom wi) :=
  TopCat.CartesianPushout.exists_leftHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER

example : HomotopyPullback.Cartesian c.hom p.hom j.hom j'.hom
    (congrArg TopCat.Hom.hom wj) :=
  TopCat.CartesianPushout.exists_rightHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER

example :
    (TopCat.CartesianPushout.leftHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf'
      EL hEL ER hER).toFun =
      HomotopyPullback.comparison p.hom i'.hom b.hom i.hom (congrArg TopCat.Hom.hom wi) :=
  TopCat.CartesianPushout.leftHomotopyEquiv_toFun sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER

example :
    (TopCat.CartesianPushout.rightHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf'
      EL hEL ER hER).toFun =
      HomotopyPullback.comparison p.hom j'.hom c.hom j.hom (congrArg TopCat.Hom.hom wj) :=
  TopCat.CartesianPushout.rightHomotopyEquiv_toFun sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER
end Cube

namespace Domain
open TopCat.CartesianDomainPushout TopCat.DoubleCylinder.HomotopyPullback
variable {A B C P A' B' C' P' E T : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ P} {j : C ⟶ P}
  {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ P'} {j' : C' ⟶ P'}
  (sq : IsPushout f g i j) (sq' : IsPushout f' g' i' j')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (wi : i ≫ p = b ≫ i') (wj : j ≫ p = c ≫ j')
  (q : E ⟶ T) (s : P' ⟶ T) (t : P ⟶ E) (w : t ≫ q = p ≫ s)
  (hf : TopCat.HomotopyExtensionProperty f) (hf' : TopCat.HomotopyExtensionProperty f')
  (EA : ContinuousMap.HomotopyEquiv A (HA f' q (baseLeft (i' := i') s)))
  (hEA : EA.toFun = (comparisonA a b p wf wi q s t w).hom)
  (EB : ContinuousMap.HomotopyEquiv B (HB q (baseLeft (i' := i') s)))
  (hEB : EB.toFun = (comparisonB b p wi q s t w).hom)
  (EC : ContinuousMap.HomotopyEquiv C (HC q (baseRight (j' := j') s)))
  (hEC : EC.toFun = (comparisonC c p wj q s t w).hom)

example :
    (homotopyEquiv sq sq' a b c p wf wg wi wj q s t w hf hf' EA hEA EB hEB EC hEC).toFun =
      HomotopyPullback.comparison q.hom s.hom p.hom t.hom (congrArg TopCat.Hom.hom w) := rfl

example : HomotopyPullback.Cartesian p.hom q.hom t.hom s.hom (congrArg TopCat.Hom.hom w) :=
  ⟨homotopyEquiv sq sq' a b c p wf wg wi wj q s t w hf hf' EA hEA EB hEB EC hEC, rfl⟩
end Domain

namespace Skeletal
open CategoryTheory.TheoremB.Skeletal HomotopyPullback
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

example (n : ℕ)
    (hboundary : Cartesian (cellBoundaryProjection η n).hom (cellProjection η n).hom
      (boundaryLeg H n).hom (boundaryLeg J n).hom
      (congrArg TopCat.Hom.hom (cellBoundarySquare η n)))
    (hattaching : Cartesian (cellBoundaryProjection η n).hom (stageProjection η n).hom
      (attachingLeg H n).hom (attachingLeg J n).hom
      (congrArg TopCat.Hom.hom (cellAttachingSquare η n))) :
    Cartesian (stageProjection η n).hom (stageProjection η (n + 1)).hom
      (stageStep H n).hom (stageStep J n).hom
      (congrArg TopCat.Hom.hom (stageStepSquare η n)) :=
  (successor_cartesian_of_incoming η n hboundary hattaching).1
end Skeletal
