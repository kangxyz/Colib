/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.PushoutDiagram
public import Colib.Topology.HomotopyPullback.DoubleCylinder

/-!
# Genuine fixed-target homotopy-cartesian domain descent

Homotopy-cartesian comparisons with one fixed target map assemble across
actual source and base pushouts with cofibrant corresponding legs. The
homotopy pullback's double-cylinder comparison is proved by its genuine
open collar charts, and both ordinary pushout collapses are actual HEs.
No preservation of an arbitrary quotient pushout by pullback is assumed.
-/
/-! Implementation source: `Quillen/Topology/HomotopyPullback/PushoutDomain.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space comparisons and
pushout hypotheses are retained. -/
@[expose] public section

open TopCat.DoubleCylinder.HomotopyPullback


noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.CartesianDomainPushout
open DoubleCylinder.HomotopyPullback
variable {A B C P A' B' C' P' E T : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ P} {j : C ⟶ P}
  {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ P'} {j' : C' ⟶ P'}
  (sq : IsPushout f g i j) (sq' : IsPushout f' g' i' j')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (wi : i ≫ p = b ≫ i') (wj : j ≫ p = c ≫ j')
  (q : E ⟶ T) (s : P' ⟶ T) (t : P ⟶ E) (w : t ≫ q = p ≫ s)
  (hf : TopCat.HomotopyExtensionProperty f) (hf' : TopCat.HomotopyExtensionProperty f')

/-- Actual HP-domain descent on the base homotopy pushout, followed by
the genuine homotopy equivalent base collapse. -/
def HPComparisonHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (HPCylinder sq' q s) (Topology.HomotopyPullback q.hom s.hom) :=
  (DoubleCylinder.HomotopyPullback.comparisonHomotopyEquiv f' g'
    (DoubleCylinder.cylinderSquare f' g') q (baseLeft (i' := i') s)
    (baseRight (j' := j') s) (baseSquare sq' s) (HPCylinderSquare sq' q s)).trans
      (parameterCollapseHomotopyEquiv sq' q s hf')

@[simp] theorem HPComparisonHomotopyEquiv_toFun :
    (HPComparisonHomotopyEquiv sq' q s hf').toFun = (HPComparison sq' q s).hom := rfl

variable
  (EA : ContinuousMap.HomotopyEquiv A (HA f' q (baseLeft (i' := i') s)))
  (hEA : EA.toFun = (comparisonA a b p wf wi q s t w).hom)
  (EB : ContinuousMap.HomotopyEquiv B (HB q (baseLeft (i' := i') s)))
  (hEB : EB.toFun = (comparisonB b p wi q s t w).hom)
  (EC : ContinuousMap.HomotopyEquiv C (HC q (baseRight (j' := j') s)))
  (hEC : EC.toFun = (comparisonC c p wj q s t w).hom)

/-- Three genuine homotopy-cartesian corner comparisons into a fixed
target assemble into the canonical comparison on the actual pushout.
All diagram maps, both HEP conditions, and all three input equivalences
are explicit; no global realization or descent conclusion is assumed. -/
def homotopyEquiv : ContinuousMap.HomotopyEquiv P (Topology.HomotopyPullback q.hom s.hom) :=
  TopCat.homotopyEquivCancelLeft
    (A := DoubleCylinder.Cylinder f g) (B := P)
    (C := TopCat.of (Topology.HomotopyPullback q.hom s.hom))
    (a := DoubleCylinder.collapseOfPushout sq) (b := totalComparison p q s t w)
    (DoubleCylinder.collapseHomotopyEquiv (DoubleCylinder.cylinderSquare f g) sq hf) rfl
    ((cylinderComparisonHomotopyEquiv sq sq' a b c p wf wg wi wj q s t w EA hEA EB hEB EC hEC).trans
      (HPComparisonHomotopyEquiv sq' q s hf'))
    (congrArg TopCat.Hom.hom (comparison_naturality sq sq' a b c p wf wg wi wj q s t w).symm)

/-- The assembled homotopy equivalence retains exactly the prescribed
canonical constant-path comparison. -/
@[simp] theorem homotopyEquiv_toFun :
    (homotopyEquiv sq sq' a b c p wf wg wi wj q s t w hf hf' EA hEA EB hEB EC hEC).toFun =
      Topology.HomotopyPullback.comparison q.hom s.hom p.hom t.hom
        (congrArg TopCat.Hom.hom w) := rfl

end TopCat.CartesianDomainPushout
