/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.WeakInvariance
public import Colib.Topology.HomotopyPullback.PushoutDomain

/-!
# Fixed-target weak-cartesian domain pushout descent

Three original weak corner comparisons assemble to the unchanged canonical
comparison on the actual pushout. The objectwise weak double-cylinder map is
followed by the genuine homotopy-pullback cylinder comparison; both specified
cofibrant pushout legs supply actual collapse homotopy equivalences.


Implementation provenance:
`Quillen/Topology/HomotopyPullback/WeakPushoutDomain.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open TopCat.DoubleCylinder.HomotopyPullback


noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace TopCat.CartesianDomainPushout
open TopCat.DoubleCylinder.HomotopyPullback
variable {A B C P A' B' C' P' E T : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ P} {j : C ⟶ P}
  {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ P'} {j' : C' ⟶ P'}
  (sq : IsPushout f g i j) (sq' : IsPushout f' g' i' j')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (wi : i ≫ p = b ≫ i') (wj : j ≫ p = c ≫ j')
  (q : E ⟶ T) (s : P' ⟶ T) (t : P ⟶ E) (w : t ≫ q = p ≫ s)

/-- Weak original corner comparisons induce weakness of the literal map
between the actual source and homotopy-pullback double cylinders. -/
theorem cylinderComparison_isWeakHomotopyEquivalence
    (hA : IsWeakHomotopyEquivalence (comparisonA a b p wf wi q s t w).hom)
    (hB : IsWeakHomotopyEquivalence (comparisonB b p wi q s t w).hom)
    (hC : IsWeakHomotopyEquivalence (comparisonC c p wj q s t w).hom) :
    IsWeakHomotopyEquivalence (cylinderComparison sq sq' a b c p wf wg wi wj q s t w).hom :=
  DoubleCylinder.map_isWeakHomotopyEquivalence
    (DoubleCylinder.cylinderSquare f g) (HPCylinderSquare sq' q s)
    (comparisonA a b p wf wi q s t w) (comparisonB b p wi q s t w)
    (comparisonC c p wj q s t w)
    (comparison_left a b p wf wi q s t w)
    (comparison_right sq sq' a b c p wf wg wi wj q s t w) hA hB hC

include sq sq' wf wg wi wj in
/-- Three weak homotopy-cartesian corner comparisons into one fixed target
assemble across the displayed actual source and base pushouts. The result
is the complete weak property of the unchanged constant-path comparison. -/
theorem comparison_isWeakHomotopyEquivalence
    (hf : TopCat.HomotopyExtensionProperty f)
    (hf' : TopCat.HomotopyExtensionProperty f')
    (hA : IsWeakHomotopyEquivalence (comparisonA a b p wf wi q s t w).hom)
    (hB : IsWeakHomotopyEquivalence (comparisonB b p wi q s t w).hom)
    (hC : IsWeakHomotopyEquivalence (comparisonC c p wj q s t w).hom) :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison q.hom s.hom p.hom t.hom (congrArg TopCat.Hom.hom w)) := by
  have hw := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (HPComparisonHomotopyEquiv sq' q s hf')).comp
      (cylinderComparison_isWeakHomotopyEquivalence sq sq' a b c p wf wg wi wj q s t w hA hB hC)
  have he := congrArg TopCat.Hom.hom
    (comparison_naturality sq sq' a b c p wf wg wi wj q s t w)
  change (totalComparison p q s t w).hom.comp (DoubleCylinder.collapseOfPushout sq).hom =
    (HPComparison sq' q s).hom.comp
      (cylinderComparison sq sq' a b c p wf wg wi wj q s t w).hom at he
  rw [HPComparisonHomotopyEquiv_toFun,← he] at hw
  exact hw.of_comp_left (isWeakHomotopyEquivalence_of_homotopyEquiv
    (DoubleCylinder.collapseHomotopyEquiv (DoubleCylinder.cylinderSquare f g) sq hf))

end TopCat.CartesianDomainPushout
