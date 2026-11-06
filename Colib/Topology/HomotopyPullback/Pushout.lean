/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.Cartesian
public import Colib.Topology.DoubleMappingCylinder.Collapse
public import Colib.Topology.HomotopyPullback.Symmetry
public import Colib.Topology.HomotopyPullback.Restriction

/-!
# The genuine homotopy-cartesian cofibrant pushout cube

For a strictly commuting map of ordinary TopCat pushout squares with
cofibrant corresponding legs, homotopy-cartesianness of the two incoming
squares implies homotopy-cartesianness of both outgoing squares. The proof
constructs double cylinders, applies finite homotopy-cartesian gluing, and
pastes with their actual homotopy-equivalent collapses.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyPullback/Pushout.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.CartesianPushout

open DoubleCylinder

variable {A B C P A' B' C' P' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ P} {j : C ⟶ P}
  {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ P'} {j' : C' ⟶ P'}
  (sq : IsPushout f g i j) (sq' : IsPushout f' g' i' j')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (wi : i ≫ p = b ≫ i') (wj : j ≫ p = c ≫ j')
  (hf : TopCat.HomotopyExtensionProperty f) (hf' : TopCat.HomotopyExtensionProperty f')

/-- The double-cylinder map induced by the strictly commuting span maps `a`, `b`, and `c`. -/
abbrev cylinderMap : Cylinder f g ⟶ Cylinder f' g' :=
  DoubleCylinder.map (cylinderSquare f g) (cylinderSquare f' g') a b c wf wg
include wi wj in
theorem collapse_square : p.hom.comp (collapseOfPushout sq).hom =
    (collapseOfPushout sq').hom.comp (cylinderMap a b c wf wg).hom :=
  congrArg TopCat.Hom.hom
    (DoubleCylinder.collapse_naturality (cylinderSquare f g) sq (cylinderSquare f' g') sq'
      a b c p wf wg wi wj).symm

/-- The two cofibrant collapses form a homotopy-cartesian square because
both horizontal maps are actual ordinary homotopy equivalences. -/
def collapseSquareEquiv : ContinuousMap.HomotopyEquiv (Cylinder f g)
    (HomotopyPullback p.hom (collapseOfPushout sq').hom) :=
  Topology.homotopyEquivCancelRight
    (a := HomotopyPullback.comparison p.hom (collapseOfPushout sq').hom
      (cylinderMap a b c wf wg).hom (collapseOfPushout sq).hom
      (collapse_square sq sq' a b c p wf wg wi wj))
    (HomotopyPullback.sourceProjectionEquivOfParameterEquiv p.hom (collapseOfPushout sq').hom
      (DoubleCylinder.collapseHomotopyEquiv (cylinderSquare f' g') sq' hf') rfl) rfl
    (DoubleCylinder.collapseHomotopyEquiv (cylinderSquare f g) sq hf) rfl

@[simp] theorem collapseSquareEquiv_toFun :
    (collapseSquareEquiv sq sq' a b c p wf wg wi wj hf hf').toFun =
      HomotopyPullback.comparison p.hom (collapseOfPushout sq').hom
        (cylinderMap a b c wf wg).hom (collapseOfPushout sq).hom
      (collapse_square sq sq' a b c p wf wg wi
          wj) := rfl

variable
  (EL : ContinuousMap.HomotopyEquiv A (HomotopyPullback b.hom f'.hom))
  (hEL : EL.toFun = HomotopyPullback.comparison b.hom f'.hom a.hom f.hom (congrArg
    TopCat.Hom.hom wf))
  (ER : ContinuousMap.HomotopyEquiv A (HomotopyPullback c.hom g'.hom))
  (hER : ER.toFun = HomotopyPullback.comparison c.hom g'.hom a.hom g.hom (congrArg
    TopCat.Hom.hom wg))

include sq sq' wf wg wi wj hf hf' hEL hER in
/-- Actual canonical homotopy-cartesianness of the outgoing left square. -/
theorem exists_leftHomotopyEquiv :
    ∃ E : ContinuousMap.HomotopyEquiv B (HomotopyPullback p.hom i'.hom),
      E.toFun = HomotopyPullback.comparison p.hom i'.hom b.hom i.hom (congrArg TopCat.Hom.hom
        wi) := by
  let e0 := DoubleCylinder.Cartesian.leftEndHomotopyEquiv (cylinderSquare f g) (cylinderSquare
    f' g')
    a b c wf wg EL hEL ER hER
  let e1 := collapseSquareEquiv sq sq' a b c p wf wg wi wj hf hf'
  let E := HomotopyPullback.pastingHomotopyEquiv b.hom (cylinderMap a b c wf wg).hom p.hom
    (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f g)).hom (collapseOfPushout sq).hom
    (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f' g')).hom (collapseOfPushout sq').hom
    (DoubleCylinder.FiniteNormalization.left_square (cylinderSquare f g) (cylinderSquare f' g')
      a b c wf wg)
    (collapse_square sq sq' a b c p wf wg wi wj) e0
    (DoubleCylinder.Cartesian.leftEndHomotopyEquiv_toFun _ _ _ _ _ _ _ _ _ _ _) e1 rfl
  have hl : (collapseOfPushout sq).hom.comp (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f
    g)).hom = i.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_leftEnd (cylinderSquare f g) sq)
  have hb : (collapseOfPushout sq').hom.comp
      (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f'
    g')).hom = i'.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_leftEnd (cylinderSquare f' g') sq')
  refine ⟨E.trans (Topology.HomotopyPullback.baseMapCongr p.hom _ i'.hom hb).toHomotopyEquiv, ?_⟩
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (b x, collapseOfPushout sq (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f g) x),
      ContinuousMap.const unitInterval
        (collapseOfPushout sq'
          (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f' g') (b x)))) =
    (b x, i x, ContinuousMap.const unitInterval (i' (b x)))
  exact Prod.ext rfl (Prod.ext (ContinuousMap.congr_fun hl x)
    (ContinuousMap.ext (fun _ ↦ ContinuousMap.congr_fun hb (b x))))

include sq sq' wf wg wi wj hf hf' hEL hER in
/-- The corresponding actual canonical outgoing right comparison. -/
theorem exists_rightHomotopyEquiv :
    ∃ E : ContinuousMap.HomotopyEquiv C (HomotopyPullback p.hom j'.hom),
      E.toFun = HomotopyPullback.comparison p.hom j'.hom c.hom j.hom (congrArg TopCat.Hom.hom
        wj) := by
  let e0 := DoubleCylinder.Cartesian.rightEndHomotopyEquiv (cylinderSquare f g) (cylinderSquare
    f' g')
    a b c wf wg EL hEL ER hER
  let e1 := collapseSquareEquiv sq sq' a b c p wf wg wi wj hf hf'
  let E := HomotopyPullback.pastingHomotopyEquiv c.hom (cylinderMap a b c wf wg).hom p.hom
    (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f g)).hom (collapseOfPushout sq).hom
    (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f' g')).hom (collapseOfPushout sq').hom
    (DoubleCylinder.FiniteNormalization.right_square (cylinderSquare f g) (cylinderSquare f' g')
      a b c wf wg)
    (collapse_square sq sq' a b c p wf wg wi wj) e0
    (DoubleCylinder.Cartesian.rightEndHomotopyEquiv_toFun _ _ _ _ _ _ _ _ _ _ _) e1 rfl
  have hr : (collapseOfPushout sq).hom.comp (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f
    g)).hom = j.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_rightEnd (cylinderSquare f g) sq)
  have hc : (collapseOfPushout sq').hom.comp (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd
    f' g')).hom = j'.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_rightEnd (cylinderSquare f' g') sq')
  refine ⟨E.trans (Topology.HomotopyPullback.baseMapCongr p.hom _ j'.hom hc).toHomotopyEquiv, ?_⟩
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (c x, collapseOfPushout sq (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f g) x),
      ContinuousMap.const unitInterval
        (collapseOfPushout sq'
          (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f' g') (c x)))) =
    (c x, j x, ContinuousMap.const unitInterval (j' (c x)))
  exact Prod.ext rfl (Prod.ext (ContinuousMap.congr_fun hr x)
    (ContinuousMap.ext (fun _ ↦ ContinuousMap.congr_fun hc (c x))))

/-- A chosen actual left comparison equivalence, with its exact forward map. -/
def leftHomotopyEquiv : ContinuousMap.HomotopyEquiv B (HomotopyPullback p.hom i'.hom) :=
  (exists_leftHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).choose
@[simp] theorem leftHomotopyEquiv_toFun :
    (leftHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).toFun =
      HomotopyPullback.comparison p.hom i'.hom b.hom i.hom (congrArg TopCat.Hom.hom wi) :=
  (exists_leftHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).choose_spec

/-- A chosen actual right comparison equivalence, with its exact forward map. -/
def rightHomotopyEquiv : ContinuousMap.HomotopyEquiv C (HomotopyPullback p.hom j'.hom) :=
  (exists_rightHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).choose
@[simp] theorem rightHomotopyEquiv_toFun :
    (rightHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).toFun =
      HomotopyPullback.comparison p.hom j'.hom c.hom j.hom (congrArg TopCat.Hom.hom wj) :=
  (exists_rightHomotopyEquiv sq sq' a b c p wf wg wi wj hf hf' EL hEL ER hER).choose_spec

end TopCat.CartesianPushout
