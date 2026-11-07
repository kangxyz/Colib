/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.DoubleCylinder
public import Colib.Topology.HomotopyPullback.Symmetry
public import Colib.Topology.DoubleMappingCylinder.Collapse

/-! The strict diagram of canonical corner comparisons used in
fixed-target homotopy-cartesian pushout descent. -/
/-! Implementation source: `Quillen/Topology/HomotopyPullback/PushoutDiagram.lean` at
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

/-- The fixed-target parameter on `B'`, obtained by composing its pushout map with `s : P' ⟶ T`. -/
abbrev baseLeft : B' ⟶ T := i' ≫ s
/-- The fixed-target parameter on `C'`, obtained by composing its pushout map with `s : P' ⟶ T`. -/
abbrev baseRight : C' ⟶ T := j' ≫ s
include sq' in
theorem baseSquare : f' ≫ baseLeft (i' := i') s = g' ≫ baseRight (j' := j') s := sq'.w_assoc s

include wi w in
theorem leftSquare : (i ≫ t) ≫ q = b ≫ baseLeft (i' := i') s := by
  rw [Category.assoc, w, ← Category.assoc, wi, Category.assoc]
include wj w in
theorem rightSquare : (j ≫ t) ≫ q = c ≫ baseRight (j' := j') s := by
  rw [Category.assoc, w, ← Category.assoc, wj, Category.assoc]
include wf wi w in
theorem sourceSquare : (f ≫ i ≫ t) ≫ q = a ≫ f' ≫ baseLeft (i' := i') s := by
  rw [Category.assoc, leftSquare b p wi q s t w, ← Category.assoc, wf, Category.assoc]

/-- The canonical constant-path comparison from `A` to the source homotopy pullback, with
coordinates `a` and `f ≫ i ≫ t`. -/
def comparisonA : A ⟶ HA f' q (baseLeft (i' := i') s) := TopCat.ofHom
  (Topology.HomotopyPullback.comparison q.hom (f' ≫ baseLeft (i' := i') s).hom a.hom (f ≫ i ≫ t).hom
    (congrArg TopCat.Hom.hom (sourceSquare a b p wf wi q s t w)))
/-- The canonical constant-path comparison from `B` to the left homotopy pullback, with
coordinates `b` and `i ≫ t`. -/
def comparisonB : B ⟶ HB q (baseLeft (i' := i') s) := TopCat.ofHom
  (Topology.HomotopyPullback.comparison q.hom (baseLeft (i' := i') s).hom b.hom (i ≫ t).hom
    (congrArg TopCat.Hom.hom (leftSquare b p wi q s t w)))
/-- The canonical constant-path comparison from `C` to the right homotopy pullback, with
coordinates `c` and `j ≫ t`. -/
def comparisonC : C ⟶ HC q (baseRight (j' := j') s) := TopCat.ofHom
  (Topology.HomotopyPullback.comparison q.hom (baseRight (j' := j') s).hom c.hom (j ≫ t).hom
    (congrArg TopCat.Hom.hom (rightSquare c p wj q s t w)))

include wf in
theorem comparison_left : f ≫ comparisonB b p wi q s t w =
    comparisonA a b p wf wi q s t w ≫ leftLeg f' q (baseLeft (i' := i') s) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  exact Prod.ext (ConcreteCategory.congr_hom wf x) (Prod.ext rfl
    (ContinuousMap.ext fun _ ↦ congrArg (baseLeft (i' := i') s) (ConcreteCategory.congr_hom wf x)))

include sq wg in
theorem comparison_right : g ≫ comparisonC c p wj q s t w =
    comparisonA a b p wf wi q s t w ≫ rightLeg f' g' q (baseLeft (i' := i') s) (baseRight (j' :=
      j') s) (baseSquare sq' s) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact ConcreteCategory.congr_hom wg x
  · apply Prod.ext
    · exact congrArg t (ConcreteCategory.congr_hom sq.w x).symm
    · apply ContinuousMap.ext
      intro r
      exact (congrArg (baseRight (j' := j') s) (ConcreteCategory.congr_hom wg x)).trans
        (ConcreteCategory.congr_hom (baseSquare sq' s) (a x)).symm

/-- The left leg of the homotopy-pullback span over the fixed target `T`. -/
abbrev HPLeft := leftLeg f' q (baseLeft (i' := i') s)
/-- The right leg of the homotopy-pullback span, using the base pushout square to identify the
two parameters. -/
abbrev HPRight := rightLeg f' g' q (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare
    sq' s)
/-- The double mapping cylinder of the left and right legs of the homotopy-pullback span. -/
abbrev HPCylinder := DoubleCylinder.Cylinder (HPLeft (f' := f') (i' := i') q s) (HPRight sq' q s)
/-- The canonical pushout square presenting the double mapping cylinder of the homotopy-pullback
span. -/
abbrev HPCylinderSquare := DoubleCylinder.cylinderSquare (HPLeft (f' := f') (i' := i') q s)
    (HPRight sq' q s)

/-- The strict map of spans whose three components are the given canonical
homotopy-cartesian corner comparisons. -/
abbrev cylinderComparison : DoubleCylinder.Cylinder f g ⟶ HPCylinder sq' q s :=
  DoubleCylinder.map (DoubleCylinder.cylinderSquare f g) (HPCylinderSquare sq' q s)
    (comparisonA a b p wf wi q s t w) (comparisonB b p wi q s t w) (comparisonC c p wj q s t w)
    (comparison_left a b p wf wi q s t w) (comparison_right sq sq' a b c p wf wg wi wj q s t w)

/-- Actual componentwise equivalences glue on their ordinary double cylinders. -/
def cylinderComparisonHomotopyEquiv
    (EA : ContinuousMap.HomotopyEquiv A (HA f' q (baseLeft (i' := i') s)))
    (hEA : EA.toFun = (comparisonA a b p wf wi q s t w).hom)
    (EB : ContinuousMap.HomotopyEquiv B (HB q (baseLeft (i' := i') s)))
    (hEB : EB.toFun = (comparisonB b p wi q s t w).hom)
    (EC : ContinuousMap.HomotopyEquiv C (HC q (baseRight (j' := j') s)))
    (hEC : EC.toFun = (comparisonC c p wj q s t w).hom) :
    ContinuousMap.HomotopyEquiv (DoubleCylinder.Cylinder f g) (HPCylinder sq' q s) :=
  DoubleCylinder.mapHomotopyEquiv (DoubleCylinder.cylinderSquare f g) (HPCylinderSquare sq' q s)
    (comparisonA a b p wf wi q s t w) (comparisonB b p wi q s t w) (comparisonC c p wj q s t w)
    (comparison_left a b p wf wi q s t w) (comparison_right sq sq' a b c p wf wg wi wj q s t w)
    EA hEA EB hEB EC hEC

/-- The parameter map from the base double cylinder to `T` induced by `baseLeft` and `baseRight`. -/
abbrev baseParameter : DoubleCylinder.Cylinder f' g' ⟶ T :=
  parameter f' g' (DoubleCylinder.cylinderSquare f' g') (baseLeft (i' := i') s) (baseRight (j'
    := j') s) (baseSquare sq' s)

/-- The fixed-target parameter on the base double cylinder is exactly the
ordinary collapse followed by the specified base map. -/
theorem baseParameter_eq : baseParameter sq' s = DoubleCylinder.collapseOfPushout sq' ≫ s := by
  apply (DoubleCylinder.cylinderSquare f' g').hom_ext
  · apply ConcreteCategory.hom_ext
    intro z
    exact (parameter_cylinder f' g' (DoubleCylinder.cylinderSquare f' g')
      (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare sq' s) z.1 z.2).trans
        (congrArg s (DoubleCylinder.collapse_cylinder_apply (DoubleCylinder.cylinderSquare f'
          g') sq' z.1 z.2)).symm
  · apply ConcreteCategory.hom_ext
    intro z
    cases z with
    | inl x =>
      exact (parameter_left f' g' (DoubleCylinder.cylinderSquare f' g')
        (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare sq' s) x).trans
          (congrArg s (DoubleCylinder.collapse_left (DoubleCylinder.cylinderSquare f' g') sq'
            x)).symm
    | inr x =>
      exact (parameter_right f' g' (DoubleCylinder.cylinderSquare f' g')
        (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare sq' s) x).trans
          (congrArg s (DoubleCylinder.collapse_right (DoubleCylinder.cylinderSquare f' g') sq'
            x)).symm

/-- Collapse only the parameter coordinate, retaining the source and the
entire compact-open path in the fixed target. -/
def parameterCollapse : C(Topology.HomotopyPullback q.hom (baseParameter sq' s).hom,
    Topology.HomotopyPullback q.hom s.hom) where
  toFun z := ⟨(DoubleCylinder.collapseOfPushout sq' z.1.1, z.1.2), z.2.1,
    z.2.2.trans (ConcreteCategory.congr_hom (baseParameter_eq sq' s) z.1.1)⟩
  continuous_toFun := by fun_prop

@[simp] theorem parameterCollapse_val
    (z : Topology.HomotopyPullback q.hom (baseParameter sq' s).hom) :
    (parameterCollapse sq' q s z).1 = (DoubleCylinder.collapseOfPushout sq' z.1.1, z.1.2) := rfl

/-- The actual parameter collapse is HE when the base attachment has HEP. -/
def parameterCollapseHomotopyEquiv (hf' : TopCat.HomotopyExtensionProperty f') :
    ContinuousMap.HomotopyEquiv (Topology.HomotopyPullback q.hom (baseParameter sq' s).hom)
      (Topology.HomotopyPullback q.hom s.hom) := by
  let e0 := (Topology.HomotopyPullback.baseMapCongr q.hom (baseParameter sq' s).hom
    (s.hom.comp (DoubleCylinder.collapseOfPushout sq').hom)
    (congrArg TopCat.Hom.hom (baseParameter_eq sq' s))).toHomotopyEquiv
  let e1 := Topology.HomotopyPullback.parameterEquiv q.hom s.hom
    (DoubleCylinder.collapseHomotopyEquiv (DoubleCylinder.cylinderSquare f' g') sq' hf')
  let E := e0.trans e1
  have hE : E.toFun = parameterCollapse sq' q s := by ext z; rfl
  exact { E with toFun := parameterCollapse sq' q s
                 left_inv := by simpa only [hE] using E.left_inv
                 right_inv := by simpa only [hE] using E.right_inv }

@[simp] theorem parameterCollapseHomotopyEquiv_toFun (hf' : TopCat.HomotopyExtensionProperty f') :
    (parameterCollapseHomotopyEquiv sq' q s hf').toFun = parameterCollapse sq' q s := rfl

/-- The path-space comparison for the base double cylinder followed by
the actual base collapse. -/
def HPComparison : HPCylinder sq' q s ⟶ TopCat.of (Topology.HomotopyPullback q.hom s.hom) :=
  DoubleCylinder.HomotopyPullback.comparison f' g' (DoubleCylinder.cylinderSquare f' g') q
    (baseLeft (i' := i') s) (baseRight (j' := j') s) (baseSquare sq' s) (HPCylinderSquare sq' q s) ≫
      TopCat.ofHom (parameterCollapse sq' q s)

/-- The prescribed canonical comparison on the ordinary pushout vertex. -/
def totalComparison : P ⟶ TopCat.of (Topology.HomotopyPullback q.hom s.hom) := TopCat.ofHom
  (Topology.HomotopyPullback.comparison q.hom s.hom p.hom t.hom (congrArg TopCat.Hom.hom w))

include sq sq' wf wg wi wj in
/-- All constructions retain the actual global canonical comparison. -/
theorem comparison_naturality :
    DoubleCylinder.collapseOfPushout sq ≫ totalComparison p q s t w =
      cylinderComparison sq sq' a b c p wf wg wi wj q s t w ≫ HPComparison sq' q s := by
  apply (DoubleCylinder.cylinderSquare f g).hom_ext
  · apply ConcreteCategory.hom_ext
    rintro ⟨x, r⟩
    change totalComparison p q s t w (DoubleCylinder.collapseOfPushout sq
      (DoubleCylinder.cylinderLine f g (x, r))) =
      HPComparison sq' q s (cylinderComparison sq sq' a b c p wf wg wi wj q s t w
        (DoubleCylinder.cylinderLine f g (x, r)))
    rw [DoubleCylinder.collapse_cylinder_apply, DoubleCylinder.map_cylinder_apply]
    apply Subtype.ext
    have hk := DoubleCylinder.HomotopyPullback.comparison_cylinder f' g'
      (DoubleCylinder.cylinderSquare f' g') q (baseLeft (i' := i') s)
      (baseRight (j' := j') s) (baseSquare sq' s) (HPCylinderSquare sq' q s)
      (comparisonA a b p wf wi q s t w x) r
    have hk' := congrArg (fun z : DoubleCylinder.Cylinder f' g' × (E × C(unitInterval, T)) ↦
      (DoubleCylinder.collapseOfPushout sq' z.1, z.2)) hk
    apply Eq.trans _ hk'.symm
    change (p (i (f x)), t (i (f x)), ContinuousMap.const unitInterval (s (p (i (f x))))) =
      (DoubleCylinder.collapseOfPushout sq' (DoubleCylinder.cylinderLine f' g' (a x, r)),
        t (i (f x)), ContinuousMap.const unitInterval (s (i' (f' (a x)))))
    rw [DoubleCylinder.collapse_cylinder_apply]
    have hx : p (i (f x)) = i' (f' (a x)) :=
      (ConcreteCategory.congr_hom wi (f x)).trans (congrArg i' (ConcreteCategory.congr_hom wf x))
    exact Prod.ext hx (Prod.ext rfl (ContinuousMap.ext (fun _ ↦ congrArg s hx)))
  · apply ConcreteCategory.hom_ext
    intro z
    cases z with
    | inl x =>
      change totalComparison p q s t w (DoubleCylinder.collapseOfPushout sq
        (DoubleCylinder.cylinderEnd f g (Sum.inl x))) =
        HPComparison sq' q s (cylinderComparison sq sq' a b c p wf wg wi wj q s t w
          (DoubleCylinder.cylinderEnd f g (Sum.inl x)))
      rw [DoubleCylinder.collapse_left, DoubleCylinder.map_left]
      apply Subtype.ext
      have hk := DoubleCylinder.HomotopyPullback.comparison_left f' g'
        (DoubleCylinder.cylinderSquare f' g') q (baseLeft (i' := i') s)
        (baseRight (j' := j') s) (baseSquare sq' s) (HPCylinderSquare sq' q s)
        (comparisonB b p wi q s t w x)
      have hk' := congrArg (fun z : DoubleCylinder.Cylinder f' g' × (E × C(unitInterval, T)) ↦
        (DoubleCylinder.collapseOfPushout sq' z.1, z.2)) hk
      apply Eq.trans _ hk'.symm
      change (p (i x), t (i x), ContinuousMap.const unitInterval (s (p (i x)))) =
        (DoubleCylinder.collapseOfPushout sq' (DoubleCylinder.cylinderEnd f' g' (Sum.inl (b x))),
          t (i x), ContinuousMap.const unitInterval (s (i' (b x))))
      rw [DoubleCylinder.collapse_left]
      exact Prod.ext (ConcreteCategory.congr_hom wi x) (Prod.ext rfl
        (ContinuousMap.ext (fun _ ↦ congrArg s (ConcreteCategory.congr_hom wi x))))
    | inr x =>
      change totalComparison p q s t w (DoubleCylinder.collapseOfPushout sq
        (DoubleCylinder.cylinderEnd f g (Sum.inr x))) =
        HPComparison sq' q s (cylinderComparison sq sq' a b c p wf wg wi wj q s t w
          (DoubleCylinder.cylinderEnd f g (Sum.inr x)))
      rw [DoubleCylinder.collapse_right, DoubleCylinder.map_right]
      apply Subtype.ext
      have hk := DoubleCylinder.HomotopyPullback.comparison_right f' g'
        (DoubleCylinder.cylinderSquare f' g') q (baseLeft (i' := i') s)
        (baseRight (j' := j') s) (baseSquare sq' s) (HPCylinderSquare sq' q s)
        (comparisonC c p wj q s t w x)
      have hk' := congrArg (fun z : DoubleCylinder.Cylinder f' g' × (E × C(unitInterval, T)) ↦
        (DoubleCylinder.collapseOfPushout sq' z.1, z.2)) hk
      apply Eq.trans _ hk'.symm
      change (p (j x), t (j x), ContinuousMap.const unitInterval (s (p (j x)))) =
        (DoubleCylinder.collapseOfPushout sq' (DoubleCylinder.cylinderEnd f' g' (Sum.inr (c x))),
          t (j x), ContinuousMap.const unitInterval (s (j' (c x))))
      rw [DoubleCylinder.collapse_right]
      exact Prod.ext (ConcreteCategory.congr_hom wj x) (Prod.ext rfl
        (ContinuousMap.ext (fun _ ↦ congrArg s (ConcreteCategory.congr_hom wj x))))

end TopCat.CartesianDomainPushout
