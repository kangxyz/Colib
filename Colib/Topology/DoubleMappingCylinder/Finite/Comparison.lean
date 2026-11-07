/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.Finite.Basic
public import Colib.Topology.DoubleMappingCylinder.HeightCover

/-! The canonical ordinary homotopy equivalence from an actual double
cylinder to its fibration normalization, built from its genuine open
cover and the checked local collar comparisons. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/Finite/Comparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.DoubleCylinder.FiniteNormalization
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

/-- The two-open partition of the original double cylinder defined by its height function. -/
abbrev coverPartition : TwoOpenPartition D := TwoOpenPartition.ofHeight (height f g sq)
/-- The inclusion of the cover overlap into the left height chart. -/
abbrev coverLeft : TopCat.of (coverPartition sq).Overlap ⟶ TopCat.of (coverPartition sq).Left :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.1⟩, by fun_prop⟩
/-- The inclusion of the cover overlap into the right height chart. -/
abbrev coverRight : TopCat.of (coverPartition sq).Overlap ⟶ TopCat.of (coverPartition sq).Right :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.2⟩, by fun_prop⟩

/-- The double mapping cylinder of the overlap inclusions into the two height charts. -/
abbrev CoverCylinder : TopCat.{u} :=
  pushout (TopCat.intervalEndpoints (TopCat.of (coverPartition sq).Overlap)) (coverPartition
    sq).endMap
/-- The canonical map of the cover overlap times `I` into the cover cylinder. -/
abbrev coverLine : TopCat.of (coverPartition sq).Overlap ⊗ TopCat.I ⟶ CoverCylinder sq :=
    pushout.inl _ _
/-- The canonical map of the two height charts into the cover cylinder. -/
abbrev coverEnd : TopCat.of ((coverPartition sq).Left ⊕ (coverPartition sq).Right) ⟶
    CoverCylinder sq := pushout.inr _ _
theorem coverSquare : IsPushout (TopCat.intervalEndpoints (TopCat.of (coverPartition sq).Overlap))
    (endMap (coverLeft sq) (coverRight sq)) (coverLine sq) (coverEnd sq) :=
      IsPushout.of_hasPushout _ _

/-- The normalized fibration-span data associated to the given map of double cylinders. -/
abbrev NData := data sq' a b c wf wg
/-- The double mapping cylinder on the full left and right legs of the normalization data. -/
abbrev Target : TopCat.{u} := pushout (TopCat.intervalEndpoints (NData sq' a b c wf wg).R)
  (endMap (NData sq' a b c wf wg).leftLeg (NData sq' a b c wf wg).rightLeg)
/-- The canonical cylinder map from the common normalization space times `I` into `Target`. -/
abbrev targetLine : (NData sq' a b c wf wg).R ⊗ TopCat.I ⟶ Target sq' a b c wf wg := pushout.inl _ _
/-- The canonical map of the two normalization target spaces into `Target`. -/
abbrev targetEnd : TopCat.of ((NData sq' a b c wf wg).E0 ⊕ (NData sq' a b c wf wg).E1) ⟶
    Target sq' a b c wf wg := pushout.inr _ _
theorem targetSquare : IsPushout (TopCat.intervalEndpoints (NData sq' a b c wf wg).R)
    (endMap (NData sq' a b c wf wg).leftLeg (NData sq' a b c wf wg).rightLeg)
      (targetLine sq' a b c wf wg) (targetEnd sq' a b c wf wg) := IsPushout.of_hasPushout _ _
/-- The collapse from the normalized double cylinder to the original target total space `D'`. -/
abbrev targetProjection : Target sq' a b c wf wg ⟶ D' :=
  (NData sq' a b c wf wg).collapse (targetSquare sq' a b c wf wg)

/-- The overlap coordinate map into the common normalization space, given by the inverse overlap
homeomorphism. -/
abbrev overlapComparison : TopCat.of (coverPartition sq).Overlap ⟶ (NData sq' a b c wf wg).R :=
  TopCat.ofHom ⟨fun x ↦ (overlapHomeomorph sq).symm x, by fun_prop⟩
/-- The left collar comparison from the original height chart to the left normalization space,
at cutoff `upper`. -/
abbrev leftComparison : TopCat.of (coverPartition sq).Left ⟶ (NData sq' a b c wf wg).E0 :=
  leftCollarComparison sq sq' a b c wf wg upper zero_lt_upper
/-- The right collar comparison from the original height chart to the right normalization space,
at cutoff `lower`. -/
abbrev rightComparison : TopCat.of (coverPartition sq).Right ⟶ (NData sq' a b c wf wg).E1 :=
  rightCollarComparison sq sq' a b c wf wg lower lower_lt_one

theorem comparison_left_square : coverLeft sq ≫ leftComparison sq sq' a b c wf wg =
    overlapComparison sq sq' a b c wf wg ≫ (NData sq' a b c wf wg).leftLeg := by
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨z, rfl⟩ := (overlapHomeomorph sq).surjective x
  change leftComparison sq sq' a b c wf wg _ =
    (NData sq' a b c wf wg).leftLeg ((overlapHomeomorph sq).symm (overlapHomeomorph sq z))
  rw [Homeomorph.symm_apply_apply]
  apply Subtype.ext
  exact leftCollarComparison_cylinder sq sq' a b c wf wg upper zero_lt_upper
    ⟨(z.1, ULift.up z.2.1), by rw [height_cylinder]; exact z.2.2.2⟩

theorem comparison_right_square : coverRight sq ≫ rightComparison sq sq' a b c wf wg =
    overlapComparison sq sq' a b c wf wg ≫ (NData sq' a b c wf wg).rightLeg := by
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨z, rfl⟩ := (overlapHomeomorph sq).surjective x
  change rightComparison sq sq' a b c wf wg _ =
    (NData sq' a b c wf wg).rightLeg ((overlapHomeomorph sq).symm (overlapHomeomorph sq z))
  rw [Homeomorph.symm_apply_apply]
  apply Subtype.ext
  exact rightCollarComparison_cylinder sq sq' a b c wf wg lower lower_lt_one
    ⟨(z.1, ULift.up z.2.1), by rw [height_cylinder]; exact z.2.2.1⟩

/-- The strict map of cover spans induces the actual cylinder comparison. -/
abbrev coverComparison : CoverCylinder sq ⟶ Target sq' a b c wf wg :=
  DoubleCylinder.map (coverSquare sq) (targetSquare sq' a b c wf wg)
    (overlapComparison sq sq' a b c wf wg)
    (leftComparison sq sq' a b c wf wg) (rightComparison sq sq' a b c wf wg)
    (comparison_left_square sq sq' a b c wf wg) (comparison_right_square sq sq' a b c wf wg)

/-- Local actual collar comparisons glue to an actual global homotopy
equivalence of ordinary double cylinders. -/
def coverComparisonHomotopyEquiv : ContinuousMap.HomotopyEquiv (CoverCylinder sq) (Target sq' a
    b c wf wg) :=
  DoubleCylinder.mapHomotopyEquiv (coverSquare sq) (targetSquare sq' a b c wf wg)
    (overlapComparison sq sq' a b c wf wg)
    (leftComparison sq sq' a b c wf wg) (rightComparison sq sq' a b c wf wg)
    (comparison_left_square sq sq' a b c wf wg) (comparison_right_square sq sq' a b c wf wg)
    (overlapHomeomorph sq).symm.toHomotopyEquiv rfl
    (leftCollarComparisonHomotopyEquiv sq sq' a b c wf wg upper zero_lt_upper) rfl
    (rightCollarComparisonHomotopyEquiv sq sq' a b c wf wg lower lower_lt_one) rfl

/-- The actual cover cylinder contracts to the original total space. -/
abbrev coverCollapse : CoverCylinder sq ⟶ D :=
  (coverPartition sq).collapse (coverSquare sq)

/-- The ordinary normalization equivalence from the original total space. -/
def homotopyEquiv : ContinuousMap.HomotopyEquiv D (Target sq' a b c wf wg) :=
  ((coverPartition sq).collapseHomotopyEquiv (coverSquare sq)).symm.trans
    (coverComparisonHomotopyEquiv sq sq' a b c wf wg)

/-- The global comparison is strictly over the original base map. -/
theorem coverComparison_over :
    coverComparison sq sq' a b c wf wg ≫ targetProjection sq' a b c wf wg =
      coverCollapse sq ≫ DoubleCylinder.map sq sq' a b c wf wg := by
  apply (coverSquare sq).hom_ext
  · apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    obtain ⟨z, rfl⟩ := (overlapHomeomorph sq).surjective x
    change targetProjection sq' a b c wf wg
      (coverComparison sq sq' a b c wf wg (coverLine sq (overlapHomeomorph sq z, t))) = _
    rw [DoubleCylinder.map_cylinder_apply]
    change targetProjection sq' a b c wf wg
      (targetLine sq' a b c wf wg ((overlapHomeomorph sq).symm (overlapHomeomorph sq z), t)) = _
    rw [Homeomorph.symm_apply_apply]
    have hh := ConcreteCategory.congr_hom
      ((NData sq' a b c wf wg).collapse_cylinder (targetSquare sq' a b c wf wg)) (z, t)
    have hcollapse : (coverPartition sq).collapse (coverSquare sq)
        (coverLine sq (overlapHomeomorph sq z, t)) = (overlapHomeomorph sq z).1 := by
      cases t
      exact TwoOpenPartition.collapse_cylinder _ _ _ _
    exact hh.trans ((DoubleCylinder.map_cylinder_apply sq sq' a b c wf wg
      z.1 (ULift.up z.2.1)).symm.trans
        (congrArg (DoubleCylinder.map sq sq' a b c wf wg) hcollapse.symm))
  · apply ConcreteCategory.hom_ext
    intro x
    cases x with
    | inl x =>
      change targetProjection sq' a b c wf wg
        (coverComparison sq sq' a b c wf wg (coverEnd sq (Sum.inl x))) = _
      rw [DoubleCylinder.map_left]
      change targetProjection sq' a b c wf wg
        (targetEnd sq' a b c wf wg (Sum.inl (leftComparison sq sq' a b c wf wg x))) =
          DoubleCylinder.map sq sq' a b c wf wg
            ((coverPartition sq).collapse (coverSquare sq) (coverEnd sq (Sum.inl x)))
      rw [TwoOpenPartition.collapse_left]
      exact (ConcreteCategory.congr_hom
        ((NData sq' a b c wf wg).collapse_left (targetSquare sq' a b c wf wg))
        (leftComparison sq sq' a b c wf wg x))
    | inr x =>
      change targetProjection sq' a b c wf wg
        (coverComparison sq sq' a b c wf wg (coverEnd sq (Sum.inr x))) = _
      rw [DoubleCylinder.map_right]
      change targetProjection sq' a b c wf wg
        (targetEnd sq' a b c wf wg (Sum.inr (rightComparison sq sq' a b c wf wg x))) =
          DoubleCylinder.map sq sq' a b c wf wg
            ((coverPartition sq).collapse (coverSquare sq) (coverEnd sq (Sum.inr x)))
      rw [TwoOpenPartition.collapse_right]
      exact (ConcreteCategory.congr_hom
        ((NData sq' a b c wf wg).collapse_right (targetSquare sq' a b c wf wg))
        (rightComparison sq sq' a b c wf wg x))

theorem homotopyEquiv_over :
    (targetProjection sq' a b c wf wg).hom.comp (homotopyEquiv sq sq' a b c wf wg).toFun =
      (DoubleCylinder.map sq sq' a b c wf wg).hom := by
  apply ContinuousMap.ext
  intro x
  change targetProjection sq' a b c wf wg (coverComparison sq sq' a b c wf wg
    ((coverPartition sq).sectionMap (coverSquare sq) x)) = _
  have hh := ConcreteCategory.congr_hom (coverComparison_over sq sq' a b c wf wg)
    ((coverPartition sq).sectionMap (coverSquare sq) x)
  exact hh.trans (congrArg (DoubleCylinder.map sq sq' a b c wf wg)
    (TwoOpenPartition.collapse_sectionMap (coverPartition sq) (coverSquare sq) x))

/-- Normalization retains the actual left endpoint map exactly. -/
theorem homotopyEquiv_left (x : B) :
    (homotopyEquiv sq sq' a b c wf wg).toFun (e (Sum.inl x)) =
      targetEnd sq' a b c wf wg (Sum.inl
        (RetractionPullback.inclusion
          (leftCollarStrongDeformationRetract f' g' sq' upper zero_lt_upper) b x)) := by
  let xL : (coverPartition sq).Left := leftCollarInclusion f g sq upper zero_lt_upper x
  have hx : (coverPartition sq).cutoff xL.1 = 0 := by
    change clampInterval (3 * (height f g sq (e (Sum.inl x)) : ℝ) - 1) = 0
    rw [height_left]
    exact clampInterval_eq_zero (by norm_num)
  change coverComparison sq sq' a b c wf wg
    ((coverPartition sq).sectionMap (coverSquare sq) xL.1) = _
  rw [TwoOpenPartition.sectionMap_of_cutoff_zero (coverPartition sq) (coverSquare sq) xL hx,
    DoubleCylinder.map_left]
  congr 2
  exact leftCollarComparison_end sq sq' a b c wf wg upper zero_lt_upper x

/-- Normalization retains the actual right endpoint map exactly. -/
theorem homotopyEquiv_right (x : C) :
    (homotopyEquiv sq sq' a b c wf wg).toFun (e (Sum.inr x)) =
      targetEnd sq' a b c wf wg (Sum.inr
        (RetractionPullback.inclusion
          (rightCollarStrongDeformationRetract f' g' sq' lower lower_lt_one) c x)) := by
  let xR : (coverPartition sq).Right := rightCollarInclusion f g sq lower lower_lt_one x
  have hx : (coverPartition sq).cutoff xR.1 = 1 := by
    change clampInterval (3 * (height f g sq (e (Sum.inr x)) : ℝ) - 1) = 1
    rw [height_right]
    exact clampInterval_eq_one (by norm_num)
  change coverComparison sq sq' a b c wf wg
    ((coverPartition sq).sectionMap (coverSquare sq) xR.1) = _
  rw [TwoOpenPartition.sectionMap_of_cutoff_one (coverPartition sq) (coverSquare sq) xR hx,
    DoubleCylinder.map_right]
  congr 2
  exact rightCollarComparison_end sq sq' a b c wf wg lower lower_lt_one x

/-- The original total is homotopy equivalent over its base to the actual
weakly lifting iterated-pushout normalization. -/
def normalizationEquiv : ContinuousMap.HomotopyEquiv D (NData sq' a b c wf wg).normalized.Total :=
  (homotopyEquiv sq sq' a b c wf wg).trans
    ((NData sq' a b c wf wg).normalizedHomeomorph (targetSquare sq' a b c wf wg)).toHomotopyEquiv

theorem normalizationEquiv_over :
    (NData sq' a b c wf wg).normalized.projection.hom.comp
      (normalizationEquiv sq sq' a b c wf wg).toFun =
        (DoubleCylinder.map sq sq' a b c wf wg).hom := by
  change ((NData sq' a b c wf wg).normalized.projection.hom.comp
    ((NData sq' a b c wf wg).normalizedHomeomorph (targetSquare sq' a b c wf wg) : C(_, _))).comp
      (homotopyEquiv sq sq' a b c wf wg).toFun = _
  rw [FibrationSpan.Data.normalizedHomeomorph_over]
  exact homotopyEquiv_over sq sq' a b c wf wg

theorem normalizationEquiv_left (x : B) :
    (normalizationEquiv sq sq' a b c wf wg).toFun (e (Sum.inl x)) =
      (NData sq' a b c wf wg).totalLeft
        (RetractionPullback.inclusion
          (leftCollarStrongDeformationRetract f' g' sq' upper zero_lt_upper) b x) := by
  change (NData sq' a b c wf wg).normalizedHomeomorph (targetSquare sq' a b c wf wg)
    ((homotopyEquiv sq sq' a b c wf wg).toFun (e (Sum.inl x))) = _
  rw [homotopyEquiv_left]
  apply (Subdivision.homeomorph_left (targetSquare sq' a b c wf wg)
    (NData sq' a b c wf wg).fullCylinder0 (NData sq' a b c wf wg).fullCylinder1
    (NData sq' a b c wf wg).full_isPushout _).trans
  exact ConcreteCategory.congr_hom
    (show (NData sq' a b c wf wg).fullEnd0 ≫ (NData sq' a b c wf wg).fullMap0 =
      (NData sq' a b c wf wg).totalLeft from pushout.inr_desc _ _ _) _

theorem normalizationEquiv_right (x : C) :
    (normalizationEquiv sq sq' a b c wf wg).toFun (e (Sum.inr x)) =
      (NData sq' a b c wf wg).totalRight
        (RetractionPullback.inclusion
          (rightCollarStrongDeformationRetract f' g' sq' lower lower_lt_one) c x) := by
  change (NData sq' a b c wf wg).normalizedHomeomorph (targetSquare sq' a b c wf wg)
    ((homotopyEquiv sq sq' a b c wf wg).toFun (e (Sum.inr x))) = _
  rw [homotopyEquiv_right]
  apply (Subdivision.homeomorph_right (targetSquare sq' a b c wf wg)
    (NData sq' a b c wf wg).fullCylinder0 (NData sq' a b c wf wg).fullCylinder1
    (NData sq' a b c wf wg).full_isPushout _).trans
  exact ConcreteCategory.congr_hom
    (show (NData sq' a b c wf wg).fullEnd1 ≫ (NData sq' a b c wf wg).fullMap1 =
      (NData sq' a b c wf wg).totalRight from pushout.inr_desc _ _ _) _

end TopCat.DoubleCylinder.FiniteNormalization
