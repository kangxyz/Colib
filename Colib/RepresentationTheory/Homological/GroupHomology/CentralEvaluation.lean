/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
public import Mathlib.Algebra.Module.ULift
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Evaluation of native second group homology in a central extension

A normalized section of an arbitrary central surjection gives a genuine central
multiplicative defect. Associativity annihilates Mathlib's actual degree-three
bar differential, so evaluation descends through its native second group homology.
No perfectness hypothesis, replacement bar complex, or Schur extension is used.

Adapted from the section-defect and native homology descent constructions in
`Quillen/Aglib/RepresentationTheory/Homological/GroupHomology/CentralBarLifts.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory Finsupp
open scoped IsMulCommutative

namespace groupHomology

section Descent
variable {k G : Type u} {M : Type v} [CommRing k] [Group G] [AddCommGroup M] [Module k M]
  {A : Rep.{u} k G} (l : (G × G →₀ A) →ₗ[k] M)
  (hl : l.comp (d₃₂ A).hom = 0)

/-- Evaluation annihilating the native degree-three boundaries descends to native H-two. -/
def H2Desc : H2 A →ₗ[k] M := by
  let S := shortComplexH2 A
  let v := l.comp (cycles₂ A).subtype
  have hv : LinearMap.range S.moduleCatToCycles ≤ LinearMap.ker v := by
    rintro _ ⟨c, rfl⟩
    exact LinearMap.congr_fun hl c
  exact ((LinearMap.range S.moduleCatToCycles).liftQ v hv).comp (H2Iso A).hom.hom

/-- The descent evaluates every native two-cycle on its actual representative. -/
@[simp] theorem H2Desc_pi (c : cycles₂ A) :
    H2Desc l hl (H2π A c) = l c.val := by
  let S := shortComplexH2 A
  have he : H2π A ≫ (H2Iso A).hom = S.moduleCatLeftHomologyData.π := by
    rw [← π_comp_H2Iso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hec : (H2Iso A).hom (H2π A c) = S.moduleCatLeftHomologyData.π c :=
    ConcreteCategory.congr_hom he c
  dsimp only [H2Desc, LinearMap.comp_apply]
  erw [hec]
  rfl

end Descent

variable {G : Type u} {H : Type v} [Group G] [Group H]
  (p : H →* G) (hp : Function.Surjective p) (hc : p.ker ≤ Subgroup.center H)

/-- A genuine section of the supplied surjection, normalized at the original identity. -/
def centralSection (g : G) : H := by
  classical
  exact if g = 1 then 1 else (hp g).choose

@[simp] theorem centralSection_one : centralSection p hp 1 = 1 := by simp [centralSection]

/-- The actual chosen lifts project to their original group elements. -/
@[simp] theorem centralSection_projection (g : G) : p (centralSection p hp g) = g := by
  classical
  by_cases hg : g = 1
  · subst g; simp
  · simp only [centralSection, ite_eq_right hg]
    exact (hp g).choose_spec

/-- The multiplicative section defect is an actual central element by the given central kernel. -/
def sectionDefect (g h : G) : Subgroup.center H :=
  ⟨centralSection p hp g * centralSection p hp h * (centralSection p hp (g * h))⁻¹,
    hc (by simp only [MonoidHom.mem_ker, map_mul, map_inv, centralSection_projection,
      mul_inv_cancel])⟩

/-- The section defect is normalized in its first argument. -/
@[simp] theorem sectionDefect_one_left (g : G) : sectionDefect p hp hc 1 g = 1 := by
  apply Subtype.ext
  simp [sectionDefect]

/-- The section defect is normalized in its second argument. -/
@[simp] theorem sectionDefect_one_right (g : G) : sectionDefect p hp hc g 1 = 1 := by
  apply Subtype.ext
  simp [sectionDefect]

/-- Multiplication of the chosen section has the displayed original central defect. -/
theorem sectionDefect_section (g h : G) :
    centralSection p hp g * centralSection p hp h =
      (sectionDefect p hp hc g h).val * centralSection p hp (g * h) := by
  simp [sectionDefect, mul_assoc]

/-- Associativity proves the actual central-defect cocycle identity. -/
theorem sectionDefect_cocycle (g h j : G) :
    sectionDefect p hp hc g h * sectionDefect p hp hc (g * h) j =
      sectionDefect p hp hc h j * sectionDefect p hp hc g (h * j) := by
  apply Subtype.ext
  change (sectionDefect p hp hc g h).val * (sectionDefect p hp hc (g * h) j).val = _
  calc
    _ = (centralSection p hp g * centralSection p hp h * centralSection p hp j) *
        (centralSection p hp (g * (h * j)))⁻¹ := by
      simp only [sectionDefect, mul_assoc]
      group
    _ = centralSection p hp g * (sectionDefect p hp hc h j).val *
        centralSection p hp (h * j) * (centralSection p hp (g * (h * j)))⁻¹ := by
      simp only [sectionDefect]
      group
    _ = (sectionDefect p hp hc h j).val * centralSection p hp g *
        centralSection p hp (h * j) * (centralSection p hp (g * (h * j)))⁻¹ := by
      rw [Subgroup.mem_center_iff.mp (sectionDefect p hp hc h j).property]
    _ = _ := by simp only [Subgroup.coe_mul, sectionDefect, mul_assoc]

/-- Extend the actual section defect linearly on the existing lifted-integral bar chains. -/
def defectEvaluation : (G × G →₀ ULift.{u} ℤ) →ₗ[ULift.{u} ℤ] Additive (Subgroup.center H) :=
  Finsupp.lsum (ULift.{u} ℤ) (fun gh => LinearMap.toSpanSingleton (ULift.{u} ℤ) _
    (Additive.ofMul (sectionDefect p hp hc gh.1 gh.2)))

/-- Evaluation of each original unit bar is the actual section defect. -/
@[simp] theorem defectEvaluation_single_one (g h : G) :
    defectEvaluation p hp hc (single (g, h) 1) =
      Additive.ofMul (sectionDefect p hp hc g h) := by
  simp [defectEvaluation]

/-- The original three-bar differential is annihilated by the proved central-defect cocycle. -/
theorem defectEvaluation_boundary :
    (defectEvaluation p hp hc).comp
      (groupHomology.d₃₂ (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))).hom = 0 := by
  apply Finsupp.lhom_ext
  intro ghk a
  have hs : single ghk a = a • single ghk (1 : ULift.{u} ℤ) := by simp
  rw [hs, map_smul]
  change a • defectEvaluation p hp hc
    (groupHomology.d₃₂ (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) (single ghk 1)) = 0
  suffices hz : defectEvaluation p hp hc
      (d₃₂ (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) (single ghk 1)) = 0 by
    rw [hz, smul_zero]
  rcases ghk with ⟨g, h, j⟩
  rw [d₃₂_single]
  change defectEvaluation p hp hc
    (single (h, j) 1 - single (g * h, j) 1 + single (g, h * j) 1 - single (g, h) 1) = 0
  rw [map_sub, map_add, map_sub, defectEvaluation_single_one,
    defectEvaluation_single_one, defectEvaluation_single_one, defectEvaluation_single_one]
  have hcycle := congrArg Additive.ofMul (sectionDefect_cocycle p hp hc g h j)
  change Additive.ofMul (sectionDefect p hp hc g h) +
      Additive.ofMul (sectionDefect p hp hc (g * h) j) =
    Additive.ofMul (sectionDefect p hp hc h j) +
      Additive.ofMul (sectionDefect p hp hc g (h * j)) at hcycle
  calc
    _ = (Additive.ofMul (sectionDefect p hp hc h j) +
        Additive.ofMul (sectionDefect p hp hc g (h * j))) -
      (Additive.ofMul (sectionDefect p hp hc g h) +
        Additive.ofMul (sectionDefect p hp hc (g * h) j)) := by abel
    _ = 0 := sub_eq_zero.mpr hcycle.symm

/-- The actual section defect induces an actual homomorphism on the native second homology. -/
def centralHomologyEvaluation :
    H2 (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) →ₗ[ULift.{u} ℤ]
      Additive (Subgroup.center H) :=
  H2Desc (defectEvaluation p hp hc) (defectEvaluation_boundary p hp hc)

/-- The actual defect projects to identity in the original quotient group. -/
theorem sectionDefect_projection (g h : G) : p (sectionDefect p hp hc g h).val = 1 := by
  simp only [sectionDefect, map_mul, map_inv, centralSection_projection, mul_inv_cancel]

/-- Every evaluated original bar chain lies in the actual projection kernel. -/
theorem defectEvaluation_projection (c : G × G →₀ ULift.{u} ℤ) :
    p (defectEvaluation p hp hc c).toMul.val = 1 := by
  induction c using Finsupp.induction with
  | zero => rw [map_zero]; exact map_one p
  | @single_add gh a c _ _ ih =>
    rw [map_add]
    change p ((defectEvaluation p hp hc (single gh a)).toMul.val *
      (defectEvaluation p hp hc c).toMul.val) = 1
    rw [map_mul, ih, mul_one]
    simp only [defectEvaluation, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
    change p (((a • Additive.ofMul (sectionDefect p hp hc gh.1 gh.2)).toMul).val) = 1
    change p ((sectionDefect p hp hc gh.1 gh.2).val ^ a.down) = 1
    rw [map_zpow, sectionDefect_projection, one_zpow]

/-- Native H-two descent retains membership in the original central kernel. -/
theorem centralHomologyEvaluation_projection
    (a : H2 (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))) :
    p (centralHomologyEvaluation p hp hc a).toMul.val = 1 := by
  induction a using groupHomology.H2_induction_on with
  | h c =>
    change p (H2Desc (defectEvaluation p hp hc) (defectEvaluation_boundary p hp hc)
      (groupHomology.H2π (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) c)).toMul.val = 1
    rw [H2Desc_pi]
    exact defectEvaluation_projection p hp hc c.val

/-- Evaluation takes values in the actual projection kernel, as a group homomorphism. -/
def centralHomologyEvaluationToKernel :
    Multiplicative (H2 (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))) →* p.ker where
  toFun a := ⟨(centralHomologyEvaluation p hp hc a.toAdd).toMul.val,
    centralHomologyEvaluation_projection p hp hc a.toAdd⟩
  map_one' := Subtype.ext (by
    change (centralHomologyEvaluation p hp hc 0).toMul.val = 1
    rw [map_zero]
    rfl)
  map_mul' a b := Subtype.ext (by
    change (centralHomologyEvaluation p hp hc (a.toAdd + b.toAdd)).toMul.val = _
    rw [map_add]
    rfl)

end groupHomology
