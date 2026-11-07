/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory
public import Mathlib.Algebra.Group.Basic

/-! # The genuine coarse Waldhausen structure of an additive object grading

An invariant of original weak arrows, normalized at the chosen zero and
additive on actual cofibration pushouts, defines coarse weak maps by equality
of the endpoint grades. Gluing, two-out-of-three and extension are proved.
This is structural input for cofinality, without a K-zero presentation or a
K-equivalence premise. In particular a grading of objects is not silently
identified with an actual homotopy-theoretic K-zero homomorphism.

Implementation provenance: `Quillen/Waldhausen/Cofinality/Grading.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace CategoryTheory.Waldhausen.Cofinality
variable {C : Type u} [Category.{v} C] (W : Structure C)
  (G : Type w) [AddCommGroup G]

/-- Original categorical data of an additive grading, not a cofinality endpoint. -/
structure Grading where
  /-- The grade of each original object in the abelian group `G`, normalized at zero, invariant
  under weak equivalences, and additive on cofibration pushouts. -/
  value : C → G
  zero : value W.zero = 0
  weak {X Y : C} (f : X ⟶ Y) : W.weq f → value X = value Y
  pushout {A B D Q : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ Q} {j : D ⟶ Q} :
    W.cof i → IsPushout i f g j → value Q = value B + value D - value A

namespace Grading
variable {W G} (d : Grading W G)

/-- The new weak class is the equality of the grades of original endpoints. -/
def gradeWeak : MorphismProperty C := fun X Y _ ↦ d.value X = d.value Y

instance gradeWeak_multiplicative : d.gradeWeak.IsMultiplicative where
  id_mem _ := rfl
  comp_mem _ _ hf hg := hf.trans hg

instance gradeWeak_twoOutOfThree : d.gradeWeak.HasTwoOutOfThreeProperty where
  comp_mem _ _ hf hg := hf.trans hg
  of_postcomp _ _ hg hfg := hfg.trans hg.symm
  of_precomp _ _ hf hfg := hf.symm.trans hfg

/-- Only weak maps change; the original category, cofibrations and chosen zero stay literal. -/
def coarseStructure : Structure C where
  zero := W.zero
  isZero := W.isZero
  cof := W.cof
  weq := d.gradeWeak
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := W.cof_iso
  weq_iso := by
    intro X Y f hf
    exact d.weak f (W.weq_iso f hf)
  cof_zero := W.cof_zero
  pushout_exists := W.pushout_exists
  cof_pushout := W.cof_pushout
  gluing := by
    intro A B D Q A' B' D' Q' i f g j i' f' g' j' a b c p hi hi' h h' _ _ _ _ ha hb hc
    change d.value Q = d.value Q'
    rw [d.pushout hi h, d.pushout hi' h']
    change d.value A = d.value A' at ha
    change d.value B = d.value B' at hb
    change d.value D = d.value D' at hc
    rw [ha, hb, hc]

/-- Every original weak map is grade-preserving. -/
def nested : Fibration.NestedWeakEquivalences W where
  coarse := d.coarseStructure
  cof_eq := rfl
  zero_eq := rfl
  le_weq := fun _ _ f hf ↦ d.weak f hf

/-- Grade-preserving weakness has the full two-out-of-three property. -/
instance coarseStructure_twoOutOfThree : d.coarseStructure.weq.HasTwoOutOfThreeProperty :=
  gradeWeak_twoOutOfThree d

/-- The actual displayed cofiber has the difference of the original endpoint grades. -/
theorem cofiber_value {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q} (hi : W.cof i)
    (h : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    d.value Q = d.value B - d.value A := by
  rw [d.pushout hi h, d.zero, add_zero]

/-- The extension axiom follows from the grades of the two actual cofiber squares. -/
theorem extensionAxiom : Fibration.ExtensionAxiom d.coarseStructure where
  extension hi hi' h h' _ _ _ _ _ ha hc := by
    change d.value _ = d.value _
    change d.value _ = d.value _ at ha hc
    have hq := d.cofiber_value hi h
    have hq' := d.cofiber_value hi' h'
    rw [hq, hq', ha] at hc
    exact (sub_left_inj).mp hc

/-- Coarse acyclicity is exactly vanishing of the original object grade. -/
@[simp] theorem acyclic_iff (X : C) :
    Fibration.Acyclic d.coarseStructure X ↔ d.value X = 0 := by
  change d.value W.zero = d.value X ↔ _
  rw [d.zero]
  exact eq_comm

/-- Thus the actual fibration's kernel category is precisely the zero-grade full subcategory. -/
@[simp] theorem acyclicObjects_iff (X : C) :
    Fibration.acyclicObjects d.nested X ↔ d.value X = 0 := d.acyclic_iff X

end Grading
end CategoryTheory.Waldhausen.Cofinality
