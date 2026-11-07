/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cofinality.Grading
public import Colib.KTheory.Waldhausen.Fibration.GeneralComparison
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.BaseFactorization

/-! # The original graded fibration from genuine fine joint-cylinder data

Only projection weakness is retargeted to grade equality. The actual fine
joint functor and both endpoint maps remain unchanged. The original second
endpoint section then supplies the genuine canonical fiber comparison.

Implementation provenance: `Quillen/Waldhausen/Cofinality/JointData.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.Fibration


noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace CategoryTheory.Waldhausen.Cofinality.Grading
open Fibration
variable {C : Type u} [Category.{v} C] {G : Type w} [AddCommGroup G]
  {W : Structure C} (d : Grading W G)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))

/-- Only the proof of projection weakness changes; the original joint functor stays literal. -/
def jointData : RowFactorization.JointData d.nested where
  joint := D.joint
  exact := D.exact
  inl := D.inl
  inr := D.inr
  coproduct := D.coproduct
  projection := D.projection
  factorization := D.factorization
  weak f := d.weak _ (D.weak f)

/-- The original section equation survives grade retargeting unchanged. -/
theorem jointData_secondEndpointSection
    (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D) :
    RowFactorization.SecondEndpointSection d.nested (d.jointData D) := hs

/-- The unchanged actual zero-grade inclusion compares weakly with the genuine original fiber. -/
theorem canonicalFiberMap_isWeakHomotopyEquivalence
    (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D) :
    IsWeakHomotopyEquivalence (Fibration.canonicalFiberMap d.nested) := by
  let : d.nested.coarse.weq.HasTwoOutOfThreeProperty := d.coarseStructure_twoOutOfThree
  exact Fibration.canonicalFiberMap_isWeakHomotopyEquivalence_general d.nested d.extensionAxiom
    (d.jointData D) (d.jointData_secondEndpointSection D hs)

end CategoryTheory.Waldhausen.Cofinality.Grading
