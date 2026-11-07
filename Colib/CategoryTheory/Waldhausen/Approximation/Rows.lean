/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.RowLift
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ReflexiveFactorization

/-! # Genuine approximation on every original quotient row

Base App2 gives an actual strict row lift by initial-flag completion.
An honest source row factorization supplies its genuine joint cofibration.
Structural base joint-cylinder data constructs such factorizations in all
degrees. No row lifting or contractibility endpoint is assumed.

Implementation provenance: `Quillen/Waldhausen/Approximation/Rows.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.QuotientRows


noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.HasApproximationProperty
open QuotientRows
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

include h
/-- App1 reflects weakness on every unchanged interval component. -/
theorem row_reflects {n : SimplexCategory} {A B : Obj W n} (f : A ⟶ B)
    (hf : weq V n ((postcompose W V hF n).map f)) : weq W n f :=
  fun p ↦ h.reflects _ (hf p)

/-- Base App1/App2 and a genuine source row factorization imply actual row
App1/App2. The cofibration is the full original all-triples Reedy property. -/
theorem row_approximation (n : SimplexCategory)
    (T : FunctorialFactorization (waldhausenStructure W n)) :
    HasApproximationProperty (waldhausenStructure W n) (waldhausenStructure V n)
      (postcompose W V hF n) :=
  of_factorization T
    (fun _ hf ↦ (postcompose_exact W V hF n).weak _ hf)
    (fun f hf ↦ row_reflects h hF f hf)
    (fun f ↦ exists_rowLift h hF f)

/-- Structural exact base joint-cylinder data supplies every required row
factorization, so approximation holds on the literal row postcomposition. -/
theorem row_approximation_of_joint
    (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))
    (n : SimplexCategory) :
    HasApproximationProperty (waldhausenStructure W n) (waldhausenStructure V n)
      (postcompose W V hF n) :=
  row_approximation h hF n (factorizationOfJointData W J n)

end CategoryTheory.Waldhausen.HasApproximationProperty
