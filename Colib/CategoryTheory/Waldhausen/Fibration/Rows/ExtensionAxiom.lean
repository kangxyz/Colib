/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.NestedWeakEquivalences

/-! # The extension axiom on the unchanged coarse quotient-row structure

Every displayed cofiber square is evaluated as an actual component pushout.
Only its genuine zero corner is replaced by the chosen coarse zero. The base
extension axiom then proves pointwise weakness of the original middle map.
No row equivalence, cylinder, or saturation hypothesis enters.


Implementation provenance:
`Quillen/Waldhausen/Fibration/Rows/ExtensionAxiom.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RowWeakEquivalences
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- Evaluation retains the original cofiber square and changes only its zero corner. -/
theorem cofiber_evaluation_isPushout {n : SimplexCategory} {A B Q : QuotientRows.Obj V n}
    {i : A ⟶ B} {q : B ⟶ Q} (hi : (coarseStructure N n).cof i)
    (h : IsPushout i ((coarseStructure N n).isZero.from_ A)
      q ((coarseStructure N n).isZero.to_ Q)) (p : Interval n) :
    IsPushout (i.hom.app p) (N.coarse.isZero.from_ (A.obj.obj p))
      (q.hom.app p) (N.coarse.isZero.to_ (Q.obj.obj p)) := by
  apply (QuotientRows.pointwise_of_isPushout V hi h p).of_iso (Iso.refl _) (Iso.refl _)
    (V.isZero.iso N.coarse.isZero) (Iso.refl _)
  · simp
  · exact N.coarse.isZero.eq_of_tgt _ _
  · simp
  · exact V.isZero.eq_of_src _ _

/-- The base extension axiom genuinely induces the coarse row extension axiom. -/
theorem extensionAxiom (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    ExtensionAxiom (coarseStructure N n) where
  extension {A B Q A' B' Q'} {i q i' q'} hi hi' h h' a b c wi wq ha hc p :=
    he.extension
      (by rw [N.cof_eq]; exact QuotientRows.cof_app V hi p)
      (by rw [N.cof_eq]; exact QuotientRows.cof_app V hi' p)
      (cofiber_evaluation_isPushout N hi h p) (cofiber_evaluation_isPushout N hi' h' p)
      (a.hom.app p) (b.hom.app p) (c.hom.app p)
      (congrArg (fun f ↦ f.hom.app p) wi) (congrArg (fun f ↦ f.hom.app p) wq)
      (ha p) (hc p)

end CategoryTheory.Waldhausen.Fibration.RowWeakEquivalences
