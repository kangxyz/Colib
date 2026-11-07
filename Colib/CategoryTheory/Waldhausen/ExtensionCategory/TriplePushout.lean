/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.PushoutCube

/-! # Actual interchange of the two relative directions of a pushout cube

The two iterated relative pushouts have the same universal property. All
pushouts in this statement are displayed; no global colimit assumption or
cofibration conclusion is included among the inputs.


Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/TriplePushout.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C]

/-- Interchange the two relative directions of an actual three-dimensional
pushout construction. The new square is proved by its universal property. -/
theorem relativePushoutInterchange
    {A B C₀ D A' B' C' P Q P' Q' T : C}
    {a : A ⟶ B} {b : A ⟶ C₀} {c : B ⟶ D} {d : C₀ ⟶ D}
    {u : A ⟶ A'} {v : B ⟶ B'} {w : C₀ ⟶ C'}
    {a' : A' ⟶ B'} {b' : A' ⟶ C'}
    {pC : C₀ ⟶ P} {pA : A' ⟶ P} {qD : D ⟶ Q} {qB : B' ⟶ Q}
    {pB : B ⟶ P'} {pA' : A' ⟶ P'} {qD' : D ⟶ Q'} {qC : C' ⟶ Q'}
    {k : P ⟶ Q} {l : P ⟶ C'} {k' : P' ⟶ Q'} {l' : P' ⟶ B'}
    {tQ : Q ⟶ T} {tC : C' ⟶ T}
    (hP : IsPushout b u pC pA) (hQ : IsPushout c v qD qB)
    (hP' : IsPushout a u pB pA') (hQ' : IsPushout d w qD' qC)
    (hT : IsPushout k l tQ tC)
    (hpk : pC ≫ k = d ≫ qD) (hak : pA ≫ k = a' ≫ qB)
    (hpl : pC ≫ l = w) (hal : pA ≫ l = b')
    (hbk' : pB ≫ k' = c ≫ qD') (hak' : pA' ≫ k' = b' ≫ qC)
    (hbl' : pB ≫ l' = v) (hal' : pA' ≫ l' = a') :
    ∃ r : Q' ⟶ T, IsPushout k' l' r (qB ≫ tQ) ∧
      qD' ≫ r = qD ≫ tQ ∧ qC ≫ r = tC := by
  have hdw : d ≫ qD ≫ tQ = w ≫ tC := by
    rw [← Category.assoc, ← hpk, Category.assoc, hT.w, ← Category.assoc, hpl]
  let r : Q' ⟶ T := hQ'.desc (qD ≫ tQ) tC hdw
  have hdr : qD' ≫ r = qD ≫ tQ := hQ'.inl_desc _ _ _
  have hcr : qC ≫ r = tC := hQ'.inr_desc _ _ _
  have har : a' ≫ qB ≫ tQ = b' ≫ tC := by
    rw [← Category.assoc, ← hak, Category.assoc, hT.w, ← Category.assoc, hal]
  have wr : k' ≫ r = l' ≫ qB ≫ tQ := by
    apply hP'.hom_ext
    · rw [← Category.assoc, hbk', Category.assoc, hdr,
        ← Category.assoc, ← Category.assoc, hbl', hQ.w]
      simp only [Category.assoc]
    · rw [← Category.assoc, hak', Category.assoc, hcr,
        ← Category.assoc, ← Category.assoc, hal']
      simpa only [Category.assoc] using har.symm
  let eQ (s : PushoutCocone k' l') : Q ⟶ s.pt :=
    hQ.desc (qD' ≫ s.inl) s.inr (by
      have hs := congrArg (fun z ↦ pB ≫ z) s.condition
      simpa only [← Category.assoc, hbk', hbl'] using hs)
  have eQ_left (s : PushoutCocone k' l') : qD ≫ eQ s = qD' ≫ s.inl := hQ.inl_desc _ _ _
  have eQ_right (s : PushoutCocone k' l') : qB ≫ eQ s = s.inr := hQ.inr_desc _ _ _
  have we (s : PushoutCocone k' l') : k ≫ eQ s = l ≫ qC ≫ s.inl := by
    apply hP.hom_ext
    · rw [← Category.assoc, hpk, Category.assoc, eQ_left,
        ← Category.assoc, ← Category.assoc, hpl, hQ'.w]
      simp only [Category.assoc]
    · rw [← Category.assoc, hak, Category.assoc, eQ_right,
        ← Category.assoc, ← Category.assoc, hal]
      have hs := congrArg (fun z ↦ pA' ≫ z) s.condition
      have hs' : b' ≫ qC ≫ s.inl = a' ≫ s.inr := by
        simpa only [← Category.assoc, hak', hal'] using hs
      simpa only [Category.assoc] using hs'.symm
  let e (s : PushoutCocone k' l') : T ⟶ s.pt := hT.desc (eQ s) (qC ≫ s.inl) (we s)
  have heQ (s : PushoutCocone k' l') : tQ ≫ e s = eQ s := hT.inl_desc _ _ _
  have heC (s : PushoutCocone k' l') : tC ≫ e s = qC ≫ s.inl := hT.inr_desc _ _ _
  have he₁ (s : PushoutCocone k' l') : r ≫ e s = s.inl := by
    apply hQ'.hom_ext
    · rw [← Category.assoc, hdr, Category.assoc, heQ, eQ_left]
    · rw [← Category.assoc, hcr, heC]
  have he₂ (s : PushoutCocone k' l') : (qB ≫ tQ) ≫ e s = s.inr := by
    rw [Category.assoc, heQ, eQ_right]
  refine ⟨r, ?_, hdr, hcr⟩
  apply IsPushout.of_isColimit (c := PushoutCocone.mk r (qB ≫ tQ) wr)
  refine PushoutCocone.IsColimit.mk wr e he₁ he₂ ?_
  intro s m hm hn
  apply hT.hom_ext
  · apply hQ.hom_ext
    · rw [← Category.assoc, ← hdr, Category.assoc, hm,
        ← Category.assoc, ← hdr, Category.assoc, he₁]
    · rw [← Category.assoc, hn, ← Category.assoc, he₂]
  · rw [← hcr, Category.assoc, hm, Category.assoc, he₁]

end CategoryTheory.Waldhausen.ExtensionCategory
