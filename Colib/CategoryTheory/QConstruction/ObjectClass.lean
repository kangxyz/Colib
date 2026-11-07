/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.KernelPullback
public import Colib.CategoryTheory.ExactCategory.Biproducts
public import Colib.CategoryTheory.QConstruction.Connected
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Canonical object endomorphisms in groupoid-valued Q-functors

There are two actual Q-arrows from the distinguished zero vertex: the already
constructed zero-apex arrow and the whole-object-apex arrow. Their images under
any groupoid-valued functor determine an endomorphism of the image of that vertex.
Conflations impose the specified product relation, and the resulting object
endomorphisms commute. No commutativity of all target endomorphisms is assumed.

This is purely categorical: it does not construct a topological loop or assert
that these endomorphisms generate a fundamental group. In particular it makes
no homotopical K₀ or π₁ comparison claim.

## Implementation provenance

Extracted from the first eleven declarations of
`Quillen/KTheory/GrothendieckComparison/Basic.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. All actual spans, apex objects, leg
maps, kernel pullback equations and product orientations are retained.
The omitted topology, algebraic Grothendieck-group and K-map imports do not
occur in these declarations. The imported Biproducts file supplies the two
actual biproduct conflations, without requiring an abelian category.
-/

@[expose] public noncomputable section

universe v u w
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The second canonical Q-arrow from zero to an object, represented by the
span with the whole object as apex. -/
def fromZeroTotal (X : E.QCategory) : E.qZero ⟶ X :=
  QConstruction.mkHom E.deflation E.inflation
    { apex := X.obj.of
      l := 0
      r := 𝟙 _
      wl := E.deflation_zero _
      wr := E.inflation_id _ }

/-- The forward Q-arrow associated to an admissible monomorphism. -/
def qInflation {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    QConstruction.of E.deflation E.inflation X ⟶ QConstruction.of E.deflation E.inflation Y :=
  QConstruction.mkHom E.deflation E.inflation
    { apex := X, l := 𝟙 _, r := i, wl := E.deflation_id _, wr := hi }

/-- The reverse Q-arrow associated to an admissible epimorphism. -/
def qDeflation {X Y : C} (p : X ⟶ Y) (hp : E.deflation p) :
    QConstruction.of E.deflation E.inflation Y ⟶ QConstruction.of E.deflation E.inflation X :=
  QConstruction.mkHom E.deflation E.inflation
    { apex := X, l := p, r := 𝟙 _, wl := hp, wr := E.inflation_id _ }

/-- Span composition may be calculated using any actual pullback square. -/
lemma q_comp_of_isPullback {X Y Z P : C}
    (s : Span E.deflation E.inflation X Y)
    (t : Span E.deflation E.inflation Y Z)
    (a : P ⟶ s.apex) (b : P ⟶ t.apex) (h : IsPullback a b s.r t.l)
    (r : Span E.deflation E.inflation X Z)
    (e : P ≅ r.apex) (hl : e.hom ≫ r.l = a ≫ s.l)
    (hr : e.hom ≫ r.r = b ≫ t.r) :
    QConstruction.mkHom E.deflation E.inflation s ≫ QConstruction.mkHom E.deflation E.inflation t =
      QConstruction.mkHom E.deflation E.inflation r := by
  refine QConstruction.mkHom_eq_of_apexIso E.deflation E.inflation (Span.comp s t) r
    (h.isoPullback.symm ≪≫ e) ?_ ?_
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hl, Span.comp_l]
    simp only [h.isoPullback_inv_fst_assoc]
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hr, Span.comp_r]
    simp only [h.isoPullback_inv_snd_assoc]

/-- The zero-apex arrow is preserved by admissible inclusions. -/
lemma fromZero_qInflation {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    E.fromZero (QConstruction.of E.deflation E.inflation X) ≫ E.qInflation i hi =
      E.fromZero (QConstruction.of E.deflation E.inflation Y) := by
  have h : IsPullback (𝟙 (0 : C)) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  apply E.q_comp_of_isPullback _ _ _ _ h _ (Iso.refl _)
  · simp [QConstruction.of]
  · simp [QConstruction.of]

/-- The whole-apex arrow is preserved by admissible quotient maps. -/
lemma fromZeroTotal_qDeflation {X Y : C} (p : X ⟶ Y) (hp : E.deflation p) :
    E.fromZeroTotal (QConstruction.of E.deflation E.inflation Y) ≫ E.qDeflation p hp =
      E.fromZeroTotal (QConstruction.of E.deflation E.inflation X) := by
  apply E.q_comp_of_isPullback _ _ p (𝟙 X)
    (IsPullback.of_horiz_isIso (fst := 𝟙 X) (g := 𝟙 Y) ⟨by simp⟩).flip
    _ (Iso.refl _)
  · simp [QConstruction.of]
  · simp [QConstruction.of]

/-- The whole-apex arrow followed by an inflation represents its subobject. -/
lemma fromZeroTotal_qInflation {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    E.fromZeroTotal (QConstruction.of E.deflation E.inflation X) ≫ E.qInflation i hi =
      QConstruction.mkHom E.deflation E.inflation
        { apex := X, l := 0, r := i, wl := E.deflation_zero _, wr := hi } := by
  have h : IsPullback (𝟙 X) (𝟙 X) (𝟙 X) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  apply E.q_comp_of_isPullback _ _ _ _ h _ (Iso.refl _)
  · simp [QConstruction.of]
  · simp [QConstruction.of]

/-- The crucial Q-construction relation for a conflation, obtained from its
kernel pullback square. -/
lemma conflation_q_relation {S : ShortComplex C} (hS : E.conflation S) :
    E.fromZero (QConstruction.of E.deflation E.inflation S.X₃) ≫
        E.qDeflation S.g (E.deflation_of_conflation hS) =
      E.fromZeroTotal (QConstruction.of E.deflation E.inflation S.X₁) ≫
        E.qInflation S.f (E.inflation_of_conflation hS) := by
  rw [E.fromZeroTotal_qInflation]
  apply E.q_comp_of_isPullback _ _ _ _ (E.conflation_kernel_isPullback hS) _ (Iso.refl _)
  · simp [QConstruction.of]
  · simp [QConstruction.of]

/-- The algebraic loop of an object under any groupoid-valued functor on QConstruction.
The application of interest is the actual realized fundamental groupoid. -/
def qObjectClass {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D) (X : C) :
    End (F.obj E.qZero) :=
  End.of (F.map (E.fromZeroTotal (QConstruction.of E.deflation E.inflation X)) ≫
    inv (F.map (E.fromZero (QConstruction.of E.deflation E.inflation X))))

/-- Exact sequences impose the genuine object-loop relation in every
Q-groupoid target, without commutativity being assumed. -/
lemma qObjectClass_conflation {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {S : ShortComplex C} (hS : E.conflation S) :
    E.qObjectClass F S.X₂ = E.qObjectClass F S.X₁ * E.qObjectClass F S.X₃ := by
  have h₁ := congrArg F.map (E.fromZero_qInflation S.f (E.inflation_of_conflation hS))
  have h₂ := congrArg F.map (E.fromZeroTotal_qDeflation S.g (E.deflation_of_conflation hS))
  have h₃ := congrArg F.map (E.conflation_q_relation hS)
  simp only [Functor.map_comp] at h₁ h₂ h₃
  apply End.ext
  simp only [End.mul_asHom, qObjectClass]
  apply (cancel_mono (F.map (E.fromZero (QConstruction.of E.deflation E.inflation S.X₂)))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h₁]
  simp only [IsIso.inv_hom_id_assoc]
  rw [← h₃, ← h₂]
  simp

/-- Canonical object loops pairwise commute in every Q-groupoid target.
This does not assert that arbitrary topological loops are generated by them. -/
lemma qObjectClass_commute {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D) (X Y : C) :
    Commute (E.qObjectClass F X) (E.qObjectClass F Y) := by
  exact (E.qObjectClass_conflation F (E.conflation_biprod_inl_snd X Y)).symm.trans
    (E.qObjectClass_conflation F (E.conflation_biprod_inr_fst X Y))



end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0075",
  colib_ref "WeibelKBook" "IV, proof of Proposition 6.2, relation preceding (6.2.2), page 54"
    "adaptation" "Q-arrow equality for a conflation, before any fundamental group claim"]
  CategoryTheory.ExactCategory.ExactStructure.conflation_q_relation

attribute [colib_tag "COL-0075",
  colib_ref "WeibelKBook" "IV, proof of Proposition 6.2, equation (6.2.2), page 54"
    "background" "Object-class relations in a groupoid target; no topological loop identification"]
  CategoryTheory.ExactCategory.ExactStructure.qObjectClass
  CategoryTheory.ExactCategory.ExactStructure.qObjectClass_conflation
  CategoryTheory.ExactCategory.ExactStructure.qObjectClass_commute
