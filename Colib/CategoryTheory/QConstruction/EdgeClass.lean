/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.QConstruction.ObjectClass

/-!
# Closed Q-edges in groupoid-valued functors

Each actual Q-edge closes using the canonical zero-apex arrows. Its class in
any groupoid target equals a canonical object class, derived by factoring the
representative span into an admissible quotient and inclusion.

## Implementation provenance

Extracted from `Quillen/KTheory/GrothendieckComparison/Edges.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The exact-structure assumptions,
independent object/hom universes, actual functors and generator maps are retained.
This is purely algebraic and makes no identification with topological π₁ or K₀.
-/

@[expose] public noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Every admissible span factors as the reverse quotient followed by the
forward inclusion. -/
lemma qSpan_factor {X Y : C} (s : Span E.deflation E.inflation X Y) :
    QConstruction.mkHom E.deflation E.inflation s =
      E.qDeflation s.l s.wl ≫ E.qInflation s.r s.wr := by
  symm
  have h : IsPullback (𝟙 s.apex) (𝟙 s.apex) (𝟙 s.apex) (𝟙 s.apex) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  apply E.q_comp_of_isPullback _ _ _ _ h s (Iso.refl _)
  · simp
  · simp

/-- Close a Q-arrow to a based endomorphism in any groupoid-valued image,
using the canonical zero-apex arrows. -/
def qEdgeClass {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {X Y : E.QCategory} (f : X ⟶ Y) : End (F.obj E.qZero) :=
  End.of (F.map (E.fromZero X) ≫ F.map f ≫ inv (F.map (E.fromZero Y)))

/-- An admissible inclusion contributes a trivial closed edge. -/
@[simp] lemma qEdgeClass_qInflation {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    E.qEdgeClass F (E.qInflation i hi) = 1 := by
  apply End.ext
  simp only [qEdgeClass, End.one_asHom]
  rw [← Category.assoc, ← F.map_comp, E.fromZero_qInflation]
  exact IsIso.hom_inv_id _

/-- Closed-edge classes respect concatenation, with the endomorphism group
multiplication convention made explicit. -/
lemma qEdgeClass_comp {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {X Y Z : E.QCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    E.qEdgeClass F (f ≫ g) = E.qEdgeClass F g * E.qEdgeClass F f := by
  apply End.ext
  simp [qEdgeClass, Category.assoc]

/-- Closing the Q-arrow of an admissible quotient yields its kernel object
class. -/
lemma qEdgeClass_qDeflation {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {S : ShortComplex C} (hS : E.conflation S) :
    E.qEdgeClass F (E.qDeflation S.g (E.deflation_of_conflation hS)) =
      E.qObjectClass F S.X₁ := by
  have h₁ := congrArg F.map (E.fromZero_qInflation S.f (E.inflation_of_conflation hS))
  have h₂ := congrArg F.map (E.conflation_q_relation hS)
  simp only [Functor.map_comp] at h₁ h₂
  apply End.ext
  dsimp only [qEdgeClass, qObjectClass]
  apply (cancel_mono (F.map (E.fromZero (QConstruction.of E.deflation E.inflation S.X₂)))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h₁]
  simp only [IsIso.inv_hom_id_assoc]
  exact h₂

/-- Every represented Q-arrow has a closed-edge class equal to an object class. -/
lemma qEdgeClass_span {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {X Y : C} (s : Span E.deflation E.inflation X Y) :
    ∃ K : C, E.qEdgeClass F (QConstruction.mkHom E.deflation E.inflation s) =
      E.qObjectClass F K := by
  obtain ⟨K, i, hi, hS⟩ := s.wl
  refine ⟨K, ?_⟩
  rw [E.qSpan_factor, E.qEdgeClass_comp, E.qEdgeClass_qInflation, one_mul]
  exact E.qEdgeClass_qDeflation F hS

/-- The normalization applies to every actual Q-morphism, independently of
its chosen span representative. -/
lemma qEdgeClass_eq_objectClass {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {X Y : E.QCategory} (f : X ⟶ Y) :
    ∃ K : C, E.qEdgeClass F f = E.qObjectClass F K := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  refine Quotient.inductionOn f (fun s => ?_)
  exact E.qEdgeClass_span F s


end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0076",
  colib_ref "WeibelKBook" "IV, proof of Proposition 6.2 and Example 6.2.3, page 54"
    "background"
    "Closed-edge normalization in groupoid targets, without identification with topological loops"]
  CategoryTheory.ExactCategory.ExactStructure.qEdgeClass_eq_objectClass
  CategoryTheory.ExactCategory.ExactStructure.qEdgeClass_qDeflation
  CategoryTheory.ExactCategory.ExactStructure.qEdgeClass_comp
