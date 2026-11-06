/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteTermFiltration

/-! # Original term evaluation and single-term insertion in finite strata

Evaluation takes the actual original term, and insertion is mathlib's original
single complex at a degree in the specified interval. Both are genuinely
exact. Their actual composites are the identity at the same degree and zero
at other degrees, and insertion after evaluation is the original layer.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteTermEvaluation`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
universe v u
namespace CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The original single complex functor preserves every actual short exact sequence. -/
theorem singleTerm_shortExact (S : ShortComplex A) (hS : S.ShortExact) (n : ℤ) :
    (S.map (single A (ComplexShape.up ℤ) n)).ShortExact := by
  apply (shortExact_iff_degreewise_shortExact _).2
  intro i
  change (S.map (single A (ComplexShape.up ℤ) n ⋙ eval A (ComplexShape.up ℤ) i)).ShortExact
  by_cases hi : i = n
  · subst i
    exact (ShortComplex.shortExact_iff_of_iso
      (S.mapNatIso (singleCompEvalIsoSelf A (ComplexShape.up ℤ) n))).2 hS
  · exact {
      mono_f := (isZero_single_obj_X (ComplexShape.up ℤ) n S.X₁ i hi).mono _
      epi_g := (isZero_single_obj_X (ComplexShape.up ℤ) n S.X₃ i hi).epi _
      exact := ShortComplex.exact_of_isZero_X₂ _
        (isZero_single_obj_X (ComplexShape.up ℤ) n S.X₂ i hi) }

variable (P : ObjectProperty A)

/-- The original term evaluation from a specified actual bound stratum. -/
def finiteTermEvaluation (a b n : ℤ) :
    (fixedTermsBounds P a b).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((fixedTermsBounds P a b).ι ⋙ (boundedTerms P).ι ⋙ eval A (ComplexShape.up ℤ) n)
    (fun K ↦ K.obj.property.2 n)

@[simp] theorem finiteTermEvaluation_map (a b n : ℤ)
    {K L : (fixedTermsBounds P a b).FullSubcategory} (f : K ⟶ L) :
    ((finiteTermEvaluation P a b n).map f).hom = f.hom.hom.f n := rfl

instance finiteTermEvaluation_additive (a b n : ℤ) : (finiteTermEvaluation P a b n).Additive :=
  inferInstanceAs (Functor.Additive (P.lift _ _))

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- Insert the actual P-object by the original single complex at an allowed degree. -/
def finiteTermSingle (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b) :
    P.FullSubcategory ⥤ (fixedTermsBounds P a b).FullSubcategory :=
  (fixedTermsBounds P a b).lift
    ((boundedTerms P).lift (P.ι ⋙ single A (ComplexShape.up ℤ) n)
      (fun X ↦ boundedTerms_single_mem P n X.obj X.property))
    (fun X i hi ↦ isZero_single_obj_X (ComplexShape.up ℤ) n X.obj i (by
      rcases hi with hi | hi <;> omega))

@[simp] theorem finiteTermSingle_map (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b)
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((finiteTermSingle P a b n ha hb).map f).hom.hom =
      (single A (ComplexShape.up ℤ) n).map f.hom := rfl

instance finiteTermSingle_additive (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b) :
    (finiteTermSingle P a b n ha hb).Additive := by
  dsimp [finiteTermSingle]
  infer_instance

/-- The actual layer is precisely original evaluation followed by original insertion. -/
theorem finiteTermEvaluation_single (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b) :
    finiteTermEvaluation P a b n ⋙ finiteTermSingle P a b n ha hb = finiteTermLayer P a b n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Insertion followed by evaluation in the same degree is naturally the identity. -/
def finiteTermSingleEvaluationIso (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b) :
    finiteTermSingle P a b n ha hb ⋙ finiteTermEvaluation P a b n ≅ 𝟭 P.FullSubcategory :=
  NatIso.ofComponents (fun X ↦ P.isoMk (singleObjXSelf (ComplexShape.up ℤ) n X.obj)) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    exact (singleCompEvalIsoSelf A (ComplexShape.up ℤ) n).hom.naturality f.hom)

/-- In every other degree the actual composite is naturally the zero functor. -/
def finiteTermSingleEvaluationZeroIso (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b)
    (j : ℤ) (hj : j ≠ n) :
    finiteTermSingle P a b n ha hb ⋙ finiteTermEvaluation P a b j ≅
      (Functor.const P.FullSubcategory).obj (0 : P.FullSubcategory) :=
  NatIso.ofComponents (fun X ↦ P.isoMk
    ((isZero_single_obj_X (ComplexShape.up ℤ) n X.obj j hj).iso
      (P.ι.map_isZero (isZero_zero _)))) (by
        intro X Y f
        apply ObjectProperty.hom_ext
        exact (isZero_single_obj_X (ComplexShape.up ℤ) n X.obj j hj).eq_of_src _ _)

variable [(abelianExactStructure A).IsExtensionClosed P]
local instance finiteTermEvaluation_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- Actual evaluation preserves inherited conflations, without kernel closure. -/
def finiteTermEvaluationExact (a b n : ℤ) :
    ExactFunctor (fixedTermsExactStructure P a b)
      (ExactSubcategory.exactStructure (abelianExactStructure A) P) where
  toFunctor := finiteTermEvaluation P a b n
  map_conflation S hS := (shortExact_iff_degreewise_shortExact
    (S.map ((fixedTermsBounds P a b).ι ⋙ (boundedTerms P).ι))).1 hS n

/-- Actual single-term insertion preserves inherited conflations. -/
def finiteTermSingleExact (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b) :
    ExactFunctor (ExactSubcategory.exactStructure (abelianExactStructure A) P)
      (fixedTermsExactStructure P a b) where
  toFunctor := finiteTermSingle P a b n ha hb
  map_conflation S hS := singleTerm_shortExact (S.map P.ι) hS n

end CochainComplex
