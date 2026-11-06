/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Approximation.FinitePoset.Replacement
public import Colib.CategoryTheory.Waldhausen.Approximation.WeakComma
public import Colib.Topology.ClassifyingSpace.Contraction

/-!
# Weak comma cones from the approximation properties

App1 and App2 supply finite-poset weak comma cones and the stated nullhomotopies of their
    classifying maps.

Implementation provenance: `Quillen/Waldhausen/Approximation/FinitePoset/WeakCommaCone.lean` at
Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Limits.FinitePosetLatching CategoryTheory.Limits.FinitePosetInsertion
universe w w' z u v u' v'

namespace CategoryTheory.Waldhausen.HasApproximationProperty
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (Y : WideSubcategory V.weq)

/-- Forget only the original comma structure and weak-map proofs. -/
def weakCommaSource : WeakComma hF Y ⥤ C :=
  CostructuredArrow.proj hF.weakFunctor Y ⋙ wideSubcategoryInclusion W.weq

variable {J : Type w} [Category.{z} J] (K : J ⥤ WeakComma hF Y)

/-- The original structure arrows to Y are a strictly natural target cocone. -/
def weakCommaTargetCocone : Cocone ((K ⋙ weakCommaSource hF Y) ⋙ F) where
  pt := Y.obj
  ι := {
    app j := (K.obj j).hom.hom
    naturality i j f := by
      change F.map (K.map f).left.hom ≫ (K.obj j).hom.hom = (K.obj i).hom.hom ≫ 𝟙 Y.obj
      rw [Category.comp_id]
      exact congrArg (fun k ↦ k.hom) (CostructuredArrow.w (K.map f)) }

include h in
/-- App2 produces a genuine cone on the original weak-comma diagram from an
actual mapped colimit. Every cone leg is proved weak by App1 and saturation.
The new source attachment is an actual cofibration, with strict original legs. -/
theorem exists_weakCommaCocone_of_mappedColimit [V.weq.HasTwoOutOfThreeProperty]
    (c : Cocone (K ⋙ weakCommaSource hF Y)) (hc : IsColimit (F.mapCocone c)) :
    ∃ (d : Cocone K) (i : c.pt ⟶ d.pt.left.obj),
      W.cof i ∧ ∀ j, (d.ι.app j).left.hom = c.ι.app j ≫ i := by
  let q := hc.desc (weakCommaTargetCocone hF Y K)
  obtain ⟨Q, i, p, hi, hp, hip⟩ := h.lift q
  let Z : WeakComma hF Y :=
    CostructuredArrow.mk (Y := (⟨Q⟩ : WideSubcategory W.weq)) ⟨p, hp⟩
  have fac (j : J) : F.map (c.ι.app j ≫ i) ≫ p = (K.obj j).hom.hom := by
    rw [F.map_comp, Category.assoc, hip]
    exact hc.fac (weakCommaTargetCocone hF Y K) j
  have hw (j : J) : W.weq (c.ι.app j ≫ i) := by
    apply h.reflects
    apply V.weq.of_postcomp _ p hp
    rw [fac j]
    exact (K.obj j).hom.property
  let leg (j : J) : K.obj j ⟶ Z := CostructuredArrow.homMk
    ⟨c.ι.app j ≫ i, hw j⟩ (by apply WideSubcategory.hom_ext; exact fac j)
  let d : Cocone K := {
    pt := Z
    ι := {
      app := leg
      naturality j k a := by
        apply CostructuredArrow.hom_ext
        apply WideSubcategory.hom_ext
        change (K.map a).left.hom ≫ (c.ι.app k ≫ i) = (c.ι.app j ≫ i) ≫ 𝟙 Q
        rw [Category.comp_id, ← Category.assoc]
        exact congrArg (fun f ↦ f ≫ i) (c.w a) } }
  exact ⟨d, i, hi, fun _ ↦ rfl⟩

section Realization
variable {C₀ D₀ J₀ : Type u} [SmallCategory C₀] [SmallCategory D₀] [SmallCategory J₀]
  {W₀ : Structure C₀} {V₀ : Structure D₀} {F₀ : C₀ ⥤ D₀}
  (h₀ : HasApproximationProperty W₀ V₀ F₀)
  (hF₀ : IsExact W₀.cof W₀.weq V₀.cof V₀.weq F₀)
  [V₀.weq.HasTwoOutOfThreeProperty] (Y₀ : WideSubcategory V₀.weq)
  (K₀ : J₀ ⥤ WeakComma hF₀ Y₀)

include h₀ in
/-- The constructed actual comma cone nullhomotopes the ORIGINAL classifying
map of this diagram. The mapped-colimit hypothesis is structural; the finite-poset replacement
    case is constructed below. -/
theorem weakComma_classifyingMap_nullhomotopic_of_mappedColimit
    (c : Cocone (K₀ ⋙ weakCommaSource hF₀ Y₀)) (hc : IsColimit (F₀.mapCocone c)) :
    (classifyingSpaceMap K₀).hom.Nullhomotopic := by
  obtain ⟨d, _, _, _⟩ := exists_weakCommaCocone_of_mappedColimit h₀ hF₀ Y₀ K₀ c hc
  refine ⟨classifyingSpacePoint d.pt, ?_⟩
  have H := classifyingSpaceNaturalTransformationHomotopy d.ι
  exact ⟨by simpa only [classifyingSpaceMap_const] using H⟩
end Realization

end CategoryTheory.Waldhausen.HasApproximationProperty

namespace CategoryTheory.Waldhausen.HasApproximationProperty
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty] (Y : WideSubcategory V.weq)
  {J : Type w} [Category.{z} J] (K : J ⥤ WeakComma hF Y)
  (R : J ⥤ C) (p : R ⟶ K ⋙ weakCommaSource hF Y)
  (hp : ∀ x, W.weq (p.app x))

/-- The original comparison to the old weak comma structure gives the new
structure arrow, with no independent choices at its vertices. -/
def replacedCommaObject (x : J) : WeakComma hF Y :=
  CostructuredArrow.mk (Y := (⟨R.obj x⟩ : WideSubcategory W.weq))
    ⟨F.map (p.app x) ≫ (K.obj x).hom.hom,
      V.weq.comp_mem _ _ (hF.weak _ (hp x)) (K.obj x).hom.property⟩

include h hF p hp in
/-- App1 and target saturation prove the replacement's original diagram arrows
weak; no source saturation assumption is added. -/
theorem replacedComma_map_weak {x y : J} (f : x ⟶ y) : W.weq (R.map f) := by
  apply h.reflects
  apply V.weq.of_postcomp _ (F.map (p.app y)) (hF.weak _ (hp y))
  rw [← F.map_comp, p.naturality, F.map_comp]
  exact V.weq.comp_mem _ _ (hF.weak _ (hp x)) (hF.weak _ (K.map f).left.property)

/-- The coherent replacement lives in the original weak-comma category. -/
def replacedCommaDiagram : J ⥤ WeakComma hF Y where
  obj := replacedCommaObject hF Y K R p hp
  map {x y} f := CostructuredArrow.homMk
    ⟨R.map f, replacedComma_map_weak h hF Y K R p hp f⟩ (by
      apply WideSubcategory.hom_ext
      change F.map (R.map f) ≫ (F.map (p.app y) ≫ (K.obj y).hom.hom) =
        F.map (p.app x) ≫ (K.obj x).hom.hom
      rw [← Category.assoc, ← F.map_comp, p.naturality, F.map_comp, Category.assoc]
      exact congrArg (fun a ↦ F.map (p.app x) ≫ a)
        (congrArg (fun k ↦ k.hom) (CostructuredArrow.w (K.map f))))
  map_id x := by
    apply CostructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    exact R.map_id x
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    exact R.map_comp f g

/-- Its source diagram is literally the constructed source replacement. -/
theorem replacedCommaDiagram_source :
    replacedCommaDiagram h hF Y K R p hp ⋙ weakCommaSource hF Y = R := rfl

/-- The weak comparison is a natural transformation to the original diagram
inside the original weak-comma category. -/
def replacedCommaComparison : replacedCommaDiagram h hF Y K R p hp ⟶ K where
  app x := CostructuredArrow.homMk ⟨p.app x, hp x⟩ (by apply WideSubcategory.hom_ext; rfl)
  naturality x y f := by
    apply CostructuredArrow.hom_ext
    apply WideSubcategory.hom_ext
    exact p.naturality f

/-- Every original comparison component is the specified source weak map. -/
theorem replacedCommaComparison_left (x : J) :
    ((replacedCommaComparison h hF Y K R p hp).app x).left.hom = p.app x := rfl

section FinitePoset
variable {J₀ : Type w} [PartialOrder J₀] [Finite J₀]
  (T : FunctorialFactorization W) (K₀ : J₀ ⥤ WeakComma hF Y)

include h T in
/-- A finite original poset diagram admits a genuine coherent replacement and
an actual cone entirely in the original weak comma, from structural axioms. -/
theorem exists_finitePoset_weakComma_cone :
    ∃ L : J₀ ⥤ WeakComma hF Y, Nonempty (L ⟶ K₀) ∧ Nonempty (Cocone L) := by
  obtain ⟨R, p, hp, hR⟩ := exists_lowerPreservedReplacement F W V hF T
    (K₀ ⋙ weakCommaSource hF Y)
  obtain ⟨c, _, ⟨hFc⟩⟩ := hR.whole F
  let L := replacedCommaDiagram h hF Y K₀ R p hp
  obtain ⟨d, _, _, _⟩ := exists_weakCommaCocone_of_mappedColimit h hF Y L c hFc
  exact ⟨L, ⟨replacedCommaComparison h hF Y K₀ R p hp⟩, ⟨d⟩⟩
end FinitePoset

section Realization
variable {C₀ D₀ J₀ : Type u} [SmallCategory C₀] [SmallCategory D₀]
  [PartialOrder J₀] [Finite J₀]
  {W₀ : Structure C₀} {V₀ : Structure D₀} {F₀ : C₀ ⥤ D₀}
  (h₀ : HasApproximationProperty W₀ V₀ F₀)
  (hF₀ : IsExact W₀.cof W₀.weq V₀.cof V₀.weq F₀)
  [V₀.weq.HasTwoOutOfThreeProperty] (T₀ : FunctorialFactorization W₀)
  (Y₀ : WideSubcategory V₀.weq) (K₀ : J₀ ⥤ WeakComma hF₀ Y₀)

include h₀ T₀ in
/-- The original classifying map of every finite-poset diagram in the original
weak comma is nullhomotopic. No arbitrary-finite-simplicial-domain conclusion
is inferred from this restricted, completely constructed coning theorem. -/
theorem finitePoset_weakComma_classifyingMap_nullhomotopic :
    (classifyingSpaceMap K₀).hom.Nullhomotopic := by
  obtain ⟨L, ⟨p⟩, ⟨d⟩⟩ := exists_finitePoset_weakComma_cone h₀ hF₀ Y₀ T₀ K₀
  refine ⟨classifyingSpacePoint d.pt, ?_⟩
  exact ⟨(classifyingSpaceNaturalTransformationHomotopy p).symm.trans
    (by simpa only [classifyingSpaceMap_const] using
      classifyingSpaceNaturalTransformationHomotopy d.ι)⟩
end Realization
end CategoryTheory.Waldhausen.HasApproximationProperty

end
