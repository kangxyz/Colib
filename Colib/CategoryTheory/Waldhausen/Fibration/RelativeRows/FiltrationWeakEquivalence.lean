/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.FiltrationEquivalence
public import Mathlib.CategoryTheory.Widesubcategory

/-! # The genuine presentation on the original fine-weak morphism categories

Restrict the proved original-filtration/completion equivalence to the actual
fine weak maps. The unit and counit are original categorical isomorphisms,
so they remain maps in those weak categories. Their classifying-space
homotopy equivalence retains the original forward and inverse functors.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/FiltrationWeakEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

instance chainFineWeak_multiplicative (n : SimplexCategory) :
    (chainFineWeak N n).IsMultiplicative where
  id_mem _ _ := V.weq.id_mem _
  comp_mem _ _ hα hβ i := V.weq.comp_mem _ _ (hα i) (hβ i)

/-- Actual chain isomorphisms are pointwise fine weak maps. -/
theorem chainFineWeak_iso {n : SimplexCategory} {F G : CofibrationWeakChain N n}
    (f : F ⟶ G) [IsIso f] : chainFineWeak N n f := by
  let : IsIso f.hom := (cofibrationWeakChains N n).ι.map_isIso f
  intro i
  exact V.weq_iso _ (inferInstance : IsIso (f.hom.app i))

/-- The actual fine-weak morphism category on the original relative rows. -/
abbrev FineWeakRows (n : SimplexCategory) := WideSubcategory (waldhausenStructure N n).weq

/-- The actual pointwise fine-weak morphism category on the original admissible chains. -/
abbrev FineWeakChains (n : SimplexCategory) := WideSubcategory (chainFineWeak N n)

/-- Restrict the original initial-filtration functor to actual fine weak maps. -/
def weakFiltrationPresentation (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    FineWeakRows N n ⥤ FineWeakChains N n where
  obj F := ⟨(filtrationPresentation N he n).obj F.obj⟩
  map f := ⟨(filtrationPresentation N he n).map f.hom,
    (filtrationPresentation_weak_iff N he f.hom).2 f.property⟩
  map_id F := WideSubcategory.hom_ext _ ((filtrationPresentation N he n).map_id F.obj)
  map_comp f g := WideSubcategory.hom_ext _ ((filtrationPresentation N he n).map_comp f.hom g.hom)

/-- Restrict the actual zero-augmented cofiber completion to pointwise fine weak maps. -/
def weakCompletionFunctor (n : SimplexCategory) : FineWeakChains N n ⥤ FineWeakRows N n where
  obj F := ⟨(completionFunctor N n).obj F.obj⟩
  map f := ⟨(completionFunctor N n).map f.hom, completionFunctor_weak N f.hom f.property⟩
  map_id F := WideSubcategory.hom_ext _ ((completionFunctor N n).map_id F.obj)
  map_comp f g := WideSubcategory.hom_ext _ ((completionFunctor N n).map_comp f.hom g.hom)

/-- The forward weak-chain map retains every original initial-interval component. -/
@[simp] theorem weakFiltrationPresentation_map_app (he : ExtensionAxiom N.coarse)
    {n : SimplexCategory} {F G : FineWeakRows N n} (f : F ⟶ G) (i : Fin (n.len + 1)) :
    (((weakFiltrationPresentation N he n).map f).hom.hom).app i =
      f.hom.hom.hom.app (interval 0 i.succ (Fin.zero_le _)) := rfl

/-- The inverse weak-row map remains the actual cofiber completion map. -/
@[simp] theorem weakCompletionFunctor_map {n : SimplexCategory} {F G : FineWeakChains N n}
    (f : F ⟶ G) : ((weakCompletionFunctor N n).map f).hom =
      relativeCompletionMap N F.obj.property.1 F.obj.property.2
        G.obj.property.1 G.obj.property.2 f.hom.hom := rfl

/-- The original quotient-by-zero comparison is still an isomorphism in fine weak chains. -/
def weakCompletionFiltrationIso (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    𝟭 (FineWeakChains N n) ≅ weakCompletionFunctor N n ⋙ weakFiltrationPresentation N he n :=
  NatIso.ofComponents (fun F ↦ WideSubcategory.isoMk ((completionFiltrationIso N he n).app F.obj)
    (chainFineWeak_iso N _) (chainFineWeak_iso N _)) (by
      intro F G f
      apply WideSubcategory.hom_ext
      exact (completionFiltrationIso N he n).hom.naturality f.hom)

/-- The actual row-side quotient-descent isomorphism remains in fine weak rows. -/
def weakFiltrationCompletionIso (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    𝟭 (FineWeakRows N n) ≅ weakFiltrationPresentation N he n ⋙ weakCompletionFunctor N n :=
  NatIso.ofComponents (fun F ↦ WideSubcategory.isoMk ((filtrationCompletionIso N he n).app F.obj)
    ((waldhausenStructure N n).weq_iso _ inferInstance)
    ((waldhausenStructure N n).weq_iso _ inferInstance)) (by
      intro F G f
      apply WideSubcategory.hom_ext
      exact (filtrationCompletionIso N he n).hom.naturality f.hom)

/-- The genuine equivalence of the actual fine-weak morphism categories. -/
def weakFiltrationEquivalence (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    FineWeakRows N n ≌ FineWeakChains N n :=
  CategoryTheory.Equivalence.mk (weakFiltrationPresentation N he n) (weakCompletionFunctor N n)
    (weakFiltrationCompletionIso N he n) (weakCompletionFiltrationIso N he n).symm

@[simp] theorem weakFiltrationEquivalence_functor (he : ExtensionAxiom N.coarse) (n :
    SimplexCategory) :
    (weakFiltrationEquivalence N he n).functor = weakFiltrationPresentation N he n := rfl

@[simp] theorem weakFiltrationEquivalence_inverse (he : ExtensionAxiom N.coarse) (n :
    SimplexCategory) :
    (weakFiltrationEquivalence N he n).inverse = weakCompletionFunctor N n := rfl

end CategoryTheory.Waldhausen.Fibration.RelativeRows
