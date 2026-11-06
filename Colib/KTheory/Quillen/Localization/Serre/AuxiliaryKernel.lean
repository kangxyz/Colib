/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Uses native Q-construction and intrinsic abelian full-subcategory exact structure. -/

public import Colib.CategoryTheory.Abelian.SerreClass.OverKernel
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.QConstruction.Abelian.Surjections
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion
public import Colib.Topology.ClassifyingSpace.Contraction

/-!
# The auxiliary kernel categories for Serre localization

The category over a fixed ambient object is a genuine restricted-span
Q-category of the ordinary slice. Its epi and mono conditions are imposed
on the underlying ambient maps. Kernel is realized by pullback along zero,
so its functoriality is inherited from the slice pullback functor.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.SerreLocalization

open CategoryTheory.Abelian.SerreLocalization CategoryTheory.Abelian

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{u} C] [Abelian C]

/-- The actual Q-style category of ambient epi/mono spans over `N`. -/
abbrev OverQ (N : C) := QConstruction (overDeflation N) (overInflation N)

/-- Forgetting the map to `N` is compatible with the actual span composition. -/
def overForgetCompatible (N : C) :
    QConstruction.CompatibleFunctor (overDeflation N) (overInflation N)
      (abelianExactStructure C).deflation (abelianExactStructure C).inflation :=
  QConstruction.CompatibleFunctor.ofPreservesPullbacks _ _ _ _ (Over.forget N)
    (fun f h => (abelianExactStructure_deflation_iff C f.left).2 h)
    (fun f h => (abelianExactStructure_inflation_iff C f.left).2 h)

/-- The underlying ambient Q-functor of the slice Q-category. -/
def overForgetQ (N : C) : OverQ N ⥤ (abelianExactStructure C).QCategory :=
  (overForgetCompatible N).mapQ

/-- The ambient Q-forgetful functor is faithful: an apex isomorphism commuting
with the right legs automatically commutes with the structure map to `N`. -/
instance overForgetQ_faithful (N : C) : (overForgetQ N).Faithful where
  map_injective := by
    rintro X Y ⟨s⟩ ⟨t⟩ h
    change QConstruction.mkHom _ _ ((overForgetCompatible N).mapSpan s) =
      QConstruction.mkHom _ _ ((overForgetCompatible N).mapSpan t) at h
    obtain ⟨e, hl, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ _ _).1 h
    change s.apex.left ≅ t.apex.left at e
    change e.hom ≫ t.l.left = s.l.left at hl
    change e.hom ≫ t.r.left = s.r.left at hr
    have he : e.hom ≫ t.apex.hom = s.apex.hom := by
      rw [← Over.w t.r, ← Category.assoc, hr, Over.w s.r]
    apply QConstruction.mkHom_eq_of_apexIso _ _ s t (Over.isoMk e he)
    · apply Over.OverMorphism.ext
      exact hl
    · apply Over.OverMorphism.ext
      exact hr

/-- Kernel supplies a genuine Q-compatible functor on the slice. -/
@[implicit_reducible]
def overKernelCompatible (N : C) :
    QConstruction.CompatibleFunctor (overDeflation N) (overInflation N)
      (abelianExactStructure C).deflation (abelianExactStructure C).inflation :=
  QConstruction.CompatibleFunctor.ofPreservesPullbacks _ _ _ _ (overKernel N)
    (fun f h => (abelianExactStructure_deflation_iff C _).2
      (MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
        (overKernel_map_isPullback f).flip h))
    (fun f h => (abelianExactStructure_inflation_iff C _).2
      (MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms C)
        (overKernel_map_isPullback f).flip h))

/-- The kernel Q-functor, before restriction to Serre-isomorphism objects. -/
@[implicit_reducible]
def overKernelQ (N : C) : OverQ N ⥤ (abelianExactStructure C).QCategory :=
  (overKernelCompatible N).mapQ

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- The auxiliary objects whose ambient map to `N` is a Serre isomorphism. -/
@[implicit_reducible]
def auxiliaryKernelProperty (N : C) : ObjectProperty (OverQ N) :=
  fun X => P.isoModSerre X.obj.of.hom

/-- Quillen's auxiliary category: Serre-isomorphisms into `N`, with actual
Q-spans commuting over `N` as morphisms. -/
abbrev AuxiliaryKernel (N : C) := (auxiliaryKernelProperty P N).FullSubcategory

/-- The actual kernel functor on Quillen's auxiliary category, landing in
`Q(P)`. Arrow maps are lifted through the proved fully faithful Q-inclusion. -/
def auxiliaryKernelFunctor (N : C) :
    AuxiliaryKernel P N ⥤ (abelianExactStructure P.FullSubcategory).QCategory
      where
  obj X := QConstruction.of _ _ ⟨(overKernel N).obj X.obj.obj.of, overKernel_mem P _ X.property⟩
  map f := (Devissage.mapQ P).preimage ((overKernelQ N).map f.hom)
  map_id X := by
    apply (Devissage.mapQ P).map_injective
    calc
      _ = (overKernelQ N).map (𝟙 X.obj) := (Devissage.mapQ P).map_preimage _
      _ = 𝟙 _ := (overKernelQ N).map_id _
      _ = _ := ((Devissage.mapQ P).map_id (QConstruction.of _ _
        ⟨(overKernel N).obj X.obj.obj.of, overKernel_mem P _ X.property⟩)).symm
  map_comp f g := by
    apply (Devissage.mapQ P).map_injective
    erw [Functor.map_preimage, Functor.map_comp, Functor.map_comp,
      Functor.map_preimage, Functor.map_preimage]

/-- Inclusion after the auxiliary kernel functor is the kernel of the actual
slice span, strictly at both objects and arrows. -/
@[simp]
theorem auxiliaryKernelFunctor_inclusion (N : C) :
    auxiliaryKernelFunctor P N ⋙ Devissage.mapQ P =
      (auxiliaryKernelProperty P N).ι ⋙ overKernelQ N := by
  refine CategoryTheory.Functor.ext (F := auxiliaryKernelFunctor P N ⋙ Devissage.mapQ P)
    (G := (auxiliaryKernelProperty P N).ι ⋙ overKernelQ N) (fun X => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (Devissage.mapQ P).map ((auxiliaryKernelFunctor P N).map f) =
    (overKernelQ N).map f.hom
  exact (Devissage.mapQ P).map_preimage (X := (auxiliaryKernelFunctor P N).obj X)
    (Y := (auxiliaryKernelFunctor P N).obj Y) ((overKernelQ N).map f.hom)

/-- The epimorphic objects of the auxiliary category. -/
@[implicit_reducible]
def epiAuxiliaryKernelProperty (N : C) : ObjectProperty (OverQ N) :=
  fun X => P.isoModSerre X.obj.of.hom ∧ Epi X.obj.of.hom

/-- The full subcategory of `OverQ N` consisting of epimorphisms over `N` that become
isomorphisms modulo the Serre class `P`. -/
abbrev EpiAuxiliaryKernel (N : C) := (epiAuxiliaryKernelProperty P N).FullSubcategory

/-- The ordinary full-subcategory inclusion `E_N → H_N`. -/
def epiAuxiliaryInclusion (N : C) : EpiAuxiliaryKernel P N ⥤ AuxiliaryKernel P N :=
  ObjectProperty.ιOfLE (fun _ h => h.1)

/-- The actual kernel Q-functor restricted to epimorphic Serre-isomorphisms. -/
def epiAuxiliaryKernelFunctor (N : C) :
    EpiAuxiliaryKernel P N ⥤ (abelianExactStructure P.FullSubcategory).QCategory
      :=
  epiAuxiliaryInclusion P N ⋙ auxiliaryKernelFunctor P N

/-- The identity epimorphism, the distinguished object in the auxiliary category. -/
def epiAuxiliaryBase (N : C) : EpiAuxiliaryKernel P N :=
  ⟨QConstruction.of _ _ (Over.mk (𝟙 N)), P.isoModSerre.id_mem N, inferInstanceAs (Epi (𝟙 N))⟩

/-- The distinguished auxiliary object has zero kernel within the actual
Serre subcategory, not merely after quotienting. -/
theorem epiAuxiliaryBase_kernel_isZero (N : C) :
    IsZero ((epiAuxiliaryKernelFunctor P N).obj (epiAuxiliaryBase P N)).obj.of :=
  IsZero.of_full_of_faithful_of_isZero P.ι _ (overKernel_identity_isZero N)

/-- The reversed structure epimorphism gives the canonical Q-arrow from the
identity object to any epimorphic auxiliary object. -/
def epiAuxiliaryBaseArrow {N : C} (X : EpiAuxiliaryKernel P N) : epiAuxiliaryBase P N ⟶ X :=
  ObjectProperty.homMk (QConstruction.mkHom _ _
    { apex := X.obj.obj.of
      l := Over.homMk (V := Over.mk (𝟙 N)) X.obj.obj.of.hom (by simp)
      r := 𝟙 _
      wl := X.property.2
      wr := by change Mono (𝟙 X.obj.obj.of.left); infer_instance })

@[simp]
theorem map_epiAuxiliaryKernelFunctor {N : C} {X Y : EpiAuxiliaryKernel P N} (f : X ⟶ Y) :
    (Devissage.mapQ P).map ((epiAuxiliaryKernelFunctor P N).map f) =
      (overKernelQ N).map f.hom := by
  exact (Devissage.mapQ P).map_preimage
    (X := (epiAuxiliaryKernelFunctor P N).obj X) (Y := (epiAuxiliaryKernelFunctor P N).obj Y) _

/-- The canonical base arrow induces a surjective arrow on kernels. -/
theorem epiAuxiliaryBaseArrow_kernel_surjection {N : C} (X : EpiAuxiliaryKernel P N) :
    QConstruction.IsSurjection ((epiAuxiliaryKernelFunctor P N).map (epiAuxiliaryBaseArrow P X))
      := by
  let : (CategoryTheory.ObjectProperty.exactInclusion P).toFunctor.ReflectsIsomorphisms :=
    inferInstanceAs P.ι.ReflectsIsomorphisms
  apply (QConstruction.isSurjection_mapQ_iff (CategoryTheory.ObjectProperty.exactInclusion P) _).1
  change QConstruction.IsSurjection ((Devissage.mapQ P).map
    ((epiAuxiliaryKernelFunctor P N).map (epiAuxiliaryBaseArrow P X)))
  rw [map_epiAuxiliaryKernelFunctor]
  change QConstruction.IsSurjection (QConstruction.mkHom _ _ ((overKernelCompatible N).mapSpan
    { apex := X.obj.obj.of
      l := Over.homMk (V := Over.mk (𝟙 N)) X.obj.obj.of.hom (by simp)
      r := 𝟙 _
      wl := X.property.2
      wr := by change Mono (𝟙 X.obj.obj.of.left); infer_instance }))
  apply (QConstruction.isSurjection_mkHom_iff _).2
  change IsIso ((overKernel N).map (𝟙 X.obj.obj.of))
  rw [(overKernel N).map_id]
  infer_instance

/-- A map from the distinguished auxiliary object with surjective kernel
map is forced to be the canonical reversed structure epimorphism. -/
theorem epiAuxiliaryBaseArrow_unique {N : C} {X : EpiAuxiliaryKernel P N}
    (f : epiAuxiliaryBase P N ⟶ X)
    (hf : QConstruction.IsSurjection ((epiAuxiliaryKernelFunctor P N).map f)) :
    f = epiAuxiliaryBaseArrow P X := by
  have h := hf.mapQ (CategoryTheory.ObjectProperty.exactInclusion P)
  change QConstruction.IsSurjection ((Devissage.mapQ P).map ((epiAuxiliaryKernelFunctor P N).map
    f)) at h
  rw [map_epiAuxiliaryKernelFunctor] at h
  obtain ⟨s, hs⟩ := Quotient.exists_rep f.hom
  change Span (overDeflation N) (overInflation N) (Over.mk (𝟙 N)) X.obj.obj.of at s
  change QConstruction.mkHom _ _ s = f.hom at hs
  rw [← hs] at h
  have hk : IsIso ((overKernel N).map s.r) :=
    (QConstruction.isSurjection_mkHom_iff ((overKernelCompatible N).mapSpan s)).1 h
  have hl : Epi s.l.left := s.wl
  have hr : Mono s.r.left := s.wr
  have hw : s.l.left = s.apex.hom := by
    have hw' := Over.w s.l
    change s.l.left ≫ 𝟙 N = s.apex.hom at hw'
    exact (Category.comp_id _).symm.trans hw'
  have he : Epi s.apex.hom := hw ▸ hl
  have ht : Epi X.obj.obj.of.hom := X.property.2
  have hi : IsIso s.r := over_isIso_of_mono_of_kernel_isIso s.r
  apply ObjectProperty.hom_ext
  rw [← hs]
  apply QConstruction.mkHom_eq_of_apexIso _ _ s _ (asIso s.r)
  · apply Over.OverMorphism.ext
    exact (Over.w s.r).trans hw.symm
  · simp

/-- The actual comma category of kernel Q-arrows into a fixed Serre object. -/
abbrev EpiKernelComma (N : C) (T : (abelianExactStructure P.FullSubcategory).QCategory) :=
  CostructuredArrow (epiAuxiliaryKernelFunctor P N) T

/-- Select those comma objects whose kernel arrow is a reversed epimorphism. -/
@[implicit_reducible]
def surjectiveKernelCommaProperty (N : C) (T :
  (abelianExactStructure P.FullSubcategory).QCategory) :
    ObjectProperty (EpiKernelComma P N T) := fun X => QConstruction.IsSurjection X.hom

/-- The full subcategory of the kernel comma category over `T` whose structure Q-arrow is
represented by a reversed epimorphism. -/
abbrev SurjectiveKernelComma (N : C) (T : (abelianExactStructure P.FullSubcategory).QCategory) :=
  (surjectiveKernelCommaProperty P N T).FullSubcategory

/-- The reversed zero epimorphism from `T` to the kernel of the identity. -/
def initialKernelArrow (N : C) (T : (abelianExactStructure P.FullSubcategory).QCategory) :
    (epiAuxiliaryKernelFunctor P N).obj (epiAuxiliaryBase P N) ⟶ T := by
  let : Epi (0 : T.obj.of ⟶
      ((epiAuxiliaryKernelFunctor P N).obj (epiAuxiliaryBase P N)).obj.of) :=
    (epiAuxiliaryBase_kernel_isZero P N).epi _
  exact QConstruction.surjectionArrow (0 : T.obj.of ⟶
    ((epiAuxiliaryKernelFunctor P N).obj (epiAuxiliaryBase P N)).obj.of)

lemma initialKernelArrow_surjection (N : C) (T :
  (abelianExactStructure P.FullSubcategory).QCategory)
  :
    QConstruction.IsSurjection (initialKernelArrow P N T) := by
  let : Epi (0 : T.obj.of ⟶
      ((epiAuxiliaryKernelFunctor P N).obj (epiAuxiliaryBase P N)).obj.of) :=
    (epiAuxiliaryBase_kernel_isZero P N).epi _
  exact QConstruction.isSurjection_surjectionArrow _

/-- The candidate initial object is the identity epimorphism over `N`. -/
def surjectiveKernelCommaInitial (N : C) (T :
  (abelianExactStructure P.FullSubcategory).QCategory) :
    SurjectiveKernelComma P N T :=
  ⟨CostructuredArrow.mk (Y := epiAuxiliaryBase P N) (initialKernelArrow P N T),
    initialKernelArrow_surjection P N T⟩

/-- The canonical arrow to each surjective-kernel object satisfies the comma
triangle because zero-source Q-arrows with the same upper endpoint agree. -/
def surjectiveKernelCommaInitialTo {N : C} {T :
  (abelianExactStructure P.FullSubcategory).QCategory}
    (X : SurjectiveKernelComma P N T) : surjectiveKernelCommaInitial P N T ⟶ X :=
  ObjectProperty.homMk (CostructuredArrow.homMk (epiAuxiliaryBaseArrow P X.obj.left) (by
    apply QConstruction.arrowUpper_injective_of_isZero (epiAuxiliaryBase_kernel_isZero P N)
    exact ((epiAuxiliaryBaseArrow_kernel_surjection P X.obj.left).comp X.property).trans
      (initialKernelArrow_surjection P N T).symm))

/-- This is a genuine initial object: a competing comma arrow must induce a
surjective kernel map, and is therefore the unique reversed structure epi. -/
def surjectiveKernelCommaInitialIsInitial (N : C)
    (T : (abelianExactStructure P.FullSubcategory).QCategory) :
    IsInitial (surjectiveKernelCommaInitial P N T) :=
  IsInitial.ofUniqueHom (surjectiveKernelCommaInitialTo P) (by
    intro X f
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply epiAuxiliaryBaseArrow_unique P f.hom.left
    have h : QConstruction.IsSurjection ((epiAuxiliaryKernelFunctor P N).map f.hom.left ≫
      X.obj.hom) := by
      rw [CostructuredArrow.w f.hom]
      exact initialKernelArrow_surjection P N T
    exact h.of_comp.1)

/-- The surjective-kernel subcategory has an actual classifying-space contraction. -/
theorem surjectiveKernelComma_contractible (N : C)
    (T : (abelianExactStructure P.FullSubcategory).QCategory) :
    ContractibleSpace (ClassifyingSpace (SurjectiveKernelComma P N T)) :=
  classifyingSpace_contractible_of_isInitial (surjectiveKernelCommaInitialIsInitial P N T)

end CategoryTheory.ExactCategory.SerreLocalization
