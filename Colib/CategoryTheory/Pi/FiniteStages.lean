/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Pi.FiniteSupport
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.PUnit

/-!
# Finite stages of the canonical finite-support category

`FiniteStage C s` is the full subcategory of the original product on families zero outside
`s`. The transition `stageInclusion` retains the same family and all its morphisms. Restriction
to `s` is equivalent to the finite product, with inverse given by zero extension. This
comparison allows arbitrary zero objects outside the support. The empty stage and singleton
stages are included.

`finiteFamilyStageObjectProperty` describes the same stage inside `FiniteCategoryFamily C`;
`stageNestedEquivalence` compares the two full-subcategory presentations without changing the
ambient family. Its inclusions are available as actual exact functors.

Adapted from `Quillen/Aglib/CategoryTheory/Pi/FiniteStages.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The literal ambient
full subcategories and restriction, zero-extension and singleton maps are retained.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Pi

attribute [local instance] Abelian.hasFiniteBiproducts

variable {I : Type u} (C : I → Type v) [∀ i, Category.{w} (C i)] [∀ i, Abelian (C i)]

omit [∀ i, Abelian (C i)] in
/-- A family lies in the stage `s` when every coordinate outside `s` is a zero object. -/
def stageObjectProperty (s : Finset I) : ObjectProperty (∀ i, C i) :=
  fun M => ∀ i, i ∉ s → IsZero (M i)

/-- The finite stage is a full subcategory of the original ambient product. -/
abbrev FiniteStage (s : Finset I) := (stageObjectProperty C s).FullSubcategory

instance stageObjectProperty_serre (s : Finset I) : (stageObjectProperty C s).IsSerreClass where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := ∀ i, C i)
    exact ⟨Z, hZ, fun i _ => (Pi.eval C i).map_isZero hZ⟩
  prop_of_mono f hf h := by
    let := hf
    intro i hi
    let : Mono (f i) := (Pi.eval C i).map_mono f
    exact ObjectProperty.prop_of_mono (IsZero (C := C i)) (f i) (h i hi)
  prop_of_epi f hf h := by
    let := hf
    intro i hi
    let : Epi (f i) := (Pi.eval C i).map_epi f
    exact ObjectProperty.prop_of_epi (IsZero (C := C i)) (f i) (h i hi)
  prop_X₂_of_shortExact h h₁ h₃ := by
    intro i hi
    exact ((h.map_of_exact (Pi.eval C i)).exact).isZero_of_both_isZero (h₁ i hi) (h₃ i hi)

omit [∀ i, Abelian (C i)] in
/-- Enlarging the finite set weakens the stage condition. -/
theorem stageObjectProperty_mono {s t : Finset I} (h : s ⊆ t) :
    stageObjectProperty C s ≤ stageObjectProperty C t :=
  fun _ hM i hi => hM i (fun his => hi (h his))

omit [∀ i, Abelian (C i)] in
/-- Every stage family has finite nonzero support. -/
theorem stageObjectProperty_le_finiteObjectSupport (s : Finset I) :
    stageObjectProperty C s ≤ finiteObjectSupport C := by
  intro M hM
  apply s.finite_toSet.subset
  intro i hi
  by_contra his
  exact hi (hM i his)

/-- An arbitrary zero family lies in every finite stage. -/
theorem stageObjectProperty_of_isZero (s : Finset I) {M : ∀ i, C i} (hM : IsZero M) :
    stageObjectProperty C s M :=
  fun i _ => (Pi.eval C i).map_isZero hM

omit [∀ i, Abelian (C i)] in
/-- The original finite-support family lies in a finite stage. -/
theorem finiteCategoryFamily_exists_stage (M : FiniteCategoryFamily C) :
    ∃ s : Finset I, stageObjectProperty C s M.obj := by
  classical
  refine ⟨M.property.toFinset, ?_⟩
  intro i hi
  by_contra hM
  exact hi (M.property.mem_toFinset.mpr hM)

/-- The standard exact structure on a finite stage. -/
abbrev stageExactStructure (s : Finset I) :=
  ExactCategory.abelianExactStructure (FiniteStage C s)

/-- The literal transition between two stages in the same ambient product. -/
def stageInclusion {s t : Finset I} (h : s ⊆ t) : FiniteStage C s ⥤ FiniteStage C t :=
  ObjectProperty.ιOfLE (stageObjectProperty_mono C h)

/-- The literal inclusion from a stage into the canonical finite-support family. -/
def stageToFiniteFamily (s : Finset I) : FiniteStage C s ⥤ FiniteCategoryFamily C :=
  ObjectProperty.ιOfLE (stageObjectProperty_le_finiteObjectSupport C s)

omit [∀ i, Abelian (C i)] in
@[simp]
theorem stageInclusion_obj_obj {s t : Finset I} (h : s ⊆ t) (M : FiniteStage C s) :
    ((stageInclusion C h).obj M).obj = M.obj := rfl

omit [∀ i, Abelian (C i)] in
@[simp]
theorem stageInclusion_map_hom {s t : Finset I} (h : s ⊆ t)
    {M N : FiniteStage C s} (f : M ⟶ N) : ((stageInclusion C h).map f).hom = f.hom := rfl

omit [∀ i, Abelian (C i)] in
@[simp]
theorem stageInclusion_refl (s : Finset I) : stageInclusion C (s := s) le_rfl = 𝟭 _ := rfl

omit [∀ i, Abelian (C i)] in
@[simp]
theorem stageInclusion_comp {r s t : Finset I} (h : r ⊆ s) (h' : s ⊆ t) :
    stageInclusion C h ⋙ stageInclusion C h' = stageInclusion C (h.trans h') := rfl

omit [∀ i, Abelian (C i)] in
@[simp]
theorem stageInclusion_comp_toFiniteFamily {s t : Finset I} (h : s ⊆ t) :
    stageInclusion C h ⋙ stageToFiniteFamily C t = stageToFiniteFamily C s := rfl

instance stageInclusion_additive {s t : Finset I} (h : s ⊆ t) :
    (stageInclusion C h).Additive where
  map_add := by intros; rfl

instance stageToFiniteFamily_additive (s : Finset I) : (stageToFiniteFamily C s).Additive where
  map_add := by intros; rfl

private theorem shortExact_fullSubcategory_iff
    {D : Type*} [Category* D] [Abelian D] (P : ObjectProperty D) [P.IsSerreClass]
    (S : ShortComplex P.FullSubcategory) : S.ShortExact ↔ (S.map P.ι).ShortExact := by
  constructor
  · exact (ObjectProperty.exactInclusion P).map_conflation S
  · intro h
    exact
      { exact := P.ι.reflects_exact_of_faithful S h.exact
        mono_f := P.ι.mono_of_mono_map h.mono_f
        epi_g := P.ι.epi_of_epi_map h.epi_g }

/-- Exactness of a stage sequence is tested in the original ambient product. -/
theorem shortExact_stage_iff (s : Finset I) (S : ShortComplex (FiniteStage C s)) :
    S.ShortExact ↔ (S.map (stageObjectProperty C s).ι).ShortExact :=
  shortExact_fullSubcategory_iff _ S

/-- The literal stage transition, bundled as an exact functor. -/
def stageExactInclusion {s t : Finset I} (h : s ⊆ t) :
    ExactCategory.ExactFunctor (stageExactStructure C s) (stageExactStructure C t) where
  toFunctor := stageInclusion C h
  map_conflation S hS := by
    apply (shortExact_stage_iff C t _).2
    exact (shortExact_stage_iff C s S).1 hS

/-- The literal stage inclusion into finite-support families, bundled as an exact functor. -/
def stageExactToFiniteFamily (s : Finset I) :
    ExactCategory.ExactFunctor (stageExactStructure C s) (finiteCategoryExactStructure C) where
  toFunctor := stageToFiniteFamily C s
  map_conflation S hS := by
    apply (shortExact_fullSubcategory_iff (finiteObjectSupport C) _).2
    exact (shortExact_stage_iff C s S).1 hS

/-- Exact evaluation of a stage at an actual coordinate of the original family. -/
def stageEvaluation (s : Finset I) (i : I) :
    ExactCategory.ExactFunctor (stageExactStructure C s)
      (ExactCategory.abelianExactStructure (C i)) :=
  (ObjectProperty.exactInclusion (stageObjectProperty C s)).comp (exactEvaluation C i)

@[simp]
theorem stageEvaluation_obj (s : Finset I) (i : I) (M : FiniteStage C s) :
    (stageEvaluation C s i).toFunctor.obj M = M.obj i := rfl

@[simp]
theorem stageEvaluation_map (s : Finset I) (i : I) {M N : FiniteStage C s} (f : M ⟶ N) :
    (stageEvaluation C s i).toFunctor.map f = f.hom i := rfl

@[simp]
theorem stageInclusion_comp_evaluation {s t : Finset I} (h : s ⊆ t) (i : I) :
    stageInclusion C h ⋙ (stageEvaluation C t i).toFunctor =
      (stageEvaluation C s i).toFunctor := rfl

@[simp]
theorem stageToFiniteFamily_comp_evaluation (s : Finset I) (i : I) :
    stageToFiniteFamily C s ⋙ (finiteCategoryEvaluation C i).toFunctor =
      (stageEvaluation C s i).toFunctor := rfl

/-- The same stage condition, regarded as a property of canonical finite-support families. -/
def finiteFamilyStageObjectProperty (s : Finset I) : ObjectProperty (FiniteCategoryFamily C) :=
  fun M => stageObjectProperty C s M.obj

instance finiteFamilyStageObjectProperty_serre (s : Finset I) :
    (finiteFamilyStageObjectProperty C s).IsSerreClass := by
  let := ObjectProperty.inclusion_preservesFiniteLimits (finiteObjectSupport C)
  let := ObjectProperty.inclusion_preservesFiniteColimits (finiteObjectSupport C)
  change ((stageObjectProperty C s).inverseImage (finiteObjectSupport C).ι).IsSerreClass
  infer_instance

omit [∀ i, Abelian (C i)] in
/-- Monotonicity of the nested stage condition. -/
theorem finiteFamilyStageObjectProperty_mono {s t : Finset I} (h : s ⊆ t) :
    finiteFamilyStageObjectProperty C s ≤ finiteFamilyStageObjectProperty C t :=
  fun _ hM => stageObjectProperty_mono C h _ hM

/-- Every zero object of the canonical family lies in every nested stage. -/
theorem finiteFamilyStageObjectProperty_zero (s : Finset I)
    {M : FiniteCategoryFamily C} (hM : IsZero M) : finiteFamilyStageObjectProperty C s M :=
  stageObjectProperty_of_isZero C s ((finiteObjectSupport C).ι.map_isZero hM)

/-- Nested stage transitions are the literal full-subcategory transitions. -/
def finiteFamilyStageInclusion {s t : Finset I} (h : s ⊆ t) :
    (finiteFamilyStageObjectProperty C s).FullSubcategory ⥤
      (finiteFamilyStageObjectProperty C t).FullSubcategory :=
  ObjectProperty.ιOfLE (finiteFamilyStageObjectProperty_mono C h)

instance finiteFamilyStageInclusion_additive {s t : Finset I} (h : s ⊆ t) :
    (finiteFamilyStageInclusion C h).Additive where
  map_add := by intros; rfl

/-- The literal nested-stage transition, bundled as an exact functor. -/
def finiteFamilyStageExactInclusion {s t : Finset I} (h : s ⊆ t) :
    ExactCategory.ExactFunctor
      (ExactCategory.abelianExactStructure (finiteFamilyStageObjectProperty C s).FullSubcategory)
      (ExactCategory.abelianExactStructure
        (finiteFamilyStageObjectProperty C t).FullSubcategory) where
  toFunctor := finiteFamilyStageInclusion C h
  map_conflation S hS := by
    apply (shortExact_fullSubcategory_iff (finiteFamilyStageObjectProperty C t) _).2
    exact (shortExact_fullSubcategory_iff (finiteFamilyStageObjectProperty C s) S).1 hS

/-- The two stage presentations retain exactly the same family and morphisms. -/
def stageNestedEquivalence (s : Finset I) :
    FiniteStage C s ≌ (finiteFamilyStageObjectProperty C s).FullSubcategory where
  functor :=
    { obj := fun M => ⟨(stageToFiniteFamily C s).obj M, M.property⟩
      map := fun f => ObjectProperty.homMk (ObjectProperty.homMk f.hom) }
  inverse :=
    { obj := fun M => ⟨M.obj.obj, M.property⟩
      map := fun f => ObjectProperty.homMk f.hom.hom }
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact Category.comp_id _

/-- Restrict the actual ambient family to the finite support set. -/
def stageRestriction (s : Finset I) : FiniteStage C s ⥤ (∀ i : s, C i.1) where
  obj M i := M.obj i.1
  map f i := f.hom i.1

instance stageRestriction_additive (s : Finset I) : (stageRestriction C s).Additive where
  map_add := by intros; rfl

/-- Restriction is exact for the standard abelian exact structures. -/
def stageExactRestriction (s : Finset I) :
    ExactCategory.ExactFunctor (stageExactStructure C s)
      (ExactCategory.abelianExactStructure (∀ i : s, C i.1)) where
  toFunctor := stageRestriction C s
  map_conflation S hS := by
    apply shortExact_pi_of
    intro i
    exact (stageEvaluation C s i.1).map_conflation S hS

/-- The coordinate functor used to extend a finite product by the chosen zero objects. -/
def zeroExtensionCoordinate (s : Finset I) (i : I) : (∀ j : s, C j.1) ⥤ C i := by
  classical
  exact if hi : i ∈ s then Pi.eval (fun j : s => C j.1) ⟨i, hi⟩
    else (Functor.const _).obj (0 : C i)

instance zeroExtensionCoordinate_additive (s : Finset I) (i : I) :
    (zeroExtensionCoordinate C s i).Additive := by
  classical
  unfold zeroExtensionCoordinate
  split
  · infer_instance
  · constructor
    simp

/-- Extend a family on `s` to the original ambient product by the chosen zero objects. -/
def zeroExtensionToProduct (s : Finset I) : (∀ j : s, C j.1) ⥤ (∀ i, C i) :=
  Functor.pi' (zeroExtensionCoordinate C s)

instance zeroExtensionToProduct_additive (s : Finset I) :
    (zeroExtensionToProduct C s).Additive where
  map_add := by
    intro X Y f g
    funext i
    exact (zeroExtensionCoordinate C s i).map_add

/-- A zero-extended family vanishes at every coordinate outside its indexing set. -/
theorem zeroExtensionToProduct_isZero (s : Finset I) (M : ∀ j : s, C j.1)
    (i : I) (hi : i ∉ s) : IsZero ((zeroExtensionToProduct C s).obj M i) := by
  classical
  change IsZero ((zeroExtensionCoordinate C s i).obj M)
  unfold zeroExtensionCoordinate
  rw [dite_eq_right hi]
  exact isZero_zero (C i)

/-- Zero extension lands in the original ambient full-subcategory stage. -/
def stageZeroExtension (s : Finset I) : (∀ j : s, C j.1) ⥤ FiniteStage C s :=
  (stageObjectProperty C s).lift (zeroExtensionToProduct C s)
    (fun M i hi => zeroExtensionToProduct_isZero C s M i hi)

instance stageZeroExtension_additive (s : Finset I) : (stageZeroExtension C s).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    funext i
    exact (zeroExtensionCoordinate C s i).map_add

/-- On a supported coordinate zero extension is the original evaluation functor. -/
def zeroExtensionEvaluationIso (s : Finset I) (i : I) (hi : i ∈ s) :
    stageZeroExtension C s ⋙ (stageEvaluation C s i).toFunctor ≅
      Pi.eval (fun j : s => C j.1) ⟨i, hi⟩ := by
  classical
  exact eqToIso (by
    change zeroExtensionCoordinate C s i = _
    simp [zeroExtensionCoordinate, hi])

/-- Off the support zero extension is the constant functor at the chosen zero object. -/
theorem zeroExtensionEvaluation_of_not_mem (s : Finset I) (i : I) (hi : i ∉ s) :
    stageZeroExtension C s ⋙ (stageEvaluation C s i).toFunctor =
      (Functor.const (∀ j : s, C j.1)).obj (0 : C i) := by
  classical
  change zeroExtensionCoordinate C s i = _
  simp [zeroExtensionCoordinate, hi]

/-- Off the support zero extension is canonically isomorphic to the chosen zero functor. -/
def zeroExtensionEvaluationZeroIso (s : Finset I) (i : I) (hi : i ∉ s) :
    stageZeroExtension C s ⋙ (stageEvaluation C s i).toFunctor ≅
      (0 : (∀ j : s, C j.1) ⥤ C i) :=
  NatIso.ofComponents
    (fun M => (zeroExtensionToProduct_isZero C s M i hi).iso (Functor.zero_obj M)) (by
      intro M N f
      exact (zeroExtensionToProduct_isZero C s M i hi).eq_of_src _ _)

/-- The unit component at one coordinate, retaining arbitrary zero objects off support. -/
def stageZeroExtensionUnitCoordinate (s : Finset I) (M : FiniteStage C s) (i : I) :
    M.obj i ≅ ((stageRestriction C s ⋙ stageZeroExtension C s).obj M).obj i := by
  classical
  exact if hi : i ∈ s then
    ((zeroExtensionEvaluationIso C s i hi).app ((stageRestriction C s).obj M)).symm
  else (M.property i hi).iso
    (zeroExtensionToProduct_isZero C s ((stageRestriction C s).obj M) i hi)

/-- The comparison from an arbitrary stage family to its zero extension after restriction. -/
def stageZeroExtensionUnitApp (s : Finset I) (M : FiniteStage C s) :
    M ≅ (stageRestriction C s ⋙ stageZeroExtension C s).obj M :=
  (stageObjectProperty C s).isoMk (Pi.isoMk (stageZeroExtensionUnitCoordinate C s M))

/-- The unit is identity on support and the unique zero-object isomorphism off support. -/
def stageZeroExtensionUnitIso (s : Finset I) :
    𝟭 (FiniteStage C s) ≅ stageRestriction C s ⋙ stageZeroExtension C s :=
  NatIso.ofComponents (stageZeroExtensionUnitApp C s) (by
    intro M N f
    apply ObjectProperty.hom_ext
    funext i
    classical
    by_cases hi : i ∈ s
    · change f.hom i ≫ (stageZeroExtensionUnitCoordinate C s N i).hom =
        (stageZeroExtensionUnitCoordinate C s M i).hom ≫
          ((stageZeroExtension C s).map ((stageRestriction C s).map f)).hom i
      simpa only [stageZeroExtensionUnitCoordinate, dite_eq_left hi, Iso.symm_hom, Iso.app_inv,
        stageRestriction, stageEvaluation, ExactCategory.ExactFunctor.comp,
        ObjectProperty.exactInclusion, exactEvaluation, Functor.comp_obj, Functor.comp_map,
        Pi.eval_obj, Pi.eval_map, ObjectProperty.ι_obj, ObjectProperty.ι_map] using
        (zeroExtensionEvaluationIso C s i hi).inv.naturality
          ((stageRestriction C s).map f)
    · exact (M.property i hi).eq_of_src _ _)

/-- Restriction after zero extension recovers the original finite-product family. -/
def stageZeroExtensionCounitIso (s : Finset I) :
    stageZeroExtension C s ⋙ stageRestriction C s ≅ 𝟭 (∀ j : s, C j.1) :=
  NatIso.pi' (fun j => zeroExtensionEvaluationIso C s j.1 j.2)

/-- Restriction and zero extension identify the actual stage with the finite product. -/
def stageProductEquivalence (s : Finset I) : FiniteStage C s ≌ (∀ j : s, C j.1) where
  functor := stageRestriction C s
  inverse := stageZeroExtension C s
  unitIso := stageZeroExtensionUnitIso C s
  counitIso := stageZeroExtensionCounitIso C s
  functor_unitIso_comp M := by
    funext j
    classical
    change (stageZeroExtensionUnitCoordinate C s M j.1).hom ≫
      ((zeroExtensionEvaluationIso C s j.1 j.2).app ((stageRestriction C s).obj M)).hom = _
    simp [stageZeroExtensionUnitCoordinate, j.property]

/-- Zero extension is exact for the standard abelian exact structures. -/
def stageExactZeroExtension (s : Finset I) :
    ExactCategory.ExactFunctor (ExactCategory.abelianExactStructure (∀ j : s, C j.1))
      (stageExactStructure C s) where
  toFunctor := stageZeroExtension C s
  map_conflation _ hS := by
    let : (stageZeroExtension C s).IsEquivalence :=
      (stageProductEquivalence C s).isEquivalence_inverse
    exact hS.map_of_exact (stageZeroExtension C s)

@[simp]
theorem stageRestriction_comp_evaluation (s : Finset I) (j : s) :
    stageRestriction C s ⋙ Pi.eval (fun j : s => C j.1) j =
      (stageEvaluation C s j.1).toFunctor := rfl

omit [∀ i, Abelian (C i)] in
/-- Finite-product restriction commutes literally with the ambient stage inclusion. -/
theorem stageInclusion_comp_restriction {s t : Finset I} (h : s ⊆ t) :
    stageInclusion C h ⋙ stageRestriction C t ⋙
        Pi.comap (fun j : t => C j.1) (fun j : s => (⟨j.1, h j.2⟩ : t)) =
      stageRestriction C s := rfl

/-- A coordinate object regarded as the family indexed by its singleton. -/
def singletonProductInsertion (i : I) : C i ⥤ (∀ j : ({i} : Finset I), C j.1) :=
  Functor.pi' (fun j =>
    (Pi.eqToEquivalence C (Finset.mem_singleton.mp j.property).symm).functor)

private theorem eqToEquivalenceFunctor_additive {i j : I} (h : i = j) :
    (Pi.eqToEquivalence C h).functor.Additive := by
  subst h
  change (𝟭 (C i)).Additive
  infer_instance

instance singletonProductInsertion_additive (i : I) :
    (singletonProductInsertion C i).Additive where
  map_add := by
    intro X Y f g
    funext j
    have h : i = j.1 := (Finset.mem_singleton.mp j.property).symm
    let := eqToEquivalenceFunctor_additive C h
    exact (Pi.eqToEquivalence C h).functor.map_add

/-- The singleton product family is exact. -/
def singletonProductExactInsertion (i : I) :
    ExactCategory.ExactFunctor (ExactCategory.abelianExactStructure (C i))
      (ExactCategory.abelianExactStructure (∀ j : ({i} : Finset I), C j.1)) where
  toFunctor := singletonProductInsertion C i
  map_conflation S hS := by
    apply shortExact_pi_of
    intro j
    have h : i = j.1 := (Finset.mem_singleton.mp j.property).symm
    let e := Pi.eqToEquivalence C h
    have : e.functor.Additive := eqToEquivalenceFunctor_additive C h
    exact hS.map_of_exact e.functor

/-- Insert one coordinate into the canonical finite-support family by singleton zero extension. -/
def singletonInclusion (i : I) : C i ⥤ FiniteCategoryFamily C :=
  singletonProductInsertion C i ⋙ stageZeroExtension C {i} ⋙ stageToFiniteFamily C {i}

instance singletonInclusion_additive (i : I) : (singletonInclusion C i).Additive := by
  dsimp [singletonInclusion]
  infer_instance

/-- Singleton insertion is exact for the standard abelian exact structures. -/
def singletonExactInclusion (i : I) : ExactCategory.ExactFunctor
    (ExactCategory.abelianExactStructure (C i)) (finiteCategoryExactStructure C) :=
  (singletonProductExactInsertion C i).comp
    ((stageExactZeroExtension C {i}).comp (stageExactToFiniteFamily C {i}))

@[simp]
theorem singletonExactInclusion_toFunctor (i : I) :
    (singletonExactInclusion C i).toFunctor = singletonInclusion C i := rfl

/-- The coordinate used for singleton insertion is recovered by its original evaluation. -/
theorem singletonInclusion_comp_evaluation (i : I) :
    singletonInclusion C i ⋙ (finiteCategoryEvaluation C i).toFunctor = 𝟭 (C i) := by
  classical
  change singletonProductInsertion C i ⋙ zeroExtensionCoordinate C {i} i = _
  simp [zeroExtensionCoordinate, singletonProductInsertion, Pi.eqToEquivalence]

/-- Away from the inserted coordinate the actual functor is constant at the chosen zero object. -/
theorem singletonInclusion_comp_evaluation_zero (i j : I) (h : j ≠ i) :
    singletonInclusion C i ⋙ (finiteCategoryEvaluation C j).toFunctor =
      (Functor.const (C i)).obj (0 : C j) := by
  classical
  change singletonProductInsertion C i ⋙ zeroExtensionCoordinate C {i} j = _
  have hj : j ∉ ({i} : Finset I) := by simpa using h
  simp only [zeroExtensionCoordinate, dite_eq_right hj]
  rfl

/-- Every other coordinate of a singleton insertion is a zero object. -/
theorem singletonInclusion_obj_isZero (i j : I) (h : j ≠ i) (X : C i) :
    IsZero (((singletonInclusion C i).obj X).obj j) := by
  classical
  exact zeroExtensionToProduct_isZero C {i} ((singletonProductInsertion C i).obj X) j
    (by simpa using h)

/-- Every other evaluation of singleton insertion is canonically a zero functor. -/
def singletonInclusionCompEvaluationOfNe (i j : I) (h : j ≠ i) :
    singletonInclusion C i ⋙ (finiteCategoryEvaluation C j).toFunctor ≅
      (0 : C i ⥤ C j) :=
  NatIso.ofComponents
    (fun X => (singletonInclusion_obj_isZero C i j h X).iso (Functor.zero_obj X)) (by
      intro X Y f
      exact (singletonInclusion_obj_isZero C i j h X).eq_of_src _ _)

/-- Every object of the empty stage is a zero object, including its arbitrary chosen objects. -/
theorem emptyStage_isZero (M : FiniteStage C ∅) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).2
  apply ObjectProperty.hom_ext
  funext i
  exact (M.property i (by simp)).eq_of_src _ _

/-- The empty stage is equivalent to the one-object zero category. -/
def emptyStageEquivalence : FiniteStage C ∅ ≌ Discrete PUnit where
  functor := Functor.star _
  inverse := (Functor.const _).obj (0 : FiniteStage C ∅)
  unitIso := NatIso.ofComponents
    (fun M => (emptyStage_isZero C M).iso (isZero_zero _)) (by
      intro M N f
      exact (emptyStage_isZero C M).eq_of_src _ _)
  counitIso := NatIso.ofComponents (fun _ => eqToIso (Subsingleton.elim _ _)) (by
    intro X Y f
    apply Subsingleton.elim)
  functor_unitIso_comp M := Subsingleton.elim _ _

instance stageNestedEquivalence_functor_additive (s : Finset I) :
    (stageNestedEquivalence C s).functor.Additive where
  map_add := by intros; rfl

/-- The nested-stage equivalence sends the original family by an exact functor. -/
def stageNestedExactFunctor (s : Finset I) : ExactCategory.ExactFunctor
    (stageExactStructure C s)
    (ExactCategory.abelianExactStructure
      (finiteFamilyStageObjectProperty C s).FullSubcategory) where
  toFunctor := (stageNestedEquivalence C s).functor
  map_conflation S hS := by
    apply (shortExact_fullSubcategory_iff (finiteFamilyStageObjectProperty C s) _).2
    exact (stageExactToFiniteFamily C s).map_conflation S hS

/-- The inverse nested-stage comparison is exact and retains the original ambient family. -/
def stageNestedInverseExactFunctor (s : Finset I) : ExactCategory.ExactFunctor
    (ExactCategory.abelianExactStructure (finiteFamilyStageObjectProperty C s).FullSubcategory)
    (stageExactStructure C s) where
  toFunctor := (stageNestedEquivalence C s).inverse
  map_conflation S hS := by
    apply (shortExact_stage_iff C s _).2
    exact (finiteCategoryInclusion C).map_conflation _
      ((ObjectProperty.exactInclusion (finiteFamilyStageObjectProperty C s)).map_conflation S hS)

omit [∀ i, Abelian (C i)] in
@[simp]
theorem stageNestedEquivalence_comp_inclusion (s : Finset I) :
    (stageNestedEquivalence C s).functor ⋙ (finiteFamilyStageObjectProperty C s).ι =
      stageToFiniteFamily C s := rfl

omit [∀ i, Abelian (C i)] in
@[simp]
theorem stageNestedEquivalence_naturality {s t : Finset I} (h : s ⊆ t) :
    stageInclusion C h ⋙ (stageNestedEquivalence C t).functor =
      (stageNestedEquivalence C s).functor ⋙ finiteFamilyStageInclusion C h := rfl

omit [∀ i, Abelian (C i)] in
@[simp]
theorem finiteFamilyStageInclusion_refl (s : Finset I) :
    finiteFamilyStageInclusion C (s := s) le_rfl = 𝟭 _ := rfl

omit [∀ i, Abelian (C i)] in
@[simp]
theorem finiteFamilyStageInclusion_comp {r s t : Finset I} (h : r ⊆ s) (h' : s ⊆ t) :
    finiteFamilyStageInclusion C h ⋙ finiteFamilyStageInclusion C h' =
      finiteFamilyStageInclusion C (h.trans h') := rfl

omit [∀ i, Abelian (C i)] in
/-- The literal stage inclusion is injective on objects. -/
theorem stageToFiniteFamily_obj_injective (s : Finset I) :
    Function.Injective (stageToFiniteFamily C s).obj := by
  intro M N h
  apply ObjectProperty.FullSubcategory.ext
  exact congrArg (fun X : FiniteCategoryFamily C => X.obj) h

end CategoryTheory.Pi
