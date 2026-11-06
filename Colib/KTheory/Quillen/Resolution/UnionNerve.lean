/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.KTheory.Quillen.Resolution.Bounded
public import Colib.Topology.FilteredRealization.NerveMonomorphism
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# The actual filtered union of resolution-length Q-categories

The indexing category is the natural numbers. Every ambient Q-arrow lifts to
one finite stratum by bounding the resolutions of its source, target, apex,
left kernel, and right cokernel. Thus no uniform resolution bound is assumed.
This leaf stops at the actual nerve colimit, before filtered realization invariance.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Simplicial

namespace CategoryTheory.ExactCategory.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [E.IsKernelClosed P] [P.IsClosedUnderFiniteProducts]
  [h : Fact (E.ResolutionHypothesis P)]

/-- Universe-compatible natural-number index for the resolution strata. -/
abbrev StratumIndex := AsSmall.{u} ℕ

/-- The finite resolution length indexing this stage. -/
abbrev stratumRank (j : StratumIndex.{u}) : ℕ := AsSmall.down.obj j

/-- A natural number viewed as an index. -/
abbrev stratumIndex (n : ℕ) : StratumIndex.{u} := AsSmall.up.obj n

/-- The strict diagram of the actual inherited Q-categories. -/
@[implicit_reducible]
def stratumQDiagram : StratumIndex.{u} ⥤ Cat.{u,u} where
  obj j := Cat.of (stratumExactStructure E P (stratumRank j)).QCategory
  map f := (stratumTransition E P (leOfHom (AsSmall.down.map f))).mapQ.toCatHom
  map_id j := by
    apply Cat.Hom.ext
    change (CategoryTheory.ExactCategory.ExactFunctor.id (stratumExactStructure E P (stratumRank
      j))).mapQ = 𝟭 _
    exact CategoryTheory.ExactCategory.ExactFunctor.mapQ_id _
  map_comp f g := by
    apply Cat.Hom.ext
    exact CategoryTheory.ExactCategory.ExactFunctor.mapQ_comp
      (stratumTransition E P (leOfHom (AsSmall.down.map f)))
      (stratumTransition E P (leOfHom (AsSmall.down.map g)))

/-- The canonical ambient inclusions assemble to a strict categorical cocone. -/
@[implicit_reducible]
def stratumQCocone : Cocone (stratumQDiagram E P) where
  pt := Cat.of E.QCategory
  ι :=
    { app j := (exactInclusion E (E.ResolutionLength P (stratumRank j))).mapQ.toCatHom
      naturality {j k} f := by
        apply Cat.Hom.ext
        change (stratumTransition E P (leOfHom (AsSmall.down.map f))).mapQ ⋙
          (exactInclusion E (E.ResolutionLength P (stratumRank k))).mapQ =
            (exactInclusion E (E.ResolutionLength P (stratumRank j))).mapQ
        rw [← CategoryTheory.ExactCategory.ExactFunctor.mapQ_comp, exactInclusionOfLE_comp] }

omit [P.IsClosedUnderFiniteProducts] in
/-- A whole ambient Q-arrow, including its kernel and cokernel witnesses,
lifts to one genuine exact length stratum. -/
theorem stratumQCocone_arrowSurjective :
    FilteredNerveColimit.ArrowSurjective (stratumQDiagram E P) (stratumQCocone E P) := by
  rintro ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ ⟨s⟩
  change Span E.deflation E.inflation X Y at s
  obtain ⟨K, i, hi, hK⟩ := s.wl
  obtain ⟨Z, p, hp, hZ⟩ := s.wr
  obtain ⟨RX⟩ := h.out X
  obtain ⟨RY⟩ := h.out Y
  obtain ⟨RA⟩ := h.out s.apex
  obtain ⟨RK⟩ := h.out K
  obtain ⟨RZ⟩ := h.out Z
  let N := max RX.length (max RY.length (max RA.length (max RK.length RZ.length)))
  have hX : E.ResolutionLength P N X := ⟨RX, by dsimp [N]; omega⟩
  have hY : E.ResolutionLength P N Y := ⟨RY, by dsimp [N]; omega⟩
  have hA : E.ResolutionLength P N s.apex := ⟨RA, by dsimp [N]; omega⟩
  have hK' : E.ResolutionLength P N K := ⟨RK, by dsimp [N]; omega⟩
  have hZ' : E.ResolutionLength P N Z := ⟨RZ, by dsimp [N]; omega⟩
  let x : (E.ResolutionLength P N).FullSubcategory := ⟨X, hX⟩
  let y : (E.ResolutionLength P N).FullSubcategory := ⟨Y, hY⟩
  let a : (E.ResolutionLength P N).FullSubcategory := ⟨s.apex, hA⟩
  let t : Span (stratumExactStructure E P N).deflation
      (stratumExactStructure E P N).inflation x y
    :=
    { apex := a
      l := ObjectProperty.homMk s.l
      r := ObjectProperty.homMk s.r
      wl := (ExactSubcategory.deflation_iff E (E.ResolutionLength P N) _).2
        ⟨K, hK', i, hi, hK⟩
      wr := (ExactSubcategory.inflation_iff E (E.ResolutionLength P N) _).2
        ⟨Z, hZ', p, hp, hZ⟩ }
  refine ⟨stratumIndex N, QConstruction.of _ _ x, QConstruction.of _ _ y,
    QConstruction.mkHom _ _ t, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl

omit [P.IsClosedUnderFiniteProducts] in
/-- Objects lift in particular by lifting their identity arrows. -/
theorem stratumQCocone_objectSurjective :
    ∀ X : (stratumQCocone E P).pt, ∃ j, ∃ x : (stratumQDiagram E P).obj j,
      ((stratumQCocone E P).ι.app j).toFunctor.obj x = X := by
  intro X
  obtain ⟨j, x, _, _, hx, _, _⟩ := stratumQCocone_arrowSurjective E P (𝟙 X)
  exact ⟨j, x, hx⟩

omit [P.IsClosedUnderFiniteProducts] in
/-- The stage inclusions already reflect equality of objects; no further
increase of the resolution bound is necessary. -/
theorem stratumQCocone_eventuallyEqualObjects :
    FilteredNerveColimit.EventuallyEqualObjects (stratumQDiagram E P) (stratumQCocone E P) := by
  intro j X Y hXY
  have hobj : X = Y := by
    rcases X with ⟨⟨X⟩⟩
    rcases Y with ⟨⟨Y⟩⟩
    have he := congrArg (fun T => T.obj.of) hXY
    change X.obj = Y.obj at he
    have he' : X = Y := ObjectProperty.FullSubcategory.ext he
    cases he'
    rfl
  exact ⟨j, 𝟙 j, congrArg ((stratumQDiagram E P).map (𝟙 j)).toFunctor.obj hobj⟩

instance stratumQCocone_faithful (j : StratumIndex.{u}) :
    (FilteredNerveColimit.leg (stratumQDiagram E P) (stratumQCocone E P) j).Faithful := by
  let : (exactInclusion E (E.ResolutionLength P (stratumRank j))).toFunctor.Full :=
    inferInstanceAs (E.ResolutionLength P (stratumRank j)).ι.Full
  let : (exactInclusion E (E.ResolutionLength P (stratumRank j))).toFunctor.Faithful :=
    inferInstanceAs (E.ResolutionLength P (stratumRank j)).ι.Faithful
  exact (exactInclusion E (E.ResolutionLength P (stratumRank j))).mapQ_faithful_of_fullyFaithful

/-- The ambient Q-nerve really is the filtered simplicial colimit of the
finite-resolution-length strata. -/
def stratumNerveCoconeIsColimit :
    IsColimit (nerveFunctor.mapCocone (stratumQCocone E P)) :=
  FilteredNerveColimit.nerveCoconeIsColimit (stratumQDiagram E P) (stratumQCocone E P)
    (stratumQCocone_objectSurjective E P) (stratumQCocone_arrowSurjective E P)
    (stratumQCocone_eventuallyEqualObjects E P)

/-- The genuine length-stratum Q transition is injective on objects and faithful,
so its actual nerve map is a monomorphism. -/
instance stratumTransition_nerveMap_mono {m n : ℕ} (hmn : m ≤ n) :
    Mono (nerveMap (stratumTransition E P hmn).mapQ) := by
  let F := stratumTransition E P hmn
  let : F.toFunctor.Full := inferInstanceAs
    (ObjectProperty.ιOfLE (E.resolutionLength_mono P hmn)).Full
  let : F.toFunctor.Faithful := inferInstanceAs
    (ObjectProperty.ιOfLE (E.resolutionLength_mono P hmn)).Faithful
  let : F.mapQ.Faithful := F.mapQ_faithful_of_fullyFaithful
  apply nerveMap_mono_of_injective_obj F.mapQ
  rintro ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ hXY
  have he : X.obj = Y.obj := congrArg (fun T => T.obj.of.obj) hXY
  have he' : X = Y := ObjectProperty.FullSubcategory.ext he
  cases he'
  rfl

end CategoryTheory.ExactCategory.Resolution

attribute [colib_tag "COL-0238",
  colib_ref "WeibelKBook" "V, proof of Theorem 3.1, page 20" "background"
    "Filtered nerves and sequential resolution unions"]
  CategoryTheory.ExactCategory.Resolution.stratumNerveCoconeIsColimit
