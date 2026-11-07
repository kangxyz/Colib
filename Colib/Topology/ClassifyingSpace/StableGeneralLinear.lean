/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.GroupTheory.StableGeneralLinear.Basic
public import Colib.Topology.ClassifyingSpace.Map
public import Colib.Topology.ClassifyingSpace.AsSmall
public import Colib.Topology.FilteredRealization.NerveColimit
public import Colib.Topology.FilteredRealization.Compact

/-!
# Finite-rank classifying spaces of the stable general linear group

The actual one-object group categories form a directed system under matrix
stabilization. Their nerves have the stable group's nerve as a genuine
simplicial colimit. Common-universe models use the existing strictly inverse
`AsSmall` nerve isomorphisms, so coefficient rings may live in any universe.

No finite-stage homotopy equivalence, plus construction, or QConstruction-comparison is
asserted here.

Implementation provenance: `Quillen/Topology/ClassifyingSpace/StableGeneralLinear.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial Topology

namespace StableGeneralLinear

variable (R : Type u) [Ring R]

/-- A universe-compatible natural-number category indexing matrix ranks. -/
abbrev RankIndex := AsSmall.{u} ℕ

/-- The ordinary rank represented by a lifted index. -/
abbrev rank (j : RankIndex.{u}) : ℕ := AsSmall.down.obj j

/-- A natural number as a universe-compatible diagram index. -/
abbrev rankIndex (n : ℕ) : RankIndex.{u} := AsSmall.up.obj n

/-- The common-universe one-object category of a finite matrix group. -/
abbrev finiteCategory (n : ℕ) := AsSmall.{0} (SingleObj (Matrix.GeneralLinearGroup (Fin n) R))

/-- The common-universe one-object category of the actual stable group. -/
abbrev stableCategory := AsSmall.{0} (SingleObj (Group R))

/-- A group homomorphism viewed in the common-universe one-object models. -/
def smallFunctor {G H : Type u} [_root_.Group G] [_root_.Group H] (f : G →* H) :
    AsSmall.{0} (SingleObj G) ⥤ AsSmall.{0} (SingleObj H) :=
  AsSmall.down ⋙ f.toFunctor ⋙ AsSmall.up

/-- The strict categorical diagram of finite general linear groups. -/
@[implicit_reducible]
def categoryDiagram : RankIndex.{u} ⥤ Cat.{u, u} where
  obj j := Cat.of (finiteCategory R (rank j))
  map f := (smallFunctor (transition R _ _ (leOfHom (AsSmall.down.map f)))).toCatHom
  map_id j := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun X => by rcases X with ⟨⟨⟩⟩; rfl) ?_
    intro X Y f
    rcases X with ⟨⟨⟩⟩
    rcases Y with ⟨⟨⟩⟩
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact congrArg ULift.up (transition_self R _ f.down)
  map_comp f g := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun X => by rcases X with ⟨⟨⟩⟩; rfl) ?_
    intro X Y a
    rcases X with ⟨⟨⟩⟩
    rcases Y with ⟨⟨⟩⟩
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact congrArg ULift.up (transition_trans R _ _ a.down).symm

/-- Finite-stage inclusions into the stable group form a strict cocone. -/
@[implicit_reducible]
def categoryCocone : Cocone (categoryDiagram R) where
  pt := Cat.of (stableCategory R)
  ι :=
    { app j := (smallFunctor (of R (rank j))).toCatHom
      naturality {j k} f := by
        apply Cat.Hom.ext
        refine CategoryTheory.Functor.ext (fun X => by rcases X with ⟨⟨⟩⟩; rfl) ?_
        intro X Y a
        rcases X with ⟨⟨⟩⟩
        rcases Y with ⟨⟨⟩⟩
        simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
        exact congrArg ULift.up (of_transition R _ a.down) }

/-- Every categorical leg is faithful because finite-stage inclusions are injective. -/
instance categoryCocone_faithful (j : RankIndex.{u}) :
    (FilteredNerveColimit.leg (categoryDiagram R) (categoryCocone R) j).Faithful where
  map_injective h := by
    apply ULift.ext
    exact of_injective R (rank j) (congrArg ULift.down h)

/-- Every arrow of the stable group comes from a finite rank. -/
lemma categoryCocone_arrowSurjective :
    FilteredNerveColimit.ArrowSurjective (categoryDiagram R) (categoryCocone R) := by
  intro X Y g
  obtain ⟨n, a, ha⟩ := exists_of R g.down
  refine ⟨rankIndex n, AsSmall.up.obj (SingleObj.star _),
    AsSmall.up.obj (SingleObj.star _), ULift.up a, (by rcases X with ⟨⟨⟩⟩; rfl),
    (by rcases Y with ⟨⟨⟩⟩; rfl), ?_⟩
  rcases X with ⟨⟨⟩⟩
  rcases Y with ⟨⟨⟩⟩
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact congrArg ULift.up ha.symm

/-- There is only one object at every stage, so object equality needs no refinement. -/
lemma categoryCocone_eventuallyEqualObjects :
    FilteredNerveColimit.EventuallyEqualObjects (categoryDiagram R) (categoryCocone R) := by
  intro j X Y _
  refine ⟨j, 𝟙 j, ?_⟩
  rcases X with ⟨⟨⟩⟩
  rcases Y with ⟨⟨⟩⟩
  rfl

/-- The finite-rank group nerves have the actual stable group nerve as their colimit. -/
def nerveCoconeIsColimit : IsColimit (nerveFunctor.mapCocone (categoryCocone R)) :=
  FilteredNerveColimit.nerveCoconeIsColimit (categoryDiagram R) (categoryCocone R)
    (fun X => ⟨rankIndex 0, AsSmall.up.obj (SingleObj.star _), by
      rcases X with ⟨⟨⟩⟩
      rfl⟩)
    (categoryCocone_arrowSurjective R) (categoryCocone_eventuallyEqualObjects R)

/-- Every compact-source map into the stable classifying space has a finite-rank lift. -/
lemma compact_factors {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, ClassifyingSpace (stableCategory R))) :
    ∃ n, ∃ g : C(T, ClassifyingSpace (finiteCategory R n)),
      (classifyingSpaceMap (smallFunctor (of R n))).hom.comp g = f := by
  obtain ⟨j, g, hg⟩ := FilteredRealization.compact_factors
    (categoryDiagram R ⋙ nerveFunctor) (nerveFunctor.mapCocone (categoryCocone R))
    (nerveCoconeIsColimit R) f
  exact ⟨rank j, g, hg⟩

/-- Common-universe replacement commutes with the original classifying-space maps. -/
lemma smallFunctor_classifying_naturality {G H : Type u}
    [_root_.Group G] [_root_.Group H] (f : G →* H)
    (x : ClassifyingSpace (SingleObj G)) :
    classifyingSpaceMap (smallFunctor f)
        (CategoryTheory.asSmallClassifyingHomeomorph (SingleObj G) x) =
      CategoryTheory.asSmallClassifyingHomeomorph (SingleObj H)
        (classifyingSpaceMap f.toFunctor x) := by
  have h : (CategoryTheory.asSmallNerveIso (SingleObj G)).hom ≫
      nerveMap (smallFunctor f) = nerveMap f.toFunctor ≫
        (CategoryTheory.asSmallNerveIso (SingleObj H)).hom := by
    ext n a
    rfl
  have h' := congrArg (fun a => SSet.toTop.map a x) h
  simpa only [Functor.map_comp, TopCat.comp_app, classifyingSpaceMap,
    CategoryTheory.asSmallClassifyingHomeomorph, TopCat.homeoOfIso_apply,
    Functor.mapIso_hom, ClassifyingSpace] using h'

/-- The original finite-rank inclusion on genuine classifying spaces. -/
def stageMap (n : ℕ) : ClassifyingSpace (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)) ⟶
    ClassifyingSpace (SingleObj (Group R)) :=
  classifyingSpaceMap (of R n).toFunctor

@[simp] lemma stageMap_point (n : ℕ) :
    stageMap R n (classifyingSpacePoint (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R))) =
      classifyingSpacePoint (SingleObj.star (Group R)) :=
  classifyingSpaceMap_point (of R n).toFunctor _

/-- The original finite-rank classifying maps commute with stabilization. -/
lemma stageMap_transition {n m : ℕ} (h : n ≤ m) :
    classifyingSpaceMap (transition R n m h).toFunctor ≫ stageMap R m = stageMap R n := by
  have he : (of R m).comp (transition R n m h) = of R n := by
    ext g
    exact of_transition R h g
  simpa only [MonoidHom.comp_toFunctor, classifyingSpaceMap_comp, stageMap] using
    congrArg (fun f => classifyingSpaceMap f.toFunctor) he

/-- Entrywise change of coefficient rings commutes with finite-rank classifying inclusions. -/
lemma stageMap_ringMap {S : Type u} [Ring S] (f : R →+* S) (n : ℕ) :
    classifyingSpaceMap (finiteMap f n).toFunctor ≫ stageMap S n =
      stageMap R n ≫ classifyingSpaceMap (map f).toFunctor := by
  have he : (of S n).comp (finiteMap f n) = (map f).comp (of R n) := by
    ext g
    exact (map_of f n g).symm
  simpa only [MonoidHom.comp_toFunctor, classifyingSpaceMap_comp, stageMap] using
    congrArg (fun f => classifyingSpaceMap f.toFunctor) he

/-- Compact maps into the original stable group nerve realization lift at finite rank. -/
lemma compact_factors_original {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, ClassifyingSpace (SingleObj (Group R)))) :
    ∃ n, ∃ g : C(T, ClassifyingSpace (SingleObj (Matrix.GeneralLinearGroup (Fin n) R))),
      (stageMap R n).hom.comp g = f := by
  let e := CategoryTheory.asSmallClassifyingHomeomorph (SingleObj (Group R))
  obtain ⟨n, g, hg⟩ := compact_factors R ((⟨e, e.continuous⟩ : C(_, _)).comp f)
  let d := CategoryTheory.asSmallClassifyingHomeomorph
    (SingleObj (Matrix.GeneralLinearGroup (Fin n) R))
  refine ⟨n, (⟨d.symm, d.symm.continuous⟩ : C(_, _)).comp g, ?_⟩
  ext t
  apply e.injective
  change e (classifyingSpaceMap (of R n).toFunctor (d.symm (g t))) = e (f t)
  rw [← smallFunctor_classifying_naturality]
  change classifyingSpaceMap (smallFunctor (of R n)) (d (d.symm (g t))) = e (f t)
  rw [d.apply_symm_apply]
  exact ContinuousMap.congr_fun hg t

end StableGeneralLinear
