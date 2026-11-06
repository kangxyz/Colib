/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Abelian.Subcategory.Exact
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.QFaithful

/-!
# Full faithfulness of the Q-inclusion in dévissage

A Q-arrow between objects of the smaller category is represented by an
admissible span whose apex is a subobject of its target. Subobject closure
therefore puts the apex in the smaller category. The span lifts, and its
isomorphisms lift through the fully faithful ordinary inclusion.

Consequently the dévissage Q-functor is fully faithful. This statement does
not require the finite-filtration hypothesis and does not assert essential
surjectivity of the Q-functor or the homotopical dévissage theorem.
-/
/-!
Implementation provenance: adapted from
`Quillen/Devissage/FullyFaithful.lean` and the Q-inclusion declarations from
`Quillen/Devissage/Setup.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Native Mathlib full subcategories, Colib exact structures,
restricted spans, actual realization maps and their universes are retained.
No extension-closure, uniform filtration bound, alternate K-model or Aglib import is added.
-/

@[expose] public section

open CategoryTheory.ExactCategory
open CategoryTheory.ObjectProperty


noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Devissage

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]
  [P.IsClosedUnderFiniteProducts]

/-- The Q-functor induced by the exact inclusion in classical dévissage. -/
def mapQ :
    QConstruction (abelianExactStructure P.FullSubcategory).deflation
      (abelianExactStructure P.FullSubcategory).inflation ⥤
      QConstruction (abelianExactStructure C).deflation (abelianExactStructure C).inflation :=
  (exactInclusion P).mapQ

@[simp]
lemma mapQ_obj_of (X : P.FullSubcategory) :
    (mapQ P).obj
      (QConstruction.of (abelianExactStructure P.FullSubcategory).deflation
        (abelianExactStructure P.FullSubcategory).inflation X) =
    QConstruction.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X.obj := rfl

omit [P.ContainsZero] [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts] in
/-- An ambient admissible span ending in an object satisfying `P` has its apex
in `P`, by the admissible monomorphism on the right. -/
lemma span_apex_mem {X Y : P.FullSubcategory}
    (s : Span (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X.obj Y.obj) : P s.apex := by
  have : Mono s.r := (abelianExactStructure_inflation_iff C s.r).1 s.wr
  exact P.prop_of_mono s.r Y.property

/-- Lift an actual ambient Q-span between objects of the full subcategory.
The same maps are admissible in the subcategory because the faithful
inclusion reflects monomorphisms and epimorphisms. -/
def liftSpan {X Y : P.FullSubcategory}
    (s : Span (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X.obj Y.obj) :
    Span (abelianExactStructure P.FullSubcategory).deflation
      (abelianExactStructure P.FullSubcategory).inflation X Y where
  apex := ⟨s.apex, span_apex_mem P s⟩
  l := P.homMk s.l
  r := P.homMk s.r
  wl := (abelianExactStructure_deflation_iff P.FullSubcategory _).2
    (P.ι.epi_of_epi_map ((abelianExactStructure_deflation_iff C s.l).1 s.wl))
  wr := (abelianExactStructure_inflation_iff P.FullSubcategory _).2
    (P.ι.mono_of_mono_map ((abelianExactStructure_inflation_iff C s.r).1 s.wr))

/-- Mapping the lifted span recovers its original ambient representative. -/
@[simp]
lemma mapSpan_liftSpan {X Y : P.FullSubcategory}
    (s : Span (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X.obj Y.obj) :
    (exactInclusion P).toQCompatibleFunctor.mapSpan (liftSpan P s) = s := rfl

/-- Every ambient Q-morphism between objects in the smaller category lifts to
a Q-morphism there. -/
instance mapQ_full : (mapQ P).Full where
  map_surjective := by
    rintro X Y ⟨s⟩
    refine ⟨QConstruction.mkHom _ _ (liftSpan P s), ?_⟩
    rfl

/-- Equality of ambient Q-morphisms is reflected: the commuting apex
isomorphism lifts to an isomorphism in the full subcategory. -/
instance mapQ_faithful : (mapQ P).Faithful := by
  let : (exactInclusion P).toFunctor.Full := by
    change P.ι.Full
    infer_instance
  let : (exactInclusion P).toFunctor.Faithful := by
    change P.ι.Faithful
    infer_instance
  exact (exactInclusion P).mapQ_faithful_of_fullyFaithful

/-- The genuine dévissage Q-inclusion is fully faithful, with inverse maps on
hom-sets supplied by lifting admissible spans. -/
def mapQFullyFaithful : (mapQ P).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (mapQ P)

/-- The resulting equivalence of Q-hom sets. -/
def mapQHomEquiv
    (X Y : QConstruction (abelianExactStructure P.FullSubcategory).deflation
      (abelianExactStructure P.FullSubcategory).inflation) :
    (X ⟶ Y) ≃ ((mapQ P).obj X ⟶ (mapQ P).obj Y) :=
  (mapQFullyFaithful P).homEquiv

end CategoryTheory.Abelian.Devissage
