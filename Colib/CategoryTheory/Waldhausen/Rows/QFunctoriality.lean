/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.QConstruction
public import Colib.CategoryTheory.Waldhausen.Rows.NervePresentation
public import Colib.CategoryTheory.ExactCategory.QSpanNaturality
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Q comparison on the original pointwise weak row maps

For an exact category every original weak component is an isomorphism.
These isomorphisms give the Q-valued interval comparison directly on
`QuotientRows.WeakRows`. Ordinal restriction retains the same maps and spans.

Adapted from `Quillen/Waldhausen/QuillenComparison/RowGroupoid.lean` and
`Reindexing.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The separate source `Row` type is not introduced.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod
universe v u
namespace CategoryTheory.Waldhausen.QuotientRows

/-- Increasing ordinal maps preserve containment of intervals. -/
def nestedIntervalMap {m n : SimplexCategory} (α : m ⟶ n) :
    NestedInterval m ⥤ NestedInterval n where
  obj p := ⟨(OrderDual.toDual (α.toOrderHom p.left), α.toOrderHom p.right),
    α.toOrderHom.monotone p.endpoints⟩
  map f := homOfLE ⟨α.toOrderHom.monotone (NestedInterval.left_anti (leOfHom f)),
    α.toOrderHom.monotone (NestedInterval.right_mono (leOfHom f))⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactCategory.ExactStructure C)
variable {n : SimplexCategory}

/-- The original weak natural transformation is an actual natural isomorphism. -/
def weakRowIso {F G : WeakRows (ofExactCategory E) n} (η : F ⟶ G) :
    F.obj.obj ≅ G.obj.obj :=
  NatIso.ofComponents (fun p ↦ by
    letI : IsIso (η.hom.hom.app p) := η.property p
    exact asIso (η.hom.hom.app p)) (fun {_ _} f ↦ η.hom.hom.naturality f)

@[simp] theorem weakRowIso_hom_app {F G : WeakRows (ofExactCategory E) n}
    (η : F ⟶ G) (p : Interval n) : (weakRowIso E η).hom.app p = η.hom.hom.app p := rfl

@[simp] theorem weakRowIso_id (F : WeakRows (ofExactCategory E) n) :
    weakRowIso E (𝟙 F) = Iso.refl F.obj.obj := by
  apply Iso.ext
  rfl

@[simp] theorem weakRowIso_comp {F G H : WeakRows (ofExactCategory E) n}
    (η : F ⟶ G) (θ : G ⟶ H) :
    weakRowIso E (η ≫ θ) = weakRowIso E η ≪≫ weakRowIso E θ := by
  apply Iso.ext
  rfl

/-- Original weak row maps induce the canonical componentwise Q-isomorphisms. -/
def intervalQFunctorIso {F G : WeakRows (ofExactCategory E) n} (η : F ⟶ G) :
    intervalQFunctor E F.obj ≅ intervalQFunctor E G.obj :=
  NatIso.ofComponents
    (fun p ↦ E.qIsoOfIso ((weakRowIso E η).app (interval p.left p.right p.endpoints))) (by
      intro p q f
      apply E.qSpan_iso_naturality
        (intervalSpan E F.obj (leOfHom f)) (intervalSpan E G.obj (leOfHom f))
        ((weakRowIso E η).app (interval p.left p.right p.endpoints))
        ((weakRowIso E η).app (interval q.left q.right q.endpoints))
        ((weakRowIso E η).app
          (interval q.left p.right ((NestedInterval.left_anti (leOfHom f)).trans p.endpoints)))
      · exact η.hom.hom.naturality _
      · exact η.hom.hom.naturality _)

/-- The interval comparison is a functor on the existing weak quotient-row category. -/
def weakRowIntervalComparison :
    WeakRows (ofExactCategory E) n ⥤ (NestedInterval n ⥤ QConstruction E.deflation E.inflation)
    where
  obj F := intervalQFunctor E F.obj
  map η := (intervalQFunctorIso E η).hom
  map_id F := by
    ext p
    change (E.qIsoOfIso ((weakRowIso E (𝟙 F)).app _)).hom = 𝟙 _
    rw [weakRowIso_id]
    rfl
  map_comp η θ := by
    ext p
    change (E.qIsoOfIso ((weakRowIso E (η ≫ θ)).app _)).hom =
      (E.qIsoOfIso ((weakRowIso E η).app _)).hom ≫
        (E.qIsoOfIso ((weakRowIso E θ).app _)).hom
    rw [weakRowIso_comp]
    change (E.qIsoOfIso ((weakRowIso E η).app _ ≪≫ (weakRowIso E θ).app _)).hom = _
    rw [ExactCategory.ExactStructure.qIsoOfIso_trans, Iso.trans_hom]

/-- The actual interval functor commutes strictly with every ordinal restriction. -/
theorem intervalQFunctor_reindex {m : SimplexCategory} (α : m ⟶ n)
    (F : Obj (ofExactCategory E) n) :
    intervalQFunctor E ((reindex (ofExactCategory E) α).obj F) =
      nestedIntervalMap α ⋙ intervalQFunctor E F := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The original nerve chain and interval comparison form the genuine Q-valued grid. -/
def weakChainQFunctor {k : SimplexCategory}
    (F : ComposableArrows (WeakRows (ofExactCategory E) n) k.len) :
    Fin (k.len + 1) × NestedInterval n ⥤ QConstruction E.deflation E.inflation :=
  Functor.uncurry.obj (F ⋙ weakRowIntervalComparison E)

/-- Both ordinal directions commute with the Q-valued original weak-chain construction. -/
theorem weakChainQFunctor_reindex {n' k k' : SimplexCategory}
    (α : n' ⟶ n) (β : k' ⟶ k)
    (F : ComposableArrows (WeakRows (ofExactCategory E) n) k.len) :
    weakChainQFunctor E
      ((SimplexCategory.toCat.map β).toFunctor ⋙ F ⋙ weakRowsReindex (ofExactCategory E) α) =
      ((SimplexCategory.toCat.map β).toFunctor.prod (nestedIntervalMap α)) ⋙
        weakChainQFunctor E F := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.QuotientRows
