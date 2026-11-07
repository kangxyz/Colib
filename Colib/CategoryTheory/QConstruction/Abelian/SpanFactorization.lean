/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.QConstruction.Abelian.CospanComposition

/-!
# Actual abelian Q-arrows: SpanFactorization

Adapted from `Quillen/CategoryTheory/QConstruction/Abelian/SpanFactorization.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual span maps,
universes and epi/mono hypotheses are retained. Bicartesian implications
use Stacks 08N4 directly.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.QConstruction
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma span_factorization {X Y : C} (s : AbelianSpan X Y) :
    surjectionArrow s.l ≫ inflationArrow s.r = mkHom _ _ s := by
  let sq : IsPullback (𝟙 s.apex) (𝟙 s.apex) (𝟙 s.apex) (𝟙 s.apex) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  symm
  apply mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst (𝟙 s.apex) (𝟙 s.apex) ≫ s.l = s.l
    simp
  · change sq.isoPullback.hom ≫ pullback.snd (𝟙 s.apex) (𝟙 s.apex) ≫ s.r = s.r
    simp
end CategoryTheory.QConstruction
