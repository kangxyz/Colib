/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Functor.QIsomorphisms
public import Colib.CategoryTheory.ExactCategory.QSpanNaturality

/-! # Exact-functor natural isomorphisms on the original Q-category

Adapted from `Quillen/KTheory/Map/NaturalIso.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original functors,
canonical zero isomorphisms and based homotopies.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe v u v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}
  {F G : ExactFunctor EC ED}

/-- Naturality in Q is obtained by comparing the actual pullback apices of
mapped spans with the component isomorphism at their original apex. -/
theorem mapQ_iso_naturality (e : F.toFunctor ≅ G.toFunctor)
    {X Y : C} (s : Span EC.deflation EC.inflation X Y) :
    F.mapQ.map (QConstruction.mkHom _ _ s) ≫ (ED.qIsoOfIso (e.app Y)).hom =
      (ED.qIsoOfIso (e.app X)).hom ≫ G.mapQ.map (QConstruction.mkHom _ _ s) := by
  exact ED.qSpan_iso_naturality
    (F.toQCompatibleFunctor.mapSpan s) (G.toQCompatibleFunctor.mapSpan s)
    (e.app X) (e.app Y) (e.app s.apex) (e.hom.naturality s.l) (e.hom.naturality s.r)

/-- An underlying natural isomorphism of exact functors induces a natural
isomorphism of their genuine Q-functors. -/
def mapQIso (e : F.toFunctor ≅ G.toFunctor) : F.mapQ ≅ G.mapQ :=
  NatIso.ofComponents (fun X => ED.qIsoOfIso (e.app X.obj.of)) (by
    rintro X Y ⟨s⟩
    exact mapQ_iso_naturality e s)

@[simp]
theorem mapQIso_app (e : F.toFunctor ≅ G.toFunctor) (X : C) :
    (mapQIso e).app (QConstruction.of EC.deflation EC.inflation X) = ED.qIsoOfIso (e.app X) := rfl

end CategoryTheory.ExactCategory.ExactFunctor
