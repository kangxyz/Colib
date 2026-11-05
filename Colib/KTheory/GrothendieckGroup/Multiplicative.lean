/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.GrothendieckGroup.Basic

/-!
# Generator extensionality for multiplicative Grothendieck-group maps

Maps into any group are determined by the actual object generators. The
target need not be commutative. The proof uses the original free-abelian
presentation and does not impose a new relation.

## Implementation provenance

Extracted from `Quillen/KTheory/GrothendieckComparison/Naturality.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The exact-structure assumptions,
independent object/hom universes, actual functors and generator maps are retained.
This is purely algebraic and makes no identification with topological π₁ or K₀.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Maps from the multiplicative Grothendieck group into any group are
determined by the object generators; commutativity of the target is unnecessary. -/
@[ext] lemma grothendieck_mulHom_ext {G : Type*} [Group G]
    (f g : Multiplicative E.GrothendieckGroup →* G)
    (h : ∀ X, f (Multiplicative.ofAdd (E.grothendieckClass X)) =
      g (Multiplicative.ofAdd (E.grothendieckClass X))) : f = g := by
  apply MonoidHom.ext
  intro a
  change f (Multiplicative.ofAdd a.toAdd) = g (Multiplicative.ofAdd a.toAdd)
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk'_surjective E.grothendieckRelations a.toAdd
  rw [← hr]
  clear hr a
  induction r using FreeAbelianGroup.induction_on with
  | zero => simp
  | of X => exact h X
  | neg r ih =>
      simp only [map_neg, ofAdd_neg, map_inv, ih]
  | add r s hr hs =>
      simp only [map_add, ofAdd_add, map_mul, hr, hs]


end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0078",
  colib_ref "WeibelKBook" "II, Definition 7.1, object generators, page 60"
    "adaptation"
    "Existing homomorphisms into any group are determined by object generators"]
  CategoryTheory.ExactCategory.ExactStructure.grothendieck_mulHom_ext
