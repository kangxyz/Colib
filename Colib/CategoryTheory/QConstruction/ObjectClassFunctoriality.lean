/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.QConstruction.ObjectClass

/-!
# Functoriality of categorical Q-object classes

Object classes commute with an actual functor between groupoid targets.
This one categorical statement does not use or construct realized paths.

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

/-- The object-loop construction commutes with functors between groupoids. -/
lemma qObjectClass_comp {D T : Type*} [Groupoid D] [Groupoid T]
    (F : E.QCategory ⥤ D) (G : D ⥤ T) (X : C) :
    E.qObjectClass (F ⋙ G) X = G.mapEnd _ (E.qObjectClass F X) := by
  apply End.ext
  simp [qObjectClass]


end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0077",
  colib_ref "WeibelKBook" "IV, proof of Proposition 6.2, equation (6.2.2), page 54"
    "background"
    "Functoriality under groupoid target functors, not a topological naturality comparison"]
  CategoryTheory.ExactCategory.ExactStructure.qObjectClass_comp
