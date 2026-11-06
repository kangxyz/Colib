/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.FlagPresentation
public import Colib.CategoryTheory.ExactCategory.Filtration.FlagExtension
public import Colib.CategoryTheory.Waldhausen.QuillenComparison.RowFull


/-! # The zero-length Q-chain is realized by an actual exact row -/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuillenComparison
open QuotientRows SSet ExactCategory.Filtration

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- The admissible one-step flag zero to the specified object. -/
def objectFlag (X : C) : ComposableArrows C 1 := zeroPrefixFlag (mk₀ X)

theorem objectFlag_inflation (X : C) {i j : Fin 2} (f : i ⟶ j) :
    E.inflation ((objectFlag X).map f) :=
  zeroPrefixFlag_inflation E (mk₀ X) (fun _ ↦ E.inflation_id X) f

/-- The one-step exact row representing a zero-length Q-chain. -/
def objectRow (X : C) : Obj (ofExactCategory E) (EdgewiseSubdivision.ε.obj ⦋0⦌) :=
  flagRow E (objectFlag X) (objectFlag_inflation E X)

/-- Its central quotient is canonically the specified object. -/
def objectRowCentralIso (X : C) :
    (objectRow E X).obj.obj (nestedToInterval (centralInterval ⦋0⦌ 0)) ≅ X :=
  ((initialCompletionIso E (objectFlag X) (objectFlag_inflation E X)
    (Limits.isZero_zero C)).app (Fin.last 1)).symm

/-- Every zero-length Q-chain has an actual row preimage up to isomorphism. -/
def objectRowChainIso (G : ComposableArrows (QConstruction E.deflation E.inflation) 0) :
    ((rowChainComparison E ⦋0⦌).obj ⟨objectRow E (G.obj 0).obj.of⟩).of ≅ G :=
  ComposableArrows.isoMk₀ (E.qIsoOfIso (objectRowCentralIso E (G.obj 0).obj.of))

end CategoryTheory.Waldhausen.QuillenComparison
