/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Extensions.Pullback
public import Colib.CategoryTheory.QConstruction.Basic

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionBaseChange.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Base change of extension fibers

Pullback is required only for admissible epimorphisms, as supplied by the exact
structure. No ambient finite-limit assumption is imposed. A Q span transports
extensions by pullback along its inflation followed by composition with its
deflation. Descent and compositional coherence remain separate obligations.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- Contravariant transport attached to an actual original Q-span representative.
This is not yet a functor out of the quotient Q category. -/
def extensionSpanTransport {X Y : C} (s : Span E.deflation E.inflation X Y) :
    E.ExtensionFiber Y ⥤ E.ExtensionFiber X :=
  E.extensionFiberPullback s.r ⋙ E.extensionFiberPostcompose s.l s.wl

end CategoryTheory.ExactCategory.ExactStructure
