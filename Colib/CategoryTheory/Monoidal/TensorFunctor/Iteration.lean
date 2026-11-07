/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.TensorFunctor.Factorization
public import Colib.CategoryTheory.Grothendieck.EndofunctorTelescope
public import Mathlib.CategoryTheory.Groupoid

/-!
Adapted from `Quillen/Aglib/CategoryTheory/Monoidal/TensorFunctor/Iteration.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original functors
and coherence transformations.
 # Commutation of finite tensor-functor iterates

The original associators and braiding give the displayed natural
isomorphisms. The source groupoid and its original monoidal structure
are retained; no telescope model or group completion is constructed.
-/
@[expose] public section

noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]

/-- The original associator interchanges left and right translation. -/
def leftRightCommutationIso (P Q : C) : tensorLeft P ⋙ tensorRight Q ≅
    tensorRight Q ⋙ tensorLeft P :=
  NatIso.ofComponents (fun X ↦ asIso ((leftStep Q P).app X))
    (fun {_ _} f ↦ (leftStep Q P).naturality f)

/-- The original iterated associator intertwines left translation and stabilization. -/
def leftIterateCommutationIso (e P : C) (k : ℕ) :
    tensorLeft P ⋙ EndofunctorTelescope.iterate (tensorRight e) k ≅
      EndofunctorTelescope.iterate (tensorRight e) k ⋙ tensorLeft P :=
  NatIso.ofComponents
    (fun X ↦ asIso ((EndofunctorTelescope.commuteIterate (leftStep e P) k).app X))
    (fun {_ _} f ↦ (EndofunctorTelescope.commuteIterate (leftStep e P) k).naturality f)

/-- At a finite stage the original braiding is genuinely a natural isomorphism. -/
def rightLeftBraidingIso [BraidedCategory C] (P : C) : tensorRight P ≅ tensorLeft P :=
  NatIso.ofComponents (fun X ↦ β_ X P)
    (fun {_ _} f ↦ BraidedCategory.braiding_naturality_left f P)

end CategoryTheory.MonoidalCategory.TranslationTelescope
