/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.TensorFunctor.Iteration
public import Colib.CategoryTheory.Monoidal.TensorFunctor.Factorization
public import Mathlib.CategoryTheory.Groupoid

/-!
Adapted from `Quillen/CategoryTheory/Monoidal/RightIterationTracks.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original functors
and coherence transformations.

# The two actual finite-stage factorization tracks

These are the two routes in the twisted group-completion argument. They share
literal endpoints but are not asserted equal or homotopic relative endpoints.
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]

/-- Apply the original factorization first and then the distinguished left translation. -/
def factorizationUpperTrack (e P Q : C) (k : ℕ)
    (G : EndofunctorTelescope.iterate (tensorRight e) k ≅ tensorRight Q ⋙ tensorLeft P) :
    EndofunctorTelescope.iterate (tensorRight e) k ⋙ tensorLeft P ≅
      tensorRight Q ⋙ tensorLeft P ⋙ tensorLeft P :=
  Functor.isoWhiskerRight G (tensorLeft P)

/-- First commute the distinguished translation past stabilization, apply the
factorization there, and use the original associator to align the endpoint. -/
def factorizationLowerTrack (e P Q : C) (k : ℕ)
    (G : EndofunctorTelescope.iterate (tensorRight e) k ≅ tensorRight Q ⋙ tensorLeft P) :
    EndofunctorTelescope.iterate (tensorRight e) k ⋙ tensorLeft P ≅
      tensorRight Q ⋙ tensorLeft P ⋙ tensorLeft P :=
  (leftIterateCommutationIso e P k).symm ≪≫
    Functor.isoWhiskerLeft (tensorLeft P) G ≪≫
      Functor.isoWhiskerRight (leftRightCommutationIso P Q) (tensorLeft P)

/-- The upper track uses exactly the left translate of the chosen factorization component. -/
theorem factorizationUpperTrack_hom_app (e P Q : C) (k : ℕ)
    (G : EndofunctorTelescope.iterate (tensorRight e) k ≅ tensorRight Q ⋙ tensorLeft P)
    (X : C) :
    (factorizationUpperTrack e P Q k G).hom.app X = (tensorLeft P).map (G.hom.app X) := rfl

/-- The lower track retains the inverse iterated associator and the final associator. -/
theorem factorizationLowerTrack_hom_app (e P Q : C) (k : ℕ)
    (G : EndofunctorTelescope.iterate (tensorRight e) k ≅ tensorRight Q ⋙ tensorLeft P)
    (X : C) :
    (factorizationLowerTrack e P Q k G).hom.app X =
      (leftIterateCommutationIso e P k).inv.app X ≫ G.hom.app ((tensorLeft P).obj X) ≫
        (tensorLeft P).map ((leftStep Q P).app X) := rfl

end CategoryTheory.MonoidalCategory.TranslationTelescope
