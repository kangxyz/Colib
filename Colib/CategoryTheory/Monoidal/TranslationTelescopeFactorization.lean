/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.TranslationTelescopeTransitions
public import Colib.CategoryTheory.Grothendieck.FiberTransitions
public import Mathlib.CategoryTheory.Functor.EpiMono

/-! # Exact original-stage factorization in the translation telescope -/

/-!
Implementation provenance: adapted from
`Quillen/CategoryTheory/Monoidal/TranslationTelescopeFactorization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section
open CategoryTheory MonoidalCategory Grothendieck
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)

/-- The original fiber map, with only the common-universe wrapper removed. -/
def stageFiber {n m : ℕ} {X Y : C}
    (g : (stageInclusion e n).obj X ⟶ (stageInclusion e m).obj Y) :
    (EndofunctorTelescope.iterate (tensorRight e) (m - n)).obj X ⟶ Y :=
  AsSmall.down.map g.fiber

/-- The original stage transition followed by the actual vertical fiber is the
specified arrow, rather than merely a homotopic or quotient substitute. -/
theorem stageTransition_factorization {n m : ℕ} {X Y : C}
    (g : (stageInclusion e n).obj X ⟶ (stageInclusion e m).obj Y) :
    (stageTransition e g.base).app X ≫ stageArrow e m (stageFiber e g) = g := by
  exact Grothendieck.fiberTransition_factorization (diagram e) g

/-- Every translated stage arrow has the canonical inverse-lineator normal form. -/
theorem translatedStageTransition_factorization {n m : ℕ} (s : C) {X Y : C}
    (g : (leftTranslation e s).obj ((stageInclusion e n).obj X) ⟶
      (stageInclusion e m).obj Y) :
    (leftTranslation e s).map ((stageTransition e g.base).app X) ≫
      stageArrow e m (rightIterateLineator e (m - n) s X ≫ stageFiber e g) = g := by
  rw [stageArrow_comp, ← Category.assoc]
  erw [← stageTransition_action]
  exact stageTransition_factorization e g

/-- The iterated lineator is an actual isomorphism with the original commuting
map as its inverse. -/
def rightIterateLineatorIso (n : ℕ) (P X : C) :
    P ⊗ (EndofunctorTelescope.iterate (tensorRight e) n).obj X ≅
      (EndofunctorTelescope.iterate (tensorRight e) n).obj (P ⊗ X) where
  hom := rightIterateLineator e n P X
  inv := (EndofunctorTelescope.commuteIterate (leftStep e P) n).app X
  hom_inv_id := rightIterateLineator_commuteIterate e n P X
  inv_hom_id := commuteIterate_rightIterateLineator e n P X

/-- The actual translated structure arrow is epic, since its original fiber is
an invertible iterated associator. -/
theorem translatedStageTransition_epi {n m : ℕ} (h : n ⟶ m) (P X : C) :
    Epi ((leftTranslation e P).map ((stageTransition e h).app X)) := by
  apply Functor.epi_of_epi_map (modelEquivalence e).functor
  rw [leftTranslation_forward_map, stageTransition_forward]
  let : IsIso ((EndofunctorTelescope.map (leftStep e P)).map
      ((Grothendieck.ιNatTrans
        (F := EndofunctorTelescope.diagram (tensorRight e)) h).app X)).fiber := by
    change IsIso ((EndofunctorTelescope.commuteIterate (leftStep e P) (m - n)).app X ≫
      (tensorLeft P).map (𝟙 _))
    rw [(tensorLeft P).map_id]
    refine ⟨⟨rightIterateLineator e (m - n) P X, ?_, ?_⟩⟩
    · erw [Category.comp_id]
      exact commuteIterate_rightIterateLineator e (m - n) P X
    · erw [Category.comp_id]
      exact rightIterateLineator_commuteIterate e (m - n) P X
  exact Grothendieck.epi_of_fiber_isIso _ _

/-- The original vertical stage arrow remembers its exact fiber map. -/
theorem stageArrow_injective (n : ℕ) {X Y : C} {f g : X ⟶ Y}
    (h : stageArrow e n f = stageArrow e n g) : f = g :=
  congrArg ULift.down ((Grothendieck.ι (diagram e) n).map_injective h)

end CategoryTheory.MonoidalCategory.TranslationTelescope
