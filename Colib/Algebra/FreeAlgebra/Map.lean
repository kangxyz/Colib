/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Logic.Function.Basic

/-!
# Injective changes of free-algebra generators

These lemmas concern Mathlib's existing `FreeAlgebra.lift`, without defining
another free-algebra map. An injective map of generators admits a set-theoretic
retraction, so its free-algebra lift is injective. No analogous assertion about
tensor algebras or module-linear retractions is made.
-/

@[expose] public noncomputable section

namespace FreeAlgebra

variable {R X Y Z : Type*} [CommSemiring R]

/-- Composing the native free-algebra lifts of two generator maps is the lift
of their composite. -/
theorem lift_ι_comp_lift_ι (f : X → Y) (g : Y → Z) :
    (lift R (ι R ∘ g)).comp (lift R (ι R ∘ f)) = lift R (ι R ∘ (g ∘ f)) := by
  apply hom_ext
  funext x
  simp only [AlgHom.coe_comp, Function.comp_apply, lift_ι_apply]

/-- An injective change of generators induces an injective native free-algebra
lift. The retraction used here is only a function of generating types. -/
theorem lift_ι_injective [Nonempty X] (f : X → Y) (hf : Function.Injective f) :
    Function.Injective (lift R (ι R ∘ f)) := by
  obtain ⟨g, hg⟩ := hf.hasLeftInverse
  have h : (lift R (ι R ∘ g)).comp (lift R (ι R ∘ f)) =
      AlgHom.id R (FreeAlgebra R X) := by
    apply hom_ext
    funext x
    simp only [AlgHom.coe_comp, Function.comp_apply, lift_ι_apply, AlgHom.coe_id, id_eq]
    rw [hg x]
  have hleft : Function.LeftInverse (lift R (ι R ∘ g)) (lift R (ι R ∘ f)) :=
    fun x => DFunLike.congr_fun h x
  exact hleft.injective

end FreeAlgebra
