/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Grothendieck.EndofunctorTelescope
public import Mathlib.CategoryTheory.Monoidal.Category
public import Colib.CategoryTheory.Monoidal.TensorFunctor.Associativity
/-!
Adapted from `Quillen/CategoryTheory/Monoidal/TranslationTelescope.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the original
functors, associators and category universes.
 # Actual left translations on the right-translation telescope -/

@[expose] public section

open CategoryTheory MonoidalCategory Grothendieck
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
/-- The original right-translation sequence in a common universe, retaining every iterate. -/
def diagram (e : C) : ℕ ⥤ Cat.{max u v, max u v} :=
  EndofunctorTelescope.diagram (tensorRight e) ⋙ Cat.asSmallFunctor.{0}
/-- The actual Grothendieck model of the right-translation sequence. -/
abbrev Model (e : C) := Grothendieck (diagram e)
/-- The explicit common-universe equivalence to the original telescope. -/
def modelEquivalence (e : C) : Model e ≌ EndofunctorTelescope.Model (tensorRight e) :=
  Grothendieck.compAsSmallFunctorEquivalence _
/-- The original left-tensor functor transported to the actual common-universe telescope. -/
def leftTranslation (e P : C) : Model e ⥤ Model e :=
  (modelEquivalence e).functor ⋙ EndofunctorTelescope.map (leftStep e P) ⋙
    (modelEquivalence e).inverse

theorem inclusion_forward (e : C) (n : ℕ) :
    Grothendieck.ι (diagram e) n ⋙ (modelEquivalence e).functor =
      AsSmall.down ⋙ Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight e)) n := by
  refine Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext _ _ ?_ ?_
  · rfl
  simp [modelEquivalence, Grothendieck.ι, diagram, down_comp, eqToHom_down]

theorem inclusion_inverse (e : C) (n : ℕ) :
    Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight e)) n ⋙
      (modelEquivalence e).inverse = AsSmall.up ⋙ Grothendieck.ι (diagram e) n := by
  refine Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext _ _ ?_ ?_
  · rfl
  simp [modelEquivalence, Grothendieck.ι, diagram, eqToHom_map]

theorem inclusion_leftTranslation (e P : C) (n : ℕ) :
    Grothendieck.ι (diagram e) n ⋙ leftTranslation e P =
      (AsSmall.down ⋙ tensorLeft P ⋙ AsSmall.up) ⋙ Grothendieck.ι (diagram e) n := by
  rw [leftTranslation, ← Functor.assoc, inclusion_forward]
  rw [Functor.assoc, ← Functor.assoc (Grothendieck.ι _ n),
    EndofunctorTelescope.inclusion_map, Functor.assoc, inclusion_inverse]
  rfl
/-- The successor step remains precisely right tensoring by the chosen object. -/
theorem diagram_map_succ (e : C) (n : ℕ) :
    (diagram e).map (homOfLE (Nat.le_succ n)) =
      (AsSmall.down ⋙ tensorRight e ⋙ AsSmall.up).toCatHom := by
  change (AsSmall.down ⋙ EndofunctorTelescope.iterate (tensorRight e) (n + 1 - n) ⋙
    AsSmall.up).toCatHom = _
  rw [Nat.add_sub_cancel_left]
  rfl

/-- Left translation of the original unit vertex retains its actual right-unitor isomorphism. -/
def leftTranslationUnitIso (e P : C) :
    (leftTranslation e P).obj ⟨0, AsSmall.up.obj (𝟙_ C)⟩ ≅
      (⟨0, AsSmall.up.obj P⟩ : Model e) :=
  (Grothendieck.ι (diagram e) 0).mapIso (AsSmall.up.mapIso (ρ_ P))

end CategoryTheory.MonoidalCategory.TranslationTelescope
