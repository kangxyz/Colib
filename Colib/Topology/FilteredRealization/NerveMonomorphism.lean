/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.FilteredRealization.NerveColimit

/-! A faithful functor injective on objects induces an actual monomorphism of nerves.
This is a direct consequence of Mathlib's actual nerve and functor extensionality. -/
@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

theorem nerveMap_mono_of_injective_obj (F : C ⥤ D) [F.Faithful]
    (hF : Function.Injective F.obj) : Mono (nerveMap F) := by
  apply (NatTrans.mono_iff_mono_app _).2
  intro n
  apply (mono_iff_injective _).2
  intro s t h
  change s ⋙ F = t ⋙ F at h
  have hv : ∀ i, s.obj i = t.obj i := fun i => hF (Functor.congr_obj h i)
  refine Functor.ext hv ?_
  intro i j f
  apply F.map_injective
  simpa only [Functor.comp_map, Functor.map_comp, eqToHom_map] using! Functor.congr_hom h f

end CategoryTheory
