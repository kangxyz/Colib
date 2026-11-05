/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.Waldhausen.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Waldhausen structures transported through an actual categorical equivalence

The original morphism classes are pulled back along the forward functor. A specified source
object whose actual image is zero is retained as the chosen zero. Pushouts are constructed
using the genuine equivalence and the original Waldhausen pushout axiom.
Implementation provenance: adapted from `Quillen/Waldhausen/EquivalenceStructure.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This isolated draft has not been compiled.

-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (W : Structure D) (e : C ≌ D) (z : C) (hz : IsZero (e.functor.obj z))

/-- The original classes transported along an equivalence, with the supplied actual zero object. -/
def Structure.ofEquivalence : Structure C where
  zero := z
  isZero := IsZero.of_full_of_faithful_of_isZero e.functor z hz
  cof := W.cof.inverseImage e.functor
  weq := W.weq.inverseImage e.functor
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso _ _ f hf := by
    let : IsIso f := hf
    exact W.cof_iso _ inferInstance
  weq_iso _ _ f hf := by
    let : IsIso f := hf
    exact W.weq_iso _ inferInstance
  cof_zero X := by
    change W.cof _
    have he := hz.eq_of_src
      (e.functor.map ((IsZero.of_full_of_faithful_of_isZero e.functor z hz).to_ X))
      ((hz.iso W.isZero).hom ≫ W.isZero.to_ (e.functor.obj X))
    rw [he]
    exact W.cof.comp_mem _ _ (W.cof_iso _ inferInstance) (W.cof_zero _)
  pushout_exists i f hi := by
    obtain ⟨P, g, j, h⟩ := W.pushout_exists (e.functor.map i) (e.functor.map f) hi
    have : HasPushout (e.functor.map i) (e.functor.map f) := h.hasPushout
    have : HasColimit (span i f ⋙ e.functor) :=
      hasColimit_of_iso (spanCompIso e.functor i f)
    have : HasPushout i f := Adjunction.hasColimit_of_comp_equivalence (span i f) e.functor
    exact ⟨pushout i f, pushout.inl i f, pushout.inr i f, IsPushout.of_hasPushout i f⟩
  cof_pushout hi h := W.cof_pushout hi (h.map e.functor)
  gluing a b d p hi hi' h h' ei ef eg ej ha hb hd :=
    W.gluing (e.functor.map a) (e.functor.map b) (e.functor.map d) (e.functor.map p)
      hi hi' (h.map e.functor) (h'.map e.functor)
      (by simpa only [Functor.map_comp] using congrArg e.functor.map ei)
      (by simpa only [Functor.map_comp] using congrArg e.functor.map ef)
      (by simpa only [Functor.map_comp] using congrArg e.functor.map eg)
      (by simpa only [Functor.map_comp] using congrArg e.functor.map ej) ha hb hd

/-- The actual forward equivalence is Waldhausen-exact for the transported original classes. -/
theorem Structure.ofEquivalence_exact :
    IsExact (W.ofEquivalence e z hz).cof (W.ofEquivalence e z hz).weq W.cof W.weq
      e.functor where
  zero h := IsZero.of_full_of_faithful_of_isZero e.inverse _
    (h.of_iso (e.unitIso.app _).symm)
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map e.functor

/-- The actual inverse equivalence is exact for the transported original classes. -/
theorem Structure.ofEquivalence_inverse_exact :
    IsExact W.cof W.weq (W.ofEquivalence e z hz).cof (W.ofEquivalence e z hz).weq
      e.inverse where
  zero h := IsZero.of_full_of_faithful_of_isZero e.functor _
    (h.of_iso (e.counitIso.app _))
  cofibration f hf := by
    change W.cof (e.functor.map (e.inverse.map f))
    have hm : e.functor.map (e.inverse.map f) =
        e.counitIso.hom.app _ ≫ f ≫ e.counitIso.inv.app _ := by
      simpa only [Functor.comp_map, Functor.id_map, Category.assoc,
        Iso.hom_inv_id_app, Category.comp_id] using
        congrArg (fun k => k ≫ e.counitIso.inv.app _)
          (e.counitIso.hom.naturality f)
    rw [hm]
    exact W.cof.comp_mem _ _ (W.cof_iso _ inferInstance)
      (W.cof.comp_mem _ _ hf (W.cof_iso _ inferInstance))
  weak f hf := by
    change W.weq (e.functor.map (e.inverse.map f))
    have hm : e.functor.map (e.inverse.map f) =
        e.counitIso.hom.app _ ≫ f ≫ e.counitIso.inv.app _ := by
      simpa only [Functor.comp_map, Functor.id_map, Category.assoc,
        Iso.hom_inv_id_app, Category.comp_id] using
        congrArg (fun k => k ≫ e.counitIso.inv.app _)
          (e.counitIso.hom.naturality f)
    rw [hm]
    exact W.weq.comp_mem _ _ (W.weq_iso _ inferInstance)
      (W.weq.comp_mem _ _ hf (W.weq_iso _ inferInstance))
  pushout _ h := h.map e.inverse

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0145",
  colib_ref "Waldhausen1985" "Sections 1.1-1.2, pp.320-321 and 326-327"
    "background" "Transport derived from the axioms with an explicit preimage zero object"]
  CategoryTheory.Waldhausen.Structure.ofEquivalence
  CategoryTheory.Waldhausen.Structure.ofEquivalence_exact
  CategoryTheory.Waldhausen.Structure.ofEquivalence_inverse_exact
