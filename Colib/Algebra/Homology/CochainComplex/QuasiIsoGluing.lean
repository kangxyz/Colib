/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Quasi-isomorphism gluing for ordinary cochain complexes

Adapted from Quillen/Aglib/Algebra/Homology/CochainComplex/QuasiIsoGluing.lean
at c561118b7795eb9780be9ed391c3251d6a4d0afd; actual maps and hypotheses are retained.

Biproducts preserve quasi-isomorphisms, and actual pushouts along monomorphisms
admit their genuine short exact sequence. The homology sequence gives the
original gluing result with all four displayed maps and commuting equations.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The biproduct of two quasi-isomorphisms is a quasi-isomorphism. -/
private theorem quasiIso_biprod_map {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g] :
    QuasiIso (biprod.map f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := homologyFunctor A (ComplexShape.up ℤ) n
  change IsIso (H.map (biprod.map f g))
  have h : H.map (biprod.map f g) =
      (H.mapBiprod K L).hom ≫ biprod.map (H.map f) (H.map g) ≫ (H.mapBiprod K' L').inv := by
    apply (cancel_mono (H.mapBiprod K' L').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext
    · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc]
      rw [← H.map_comp, biprod.map_fst, H.map_comp]
    · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc]
      rw [← H.map_comp, biprod.map_snd, H.map_comp]
  have : IsIso (H.map f) := inferInstanceAs (IsIso (homologyMap f n))
  have : IsIso (H.map g) := inferInstanceAs (IsIso (homologyMap g n))
  have : IsIso (biprod.map (H.map f) (H.map g)) :=
    (biprod.mapIso (asIso (H.map f)) (asIso (H.map g))).isIso_hom
  rw [h]
  infer_instance

/-- The pushout exact sequence is short exact when its upper arrow is mono. -/
private theorem pushout_shortExact {C : Type*} [Category* C] [Abelian C]
    {B D E P : C} {i : B ⟶ D} {f : B ⟶ E} {g : D ⟶ P} {j : E ⟶ P}
    [Mono i] (h : IsPushout i f g j) : h.shortComplex.ShortExact where
  exact := h.exact_shortComplex
  mono_f := by dsimp [CommSq.shortComplex]; infer_instance
  epi_g := h.epi_shortComplex_g

/-- Gluing quasi-isomorphisms across pushouts along monomorphisms. -/
@[colib_ref "quillen" "Quillen/Aglib/Algebra/Homology/CochainComplex/QuasiIsoGluing.lean:76-101"
  "adaptation" "The original four pushout comparison maps and all commuting equations"]
theorem quasiIso_gluing
    {B D E P B' D' E' P' : CochainComplex A ℤ}
    {i : B ⟶ D} {f : B ⟶ E} {g : D ⟶ P} {j : E ⟶ P}
    {i' : B' ⟶ D'} {f' : B' ⟶ E'} {g' : D' ⟶ P'} {j' : E' ⟶ P'}
    [Mono i] [Mono i'] (h : IsPushout i f g j) (h' : IsPushout i' f' g' j')
    (a : B ⟶ B') (b : D ⟶ D') (d : E ⟶ E') (p : P ⟶ P')
    (hi : i ≫ b = a ≫ i') (hf : f ≫ d = a ≫ f')
    (hg : g ≫ p = b ≫ g') (hj : j ≫ p = d ≫ j')
    [QuasiIso a] [QuasiIso b] [QuasiIso d] : QuasiIso p := by
  let φ : h.shortComplex ⟶ h'.shortComplex := {
    τ₁ := a
    τ₂ := biprod.map b d
    τ₃ := p
    comm₁₂ := by
      dsimp [CommSq.shortComplex]
      apply biprod.hom_ext <;> simp [hi, hf]
    comm₂₃ := by
      dsimp [CommSq.shortComplex]
      apply biprod.hom_ext' <;> simp [hg, hj] }
  exact HomologySequence.quasiIso_τ₃ φ (pushout_shortExact h) (pushout_shortExact h')
    inferInstance (quasiIso_biprod_map b d)

end CochainComplex
