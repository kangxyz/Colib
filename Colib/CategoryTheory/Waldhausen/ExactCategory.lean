/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Basic
public import Colib.CategoryTheory.ExactCategory.Isomorphisms

/-!
# Exact categories as Waldhausen categories

The cofibrations are the admissible monomorphisms, and the weak equivalences
are isomorphisms. Every Waldhausen axiom is proved from the exact-category
axioms. Adapted from `Quillen/Waldhausen/ExactCategory.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This construction does not assert the Q/S comparison theorem.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Waldhausen

variable {C : Type u} [Category.{v} C]

/-- An isomorphism on all three input vertices induces an isomorphism on
pushouts. This is the gluing lemma for isomorphisms. -/
theorem isIso_gluing {A B D P A' B' D' P' : C}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P}
    {i' : A' ⟶ B'} {f' : A' ⟶ D'} {g' : B' ⟶ P'} {j' : D' ⟶ P'}
    (h : IsPushout i f g j) (h' : IsPushout i' f' g' j')
    (a : A ⟶ A') (b : B ⟶ B') (d : D ⟶ D') (p : P ⟶ P')
    (hi : i ≫ b = a ≫ i') (hf : f ≫ d = a ≫ f')
    (hg : g ≫ p = b ≫ g') (hj : j ≫ p = d ≫ j')
    [IsIso a] [IsIso b] [IsIso d] : IsIso p := by
  have h'' : IsPushout i f (b ≫ g') (d ≫ j') :=
    h'.of_iso' (asIso a) (asIso b) (asIso d) (Iso.refl _)
      hi.symm hf.symm (by simp) (by simp)
  let e : P ≅ P' := h.isoIsPushout _ _ h''
  have hp : p = e.hom := by
    apply h.hom_ext
    · exact hg.trans (h.inl_isoIsPushout_hom _ _ h'').symm
    · exact hj.trans (h.inr_isoIsPushout_hom _ _ h'').symm
  rw [hp]
  infer_instance

variable [Preadditive C] [HasFiniteBiproducts C]

/-- Every Quillen exact category gives a genuine Waldhausen category. -/
def ofExactCategory (E : CategoryTheory.ExactCategory.ExactStructure C) : Structure C where
  zero := 0
  isZero := isZero_zero C
  cof := E.inflation
  weq := MorphismProperty.isomorphisms C
  cof_multiplicative := { id_mem := E.inflation_id, comp_mem := E.inflation_comp }
  weq_multiplicative := inferInstance
  cof_iso := by intro X Y f hf; let : IsIso f := hf; exact E.inflation_of_iso (asIso f)
  weq_iso := le_refl _
  cof_zero X := by
    simpa only [IsZero.to_eq (isZero_zero C) (0 : 0 ⟶ X)] using E.inflation_zero X
  pushout_exists i f hi := by
    let : HasPushout i f := E.inflation.hasPushout f hi
    exact ⟨pushout i f, pushout.inl _ _, pushout.inr _ _, .of_hasPushout _ _⟩
  cof_pushout hi h := E.inflation.of_isPushout h.flip hi
  gluing a b d p _ _ h h' hi hf hg hj ha hb hd := by
    let : IsIso a := ha
    let : IsIso b := hb
    let : IsIso d := hd
    exact isIso_gluing h h' a b d p hi hf hg hj

end CategoryTheory.Waldhausen
