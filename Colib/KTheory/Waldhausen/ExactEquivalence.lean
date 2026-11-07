/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Functoriality
public import Mathlib.Algebra.Group.Equiv.Defs

/-!
# The canonical K-group equivalence of a two-sided exact categorical equivalence

Implementation correspondence: Quillen/Waldhausen/Functoriality/ExactEquivalence.lean
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The original pointwise inverse identities
are presented as equalities of the actual group homomorphisms; the equivalence retains
the original forward and inverse canonical K-maps.

The maps are exactly the existing canonical `KMap` of the forward and inverse functors.
Their composites are identity by the already proved composition law, natural-isomorphism
invariance applied to the actual unit and counit, and the identity law.
Mathematically this is the formal consequence of Waldhausen's functoriality and
weak-natural-transformation homotopy invariance in Proposition 1.3.1, not an
application of the Approximation theorem.

No strict preservation of the chosen zero is required: the canonical maps already use the
proved zero rebasing and based homotopy comparison. These are the connective groups of the
existing unnormalized IsZero-diagonal S-construction. This does not identify that model with
a strict chosen-zero model, Quillen Q-theory, or a nonconnective spectrum.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.Waldhausen

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} (e : C ≌ D)
  (hF : IsExact V.cof V.weq W.cof W.weq e.functor)
  (hG : IsExact W.cof W.weq V.cof V.weq e.inverse)

/-- The inverse exact functor's canonical K-map is a left inverse. -/
theorem KMap_inverse_comp_KMap (n : ℕ) :
    (KMap hG n).comp (KMap hF n) = MonoidHom.id (V.K n) := by
  rw [KMap_comp_KMap]
  exact (KMap_eq_of_iso (hF.comp hG) (IsExact.id V.cof V.weq) e.unitIso.symm n).trans
    (KMap_id V n)

/-- The inverse exact functor's canonical K-map is a right inverse. -/
theorem KMap_comp_KMap_inverse (n : ℕ) :
    (KMap hF n).comp (KMap hG n) = MonoidHom.id (W.K n) := by
  rw [KMap_comp_KMap]
  exact (KMap_eq_of_iso (hG.comp hF) (IsExact.id W.cof W.weq) e.counitIso n).trans
    (KMap_id W n)

/-- The existing canonical K-maps of an equivalence exact in both directions form a genuine
multiplicative equivalence, in every nonnegative K-degree. -/
def KEquivOfExactEquivalence (n : ℕ) : V.K n ≃* W.K n where
  toFun := KMap hF n
  invFun := KMap hG n
  left_inv x := DFunLike.congr_fun (KMap_inverse_comp_KMap e hF hG n) x
  right_inv x := DFunLike.congr_fun (KMap_comp_KMap_inverse e hF hG n) x
  map_mul' := (KMap hF n).map_mul

/-- The forward homomorphism is the original canonical exact-functor map. -/
theorem KEquivOfExactEquivalence_toMonoidHom (n : ℕ) :
    (KEquivOfExactEquivalence e hF hG n).toMonoidHom = KMap hF n := rfl

/-- The inverse homomorphism is the original canonical inverse-functor map. -/
theorem KEquivOfExactEquivalence_symm_toMonoidHom (n : ℕ) :
    (KEquivOfExactEquivalence e hF hG n).symm.toMonoidHom = KMap hG n := rfl

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0179",
  colib_ref "quillen" "Quillen/Waldhausen/Functoriality/ExactEquivalence.lean:32-59"
    "adaptation" "The actual forward and inverse canonical K-maps, using unit and counit"]
  CategoryTheory.Waldhausen.KMap_inverse_comp_KMap
  CategoryTheory.Waldhausen.KMap_comp_KMap_inverse
  CategoryTheory.Waldhausen.KEquivOfExactEquivalence
  CategoryTheory.Waldhausen.KEquivOfExactEquivalence_toMonoidHom
  CategoryTheory.Waldhausen.KEquivOfExactEquivalence_symm_toMonoidHom

attribute [colib_ref "Waldhausen1985" "Section 1.3, Proposition 1.3.1, pp. 330-331"
  "ingredient"
  "Formal consequence of functoriality and weak-natural-transformation homotopy \
  invariance, applied to the unit and counit of an equivalence exact in both directions"]
  CategoryTheory.Waldhausen.KMap_inverse_comp_KMap
  CategoryTheory.Waldhausen.KMap_comp_KMap_inverse
  CategoryTheory.Waldhausen.KEquivOfExactEquivalence
