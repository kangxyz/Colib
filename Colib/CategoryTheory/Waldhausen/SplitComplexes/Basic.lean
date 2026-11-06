/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.DegreewiseSplitMono
public import Colib.CategoryTheory.Waldhausen.Complexes
public import Colib.CategoryTheory.Waldhausen.ExactFunctorIso

/-!
# Degreewise split cofibrations of actual complexes

A degreewise split monomorphism has a retraction in each degree; the
retractions are not required to form a chain map. Pushout stability is
proved by constructing the retraction in each degree. Together with the
actual quasi-isomorphism gluing theorem this gives a Waldhausen structure,
and the identity gives an exact comparison to the ambient-monomorphism
model. No comparison equivalence is asserted.
-/
/-! Adapted from `Quillen.Waldhausen.SplitComplexes.Basic`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CochainComplex



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

universe v u

namespace CategoryTheory.Waldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The degreewise split, quasi-isomorphism Waldhausen structure on actual
cochain complexes in an abelian category. -/
def splitComplexes (A : Type u) [Category.{v} A] [Abelian A] :
    Structure (CochainComplex A ℤ) :=
  { complexes A with
    cof := degreewiseSplitMono
    cof_multiplicative := inferInstance
    cof_iso := by intro K L f hf; let := hf; exact degreewiseSplitMono_of_isIso f
    cof_zero K := degreewiseSplitMono_of_isZero (isZero_zero _) _
    pushout_exists i f _ :=
      ⟨pushout i f, pushout.inl _ _, pushout.inr _ _, .of_hasPushout _ _⟩
    cof_pushout hi h := degreewiseSplitMono_pushout hi h
    gluing a b d p hi hi' h h' ei ef eg ej ha hb hd :=
      (complexes A).gluing a b d p (degreewiseSplitMono_mono hi)
        (degreewiseSplitMono_mono hi') h h' ei ef eg ej ha hb hd }

/-- The identity comparison from degreewise split to ambient-monomorphism
cofibrations is Waldhausen-exact. -/
theorem splitComplexes_to_complexes_exact :
    IsExact (splitComplexes A).cof (splitComplexes A).weq
      (complexes A).cof (complexes A).weq (𝟭 (CochainComplex A ℤ)) where
  zero h := h
  cofibration _ h := degreewiseSplitMono_mono h
  weak _ h := h
  pushout _ h := h


end CategoryTheory.Waldhausen
