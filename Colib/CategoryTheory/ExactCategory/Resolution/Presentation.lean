/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Resolution.Finite
public import Colib.CategoryTheory.ExactCategory.KernelPullback
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-! Adapted from `Quillen/Aglib/CategoryTheory/ExactCategory/Resolution/Presentation.lean`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
This module supplies finite-resolution prerequisites, not the Resolution theorem. -/

/-!
# One-step presentations with controlled syzygy

These are actual kernel–cokernel pairs. They are used to prove closure of
resolution-length strata without assuming that the resolving objects are
projective or that comparison morphisms lift against arbitrary epimorphisms.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- A conflation resolving `X` by a `P`-object and a `Q`-syzygy. -/
structure Presentation (P Q : C → Prop) (X : C) where
  /-- The kernel object of the presentation, required to satisfy `Q`. -/
  syzygy : C
  /-- The object satisfying `P` that admits the deflation onto `X`. -/
  middle : C
  /-- The inflation of the syzygy into the middle object. -/
  f : syzygy ⟶ middle
  /-- The deflation from the middle object onto the object being presented. -/
  g : middle ⟶ X
  zero : f ≫ g = 0
  conflation : E.conflation (ShortComplex.mk f g zero)
  middle_mem : P middle
  syzygy_mem : Q syzygy

/-- One additional admissible resolution step. -/
def ResolutionStep (P Q : C → Prop) : ObjectProperty C :=
  fun X => Nonempty (E.Presentation P Q X)

namespace Presentation
variable {E} {P Q : C → Prop} {X : C}

/-- The actual short complex underlying the presentation. -/
abbrev complex (T : E.Presentation P Q X) : ShortComplex C := ShortComplex.mk T.f T.g T.zero

lemma deflation (T : E.Presentation P Q X) : E.deflation T.g :=
  E.deflation_of_conflation T.conflation

lemma inflation (T : E.Presentation P Q X) : E.inflation T.f :=
  E.inflation_of_conflation T.conflation

/-- The identity presentation uses a genuine zero kernel. -/
def ofMem (hX : P X) (h₀ : Q (0 : C)) : E.Presentation P Q X where
  syzygy := 0
  middle := X
  f := 0
  g := 𝟙 X
  zero := by simp
  conflation := E.conflation_of_deflation_of_isKernel (E.deflation_id X)
    (kernel.isLimitConeZeroCone (𝟙 X))
  middle_mem := hX
  syzygy_mem := h₀

/-- A resolving middle term and an actual finite syzygy resolution give an
actual successor resolution. -/
def finiteResolution (T : E.Presentation P Q X) (R : E.FiniteResolution P T.syzygy) :
    E.FiniteResolution P X := .step T.complex T.conflation T.middle_mem R

@[simp] lemma length_finiteResolution (T : E.Presentation P Q X)
    (R : E.FiniteResolution P T.syzygy) : (T.finiteResolution R).length = R.length + 1 := rfl

end Presentation

variable (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- Every bounded finite resolution supplies a one-step presentation whose
syzygy lies in the previous resolution stratum. -/
lemma resolutionLength_succ_iff (n : ℕ) (X : C) :
    E.ResolutionLength P (n + 1) X ↔ E.ResolutionStep P (E.ResolutionLength P n) X := by
  constructor
  · rintro ⟨R, hR⟩
    cases R with
    | of_mem hX =>
      exact ⟨Presentation.ofMem hX ⟨.of_mem P.prop_zero, Nat.zero_le n⟩⟩
    | step S hS hP R =>
      exact ⟨⟨S.X₁, S.X₂, S.f, S.g, S.zero, hS, hP,
        ⟨R, Nat.le_of_succ_le_succ hR⟩⟩⟩
  · rintro ⟨T⟩
    obtain ⟨R, hR⟩ := T.syzygy_mem
    exact ⟨T.finiteResolution R, Nat.succ_le_succ hR⟩

end CategoryTheory.ExactCategory.ExactStructure
