/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors, kangxyz
-/
module

import Colib.RingTheory.Koszul.PolynomialVariables
import Mathlib.Data.ZMod.Basic

/-!
Regression consumers for arbitrary coordinate types, independent universes, empty families,
the zero ring, flat coefficients, and the actual original degree-zero augmentation map.
-/

noncomputable section

open CategoryTheory RingTheory.Sequence
open scoped TensorProduct ExteriorAlgebra

universe u v w

variable {R : Type u} [CommRing R] {I : Type v} {n : ℕ}

example (s : Set I) (i : I) (hi : i ∉ s) :
    IsSMulRegular
      (MvPolynomial I R ⧸ Ideal.span ((MvPolynomial.X : I → MvPolynomial I R) '' s))
      (MvPolynomial.X i : MvPolynomial I R) :=
  MvPolynomial.isSMulRegular_quotient_span_X s i hi

example (l : List I) (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial I R) (l.map (MvPolynomial.X : I → MvPolynomial I R)) :=
  MvPolynomial.isWeaklyRegular_X l hl

example [Nontrivial R] (l : List I) (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial I R)
      (l.map (MvPolynomial.X : I → MvPolynomial I R)) :=
  MvPolynomial.isRegular_X_of_nodup l hl

-- The ambient coordinate type need not be finite.
example (n : ℕ) :
    Koszul.IsKoszulRegular (fun i : Fin n => (MvPolynomial.X i.val : MvPolynomial ℕ R)) :=
  Koszul.isKoszulRegular_X_of_injective Fin.val Fin.val_injective

-- No nontriviality assumption is introduced, including in the ring augmentation theorem.
example (f : Fin n → I) (hf : Function.Injective f) :
    QuasiIso (Koszul.koszulAugmentation
      (fun i => (MvPolynomial.X (f i) : MvPolynomial I (ZMod 1)))) :=
  Koszul.koszulAugmentation_X_quasiIso f hf

example (f : Fin 0 → I) :
    QuasiIso (Koszul.koszulAugmentation
      (fun i => (MvPolynomial.X (f i) : MvPolynomial I R))) :=
  Koszul.koszulAugmentation_X_quasiIso f (fun i => Fin.elim0 i)

variable (f : Fin n → I) (hf : Function.Injective f)
variable (M : ModuleCat.{w} (MvPolynomial I R)) [Module.Flat (MvPolynomial I R) M]

example : QuasiIso (Koszul.coefficientAugmentation (fun i => MvPolynomial.X (f i)) M) :=
  Koszul.coefficientAugmentation_X_quasiIso f hf M

example (d : ℕ) (hd : d ≠ 0) :
    CategoryTheory.Limits.IsZero
      ((Koszul.seqComplexTensor
        (fun i => (MvPolynomial.X (f i) : MvPolynomial I R)) M).homology d) :=
  Koszul.isKoszulRegularOn_X_of_injective f hf M d hd

-- The constructed map is the existing augmentation, not merely an unspecified quasi-isomorphism.
example (m : M) :
    ((Koszul.coefficientAugmentation (fun i => MvPolynomial.X (f i)) M).f 0
      ((exteriorPower.zeroEquiv (MvPolynomial I R)
        (Fin n → MvPolynomial I R)).symm 1 ⊗ₜ[MvPolynomial I R] m)).down =
          Submodule.Quotient.mk m := by
  simpa only [LinearEquiv.apply_symm_apply, one_smul] using
    Koszul.coefficientAugmentation_f_zero_tmul (fun i => MvPolynomial.X (f i)) M
      ((exteriorPower.zeroEquiv (MvPolynomial I R) (Fin n → MvPolynomial I R)).symm 1) m

example (S : Type w) [CommRing S] [Algebra (MvPolynomial I R) S]
    [Module.Flat (MvPolynomial I R) S] :
    QuasiIso (Koszul.koszulAugmentation
      (fun i => algebraMap (MvPolynomial I R) S (MvPolynomial.X (f i)))) :=
  Koszul.koszulAugmentation_map_X_quasiIso_of_flat f hf S

end
