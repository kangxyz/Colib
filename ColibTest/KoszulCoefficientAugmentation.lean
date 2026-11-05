module

import Colib.RingTheory.Koszul.CoefficientAugmentation

open CategoryTheory
open scoped TensorProduct ExteriorAlgebra

noncomputable section

universe u v

variable {R : Type u} [CommRing R] {r : ℕ}
variable (f : Fin r → R) (M : ModuleCat.{v} R)

example : (Koszul.seqComplexTensor f M).homology 0 ≅
    ModuleCat.of R (ULift.{u} (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R M)))) :=
  Koszul.coefficientHomologyZeroIso f M

example (hf : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn f)) :
    QuasiIso (Koszul.coefficientAugmentation f M) :=
  Koszul.coefficientAugmentation_quasiIso_of_weaklyRegular f M hf

example (m : M) :
    ((Koszul.coefficientAugmentation f M).f 0
      ((exteriorPower.zeroEquiv R (Fin r → R)).symm 1 ⊗ₜ[R] m)).down =
        Submodule.Quotient.mk m := by
  simpa only [LinearEquiv.apply_symm_apply, one_smul] using
    Koszul.coefficientAugmentation_f_zero_tmul f M
      ((exteriorPower.zeroEquiv R (Fin r → R)).symm 1) m

-- Empty sequences are included, with no properness hypothesis.
example (f : Fin 0 → R) :
    QuasiIso (Koszul.coefficientAugmentation f M) := by
  apply Koszul.coefficientAugmentation_quasiIso_of_weaklyRegular
  simp
