/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors, kangxyz
-/
module

public import Colib.Util.References

public import Colib.RingTheory.MvPolynomial.RegularSequence
public import Colib.RingTheory.Koszul.CoefficientAugmentation
public import Mathlib.RingTheory.Regular.Flat

/-!
# Native Koszul resolutions for selected polynomial variables

The original exterior-power Koszul complex on any finite injective family of variables
resolves its actual quotient. Its original coefficient augmentation is a quasi-isomorphism
for any flat module over the polynomial ring. The ring, coordinate and module universes
remain independent, and the empty family and zero coefficient ring are included.

A flat algebra over the polynomial ring has the corresponding Koszul resolution on the
images of these same variables. This uses Mathlib's existing flat transport, rather than
adding another base-change construction. Neither proper regularity after a nonfaithful
flat map nor the quotient's nontriviality is asserted.

These are native consumers of the migrated variable-regularity endpoints, using the existing
Stacks exterior Koszul complex and Colib coefficient augmentation. The original recursive
Motivic Koszul model and its coordinate adapters are not imported or reconstructed.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace Koszul

variable {R : Type u} [CommRing R] {I : Type v} {n : ℕ}

/-- Selected original variables are Koszul-regular on every flat coefficient module. -/
theorem isKoszulRegularOn_X_of_injective (f : Fin n → I) (hf : Function.Injective f)
    (M : Type w) [AddCommGroup M] [Module (MvPolynomial I R) M]
    [Module.Flat (MvPolynomial I R) M] :
    IsKoszulRegularOn (fun i => (MvPolynomial.X (f i) : MvPolynomial I R)) M :=
  isKoszulRegularOn_and_isKoszulRegular_of_regular.1
    (MvPolynomial.isWeaklyRegular_ofFn_X_on_flat f hf M)

/-- The native coefficient augmentation resolves the actual quotient by selected variables. -/
theorem coefficientAugmentation_X_quasiIso (f : Fin n → I) (hf : Function.Injective f)
    (M : ModuleCat.{w} (MvPolynomial I R)) [Module.Flat (MvPolynomial I R) M] :
    QuasiIso (coefficientAugmentation (fun i => MvPolynomial.X (f i)) M) :=
  coefficientAugmentation_quasiIso _ M (isKoszulRegularOn_X_of_injective f hf M)

/-- The original ring Koszul complex is regular even when the coefficient ring is zero. -/
theorem isKoszulRegular_X_of_injective (f : Fin n → I) (hf : Function.Injective f) :
    IsKoszulRegular (fun i => (MvPolynomial.X (f i) : MvPolynomial I R)) :=
  (isKoszulRegularOn_self_iff _).mp
    (isKoszulRegularOn_X_of_injective f hf (MvPolynomial I R))

/-- The original exterior Koszul augmentation resolves the original variable ideal quotient. -/
theorem koszulAugmentation_X_quasiIso (f : Fin n → I) (hf : Function.Injective f) :
    QuasiIso (koszulAugmentation (fun i => (MvPolynomial.X (f i) : MvPolynomial I R))) :=
  koszulAugmentation_quasiIso _ (isKoszulRegular_X_of_injective f hf)

/-- After a flat algebra map, the same selected variable images remain Koszul-regular.
No faithful-flatness, finite-generation, or properness hypothesis is needed. -/
theorem isKoszulRegular_map_X_of_flat (f : Fin n → I) (hf : Function.Injective f)
    (S : Type w) [CommRing S] [Algebra (MvPolynomial I R) S]
    [Module.Flat (MvPolynomial I R) S] :
    IsKoszulRegular (fun i => algebraMap (MvPolynomial I R) S (MvPolynomial.X (f i))) := by
  have h := (MvPolynomial.isWeaklyRegular_ofFn_X_of_injective (R := R) f hf).of_flat
    (S := S)
  rw [List.map_ofFn] at h
  exact (isKoszulRegularOn_self_iff _).mp
    (isKoszulRegularOn_and_isKoszulRegular_of_regular.1 h)

/-- The native Koszul augmentation on the images of selected variables under a flat map
resolves its literal quotient in the target ring. -/
theorem koszulAugmentation_map_X_quasiIso_of_flat (f : Fin n → I)
    (hf : Function.Injective f) (S : Type w) [CommRing S]
    [Algebra (MvPolynomial I R) S] [Module.Flat (MvPolynomial I R) S] :
    QuasiIso (koszulAugmentation
      (fun i => algebraMap (MvPolynomial I R) S (MvPolynomial.X (f i)))) :=
  koszulAugmentation_quasiIso _ (isKoszulRegular_map_X_of_flat f hf S)

end Koszul

attribute [colib_tag "COL-0265"]
  Koszul.coefficientAugmentation_X_quasiIso
  Koszul.koszulAugmentation_X_quasiIso
  Koszul.koszulAugmentation_map_X_quasiIso_of_flat

attribute [colib_ref "aglib_principal_euler_pin"
  "Aglib/RingTheory/MvPolynomial/RegularSequence.lean:36-75"
  "ingredient"
  "Source weak regularity; augmentations and flat-algebra endpoints are new native consequences"]
  Koszul.coefficientAugmentation_X_quasiIso
  Koszul.koszulAugmentation_X_quasiIso
  Koszul.koszulAugmentation_map_X_quasiIso_of_flat

attribute [colib_ref "axiom_stacks"
  "StacksFrontier/RingTheory/MvPolynomial/VariablesRegular.lean:102-115"
  "ingredient"
  "The native monomial criterion cancels a variable outside the generating coordinate set"]
  Koszul.coefficientAugmentation_X_quasiIso
  Koszul.koszulAugmentation_X_quasiIso
  Koszul.koszulAugmentation_map_X_quasiIso_of_flat

attribute [colib_ref "axiom_stacks"
  "StacksFrontier/RingTheory/Koszul/Regular.lean:846-851"
  "ingredient"
  "Weak coefficient regularity implies regularity for the original exterior Koszul complex"]
  Koszul.coefficientAugmentation_X_quasiIso
  Koszul.koszulAugmentation_X_quasiIso
  Koszul.koszulAugmentation_map_X_quasiIso_of_flat

attribute [colib_ref "mathlib_koszul_pin"
  "Mathlib/RingTheory/Regular/RegularSequence.lean:540-547"
  "ingredient"
  "Native weak regularity transport to independently sized flat coefficient modules"]
  Koszul.coefficientAugmentation_X_quasiIso

attribute [colib_ref "axiom_stacks"
  "StacksFrontier/RingTheory/Koszul/Augmentation.lean:Koszul.koszulAugmentation_quasiIso"
  "ingredient"
  "The original ring augmentation resolves the literal quotient of a Koszul-regular sequence"]
  Koszul.koszulAugmentation_X_quasiIso
  Koszul.koszulAugmentation_map_X_quasiIso_of_flat

attribute [colib_ref "mathlib_koszul_pin"
  "Mathlib/RingTheory/Regular/Flat.lean:47-49"
  "ingredient"
  "Native flat transport; properness and faithful flatness are not asserted"]
  Koszul.koszulAugmentation_map_X_quasiIso_of_flat
