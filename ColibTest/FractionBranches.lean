/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.AdicCompletion.FractionBranches

/-!
# Regressions for specified fraction fields and actual completed branches

The ring, field, factor and index universes are independent. The generic product tests use
algebraic faithful algebras, with no module-finiteness premise. Locality is tested without
torsion-freeness or finiteness, and injectivity without finiteness. Original branch residue
finiteness does not assume that the original localization is finite over the base.

The formulas retain the native fraction lifts and the actual localization and completion
maps. Fractions include zero denominators, and uniqueness is tested on integral generators.
-/

noncomputable section

open IsLocalRing
open scoped TensorProduct

universe uR uS uA uF uE uB uι uD uC uQ

namespace Algebra.TensorProduct

-- The target has no assumed S-algebra structure, and F, B and E need not be fields.
example (F : Type uF) (B : Type uB) (S : Type uS) (E : Type uE) (Q : Type uQ)
    [CommSemiring F] [CommSemiring B] [CommRing S] [CommRing E] [Semiring Q]
    [Algebra F B] [Algebra F E] [Algebra S E] [IsFractionRing S E] [Algebra B Q]
    (f g : B ⊗[F] E →ₐ[B] Q)
    (h : ∀ s t : S, f (1 ⊗ₜ[F] algebraMap S E (s + t)) =
      g (1 ⊗ₜ[F] algebraMap S E (s + t))) : f = g := by
  apply algHom_ext_of_isFractionRing S
  intro s
  simpa using h s 0

section AlgebraicProduct

variable (R : Type uR) (S : Type uS) (A : Type uA)
  (F : Type uF) (E : Type uE) (B : Type uB)
  [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
  [FaithfulSMul R S] [Algebra.IsAlgebraic R S]
  [CommRing A] [Algebra R A]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsFractionRing S E]
  [IsScalarTower R S E] [Algebra F E] [IsScalarTower R F E]
  [Field B] [Algebra A B] [IsFractionRing A B]
  [Algebra R B] [IsScalarTower R A B]
  [Algebra F B] [IsScalarTower R F B]
  {ι : Type uι} [Finite ι] (D : ι → Type uD) (C : ι → Type uC)
  [∀ i, CommRing (D i)] [∀ i, IsDomain (D i)] [∀ i, Algebra A (D i)]
  [∀ i, FaithfulSMul A (D i)] [∀ i, Algebra.IsAlgebraic A (D i)]
  [∀ i, Field (C i)] [∀ i, Algebra (D i) (C i)] [∀ i, IsFractionRing (D i) (C i)]
  [∀ i, Algebra A (C i)] [∀ i, IsScalarTower A (D i) (C i)]
  [∀ i, Algebra B (C i)] [∀ i, IsScalarTower A B (C i)]
  (e : A ⊗[R] S ≃ₐ[A] ∀ i, D i)

-- Only Finite, not a chosen Fintype or a nonempty index, is in the context.
example : B ⊗[F] E ≃ₐ[B] ∀ i, C i :=
  fractionPiEquiv R S A F E B D C e

example (s t : S) (i : ι) :
    fractionPiEquiv R S A F E B D C e (1 ⊗ₜ[F] algebraMap S E (s + t)) i =
      algebraMap (D i) (C i) (e (1 ⊗ₜ[R] s) i) +
        algebraMap (D i) (C i) (e (1 ⊗ₜ[R] t) i) := by
  simp [map_add, TensorProduct.tmul_add]

example (b : B) (s t : S) (i : ι) :
    fractionPiEquiv R S A F E B D C e
        (b ⊗ₜ[F] (algebraMap S E s / algebraMap S E t)) i =
      algebraMap B (C i) b *
        (algebraMap (D i) (C i) (e (1 ⊗ₜ[R] s) i) /
          algebraMap (D i) (C i) (e (1 ⊗ₜ[R] t) i)) :=
  fractionPiEquiv_tmul_div R S A F E B D C e b s t i

-- The denominator theorem is total, rather than requiring a nonzero denominator.
example (b : B) (s : S) (i : ι) :
    fractionPiEquiv R S A F E B D C e
      (b ⊗ₜ[F] (algebraMap S E s / algebraMap S E (0 : S))) i = 0 := by
  simp

example (s : S) (i : ι) :
    fractionPiEquiv R S A F E B D C e
        (1 ⊗ₜ[F] (algebraMap S E s / algebraMap S E (1 : S))) i =
      algebraMap (D i) (C i) (e (1 ⊗ₜ[R] s) i) := by
  simp

example (b : B) (x : E) (i : ι) :
    fractionPiEquiv R S A F E B D C e (b ⊗ₜ[F] x) i =
      algebraMap B (C i) b * fractionPiEquiv R S A F E B D C e (1 ⊗ₜ[F] x) i :=
  fractionPiEquiv_tmul R S A F E B D C e b x i

example (b : B) (s t : S) :
    (fractionPiEquiv R S A F E B D C e).symm
        (fun i => algebraMap B (C i) b *
          (algebraMap (D i) (C i) (e (1 ⊗ₜ[R] s) i) /
            algebraMap (D i) (C i) (e (1 ⊗ₜ[R] t) i))) =
      b ⊗ₜ[F] (algebraMap S E s / algebraMap S E t) := by
  apply (fractionPiEquiv R S A F E B D C e).injective
  ext i
  simp only [AlgEquiv.apply_symm_apply, fractionPiEquiv_tmul_div]

example (f : B ⊗[F] E →ₐ[B] ∀ i, C i)
    (h : ∀ (s : S) (i : ι), f (1 ⊗ₜ[F] algebraMap S E s) i =
      algebraMap (D i) (C i) (e (1 ⊗ₜ[R] s) i)) (b : B) (x : E) :
    f (b ⊗ₜ[F] x) = fractionPiEquiv R S A F E B D C e (b ⊗ₜ[F] x) := by
  rw [fractionPiEquiv_unique R S A F E B D C e f h]
  rfl

end AlgebraicProduct

end Algebra.TensorProduct

namespace AdicCompletion

section CompletedDVR

variable (R : Type uR) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (F : Type uF) [Field F] [Algebra R F] [IsFractionRing R F]

example : IsDomain (AdicCompletion (maximalIdeal R) R) ∧
    IsDiscreteValuationRing (AdicCompletion (maximalIdeal R) R) :=
  ⟨inferInstance, inferInstance⟩

example : Function.Injective
    (algebraMap R (FractionRing (AdicCompletion (maximalIdeal R) R))) :=
  fraction_algebraMap_injective R

example {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R (AdicCompletion (maximalIdeal R) R) π) :=
  irreducible_algebraMap R hπ

example :
    letI := fractionCompletionAlgebra R F
    algebraMap F (FractionRing (AdicCompletion (maximalIdeal R) R)) =
      IsFractionRing.lift (K := F) (fraction_algebraMap_injective R) :=
  fractionCompletionAlgebra_algebraMap R F

example (r s : R) :
    letI := fractionCompletionAlgebra R F
    algebraMap F (FractionRing (AdicCompletion (maximalIdeal R) R))
        (algebraMap R F r / algebraMap R F s) =
      algebraMap (AdicCompletion (maximalIdeal R) R)
          (FractionRing (AdicCompletion (maximalIdeal R) R))
          (algebraMap R (AdicCompletion (maximalIdeal R) R) r) /
        algebraMap (AdicCompletion (maximalIdeal R) R)
          (FractionRing (AdicCompletion (maximalIdeal R) R))
          (algebraMap R (AdicCompletion (maximalIdeal R) R) s) := by
  let := fractionCompletionAlgebra R F
  rw [map_div₀, fractionCompletionAlgebra_algebraMap_apply,
    fractionCompletionAlgebra_algebraMap_apply]

end CompletedDVR

section OriginalResidues

-- Here the base is merely local: no DVR, faithfulness or finite-localization premise.
variable (R : Type uR) (S : Type uS) [CommRing R] [IsLocalRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [DecidableEq (Ideal S)]
  (q : IdealBranch ((maximalIdeal R).map (algebraMap R S)))

example : IsLocalHom (algebraMap R (Localization.AtPrime q.val)) := inferInstance

example : Function.Surjective
    (algebraMap S (ResidueField (Localization.AtPrime q.val))) :=
  originalBranchResidue_surjective R S q

example [Module.Finite R S] :
    Module.Finite (ResidueField R) (ResidueField (Localization.AtPrime q.val)) :=
  inferInstance

end OriginalResidues

section SpecifiedOriginalFractionField

variable (S : Type uS) (E : Type uE) [CommRing S] [IsDedekindDomain S]
  [Field E] [Algebra S E] [IsFractionRing S E] [DecidableEq (Ideal S)]
  (I : Ideal S) (q : IdealBranch I)

example :
    letI := originalBranchFractionAlgebra S E q
    IsFractionRing (Localization.AtPrime q.val) E :=
  originalBranchIsFractionRing S E q

example :
    letI := originalBranchFractionAlgebra S E q
    IsScalarTower S (Localization.AtPrime q.val) E :=
  originalBranchFractionTower S E q

example (s t : S) :
    letI := originalBranchFractionAlgebra S E q
    algebraMap (Localization.AtPrime q.val) E (algebraMap S (Localization.AtPrime q.val) s) /
        algebraMap (Localization.AtPrime q.val) E (algebraMap S (Localization.AtPrime q.val) t) =
      algebraMap S E s / algebraMap S E t := by
  let := originalBranchFractionAlgebra S E q
  rw [originalBranchFractionAlgebra_algebraMap, originalBranchFractionAlgebra_algebraMap]

end SpecifiedOriginalFractionField

section LocalBranches

variable (R : Type uR) (S : Type uS) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [DecidableEq (Ideal S)]
  (q : IdealBranch ((maximalIdeal R).map (algebraMap R S)))

local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "Dq" => BranchCompletion (Ideal.map (algebraMap R S) (maximalIdeal R)) q

example : IsDiscreteValuationRing Dq := inferInstance

example : Function.Injective (algebraMap S Dq) :=
  branchCompletion_algebraMap_injective _ q

-- Both finiteness and torsion-freeness are deliberately absent here.
example :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    IsLocalHom (algebraMap Rhat Dq) :=
  localCompletionBase_isLocalHom R S q

example {π : R} (hπ : Irreducible π) :
    ¬ IsUnit (algebraMap S Dq (algebraMap R S π)) :=
  branchCompletion_uniformizer_not_isUnit R S hπ q

variable [Module.IsTorsionFree R S]

-- Finiteness is still absent from the injectivity and native fraction-action tests.
example :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    Function.Injective (algebraMap Rhat Dq) :=
  localCompletionBase_injective R S q

example :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    FaithfulSMul Rhat Dq :=
  localCompletionBaseFaithfulSMul R S q

example {π : R} (hπ : Irreducible π) :
    algebraMap S Dq (algebraMap R S π) ≠ 0 ∧
      ¬ IsUnit (algebraMap S Dq (algebraMap R S π)) :=
  ⟨branchCompletion_uniformizer_ne_zero R S hπ q,
    branchCompletion_uniformizer_not_isUnit R S hπ q⟩

example (x y : Rhat) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    letI := localCompletionFractionAlgebra R S q
    algebraMap (FractionRing Rhat) (FractionRing Dq)
        (algebraMap Rhat (FractionRing Rhat) x /
          algebraMap Rhat (FractionRing Rhat) y) =
      algebraMap Dq (FractionRing Dq) (localCompletionBaseMap (maximalIdeal R) q x) /
        algebraMap Dq (FractionRing Dq) (localCompletionBaseMap (maximalIdeal R) q y) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  let := localCompletionFractionAlgebra R S q
  rw [map_div₀, localCompletionFractionAlgebra_algebraMap,
    localCompletionFractionAlgebra_algebraMap]

example [Module.Finite R S] :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    letI := localCompletionFractionAlgebra R S q
    Module.Finite (FractionRing Rhat) (FractionRing Dq) :=
  localCompletionFractionFinite R S q

end LocalBranches

section FullFractionTensor

variable (R : Type uR) (S : Type uS) (F : Type uF) (E : Type uE)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E]

local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "Khat" => FractionRing Rhat
local notation "D" => fun q : IdealBranch J => BranchCompletion J q
local notation "C" => fun q : IdealBranch J => FractionRing (D q)

-- Neither a nonzero-ideal witness nor a chosen uniformizer is an input.
example :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    Khat ⊗[F] E ≃ₐ[Khat] ∀ q : IdealBranch J, C q :=
  fractionTensorEquivLocalFractionFields R S F E

example (b : Khat) (s : S) (q : IdealBranch J) :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    fractionTensorEquivLocalFractionFields R S F E (b ⊗ₜ[F] algebraMap S E s) q =
      algebraMap Khat (C q) b *
        algebraMap (D q) (C q)
          (algebraMap (Localization.AtPrime q.val) (D q)
            (algebraMap S (Localization.AtPrime q.val) s)) := by
  let := fractionCompletionAlgebra R F
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionFractionAlgebra R S q
  rw [fractionTensorEquivLocalFractionFields_tmul,
    fractionTensorEquivLocalFractionFields_one_tmul]

example (b : Khat) (s t : S) (q : IdealBranch J) :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    fractionTensorEquivLocalFractionFields R S F E
        (b ⊗ₜ[F] (algebraMap S E s / algebraMap S E t)) q =
      algebraMap Khat (C q) b *
        (algebraMap (D q) (C q) (algebraMap S (D q) s) /
          algebraMap (D q) (C q) (algebraMap S (D q) t)) := by
  let := fractionCompletionAlgebra R F
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionFractionAlgebra R S q
  rw [fractionTensorEquivLocalFractionFields_tmul,
    fractionTensorEquivLocalFractionFields_one_tmul_div]

example (s : S) (q : IdealBranch J) :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    fractionTensorEquivLocalFractionFields R S F E
      (1 ⊗ₜ[F] (algebraMap S E s / algebraMap S E (0 : S))) q = 0 := by
  let := fractionCompletionAlgebra R F
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionFractionAlgebra R S q
  simp

-- Compare ring homomorphisms, not merely the existence of isomorphic field factors.
example (q : IdealBranch J) :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    letI := originalBranchFractionAlgebra S E q
    letI := originalBranchIsFractionRing S E q
    (Pi.evalRingHom C q).comp
        ((fractionTensorEquivLocalFractionFields R S F E).toRingHom.comp
          (Algebra.TensorProduct.includeRight : E →ₐ[F] Khat ⊗[F] E).toRingHom) =
      IsFractionRing.lift (K := E)
        (fraction_algebraMap_injective (Localization.AtPrime q.val)) :=
  fractionTensorEquivLocalFractionFields_coordinate R S F E q

example :
    letI := fractionCompletionAlgebra R F
    letI := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
    letI := fun q => localCompletionFractionAlgebra R S q
    ∀ (f g : Khat ⊗[F] E →ₐ[Khat] ∀ q : IdealBranch J, C q),
      (∀ (s : S) (q : IdealBranch J), f (1 ⊗ₜ[F] algebraMap S E s) q =
        algebraMap (D q) (C q) (algebraMap (Localization.AtPrime q.val) (D q)
          (algebraMap S (Localization.AtPrime q.val) s))) →
      (∀ (s : S) (q : IdealBranch J), g (1 ⊗ₜ[F] algebraMap S E s) q =
        algebraMap (D q) (C q) (algebraMap (Localization.AtPrime q.val) (D q)
          (algebraMap S (Localization.AtPrime q.val) s))) →
      f = g := by
  let := fractionCompletionAlgebra R F
  let := fun q => localCompletionBaseAlgebra (S := S) (maximalIdeal R) q
  let := fun q => localCompletionFractionAlgebra R S q
  intro f g hf hg
  rw [fractionTensorEquivLocalFractionFields_unique R S F E f hf,
    fractionTensorEquivLocalFractionFields_unique R S F E g hg]

end FullFractionTensor

end AdicCompletion
