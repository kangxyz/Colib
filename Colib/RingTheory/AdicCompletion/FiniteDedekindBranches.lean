/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.DedekindBranches
public import Colib.RingTheory.AdicCompletion.FiniteAlgebra
public import Colib.Util.References

/-!
# Finite-algebra tensor products and actual completed Dedekind branches

The finite algebra tensor product is identified with all local completions at the actual
normalized factors of the extended ideal. The action of the completed base is specified by
the native map on completions, before constructing the tensor equivalence.

Adapted from `Aglib/RingTheory/AdicCompletion/FiniteDedekindBranches.lean` and
`Aglib/RingTheory/AdicCompletion/LocalCompletionsBase.lean`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. Ring and algebra universes are independent.
No flatness, torsion-freeness, or nonzero base-ideal premise is added: the hypothesis concerns
the actual extended ideal. There is no fraction-field or Milnor-norm assertion in this file.
-/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing
open scoped TensorProduct

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [DecidableEq (Ideal S)]

/-- The original base ideal maps into the maximal ideal of every actual branch. -/
theorem idealBranch_base_map_le_maximalIdeal (I : Ideal R)
    (q : IdealBranch (I.map (algebraMap R S))) :
    I.map (algebraMap R (Localization.AtPrime q.val)) ≤
      maximalIdeal (Localization.AtPrime q.val) := by
  rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.val), ← Ideal.map_map]
  exact idealBranch_map_le_maximalIdeal (I.map (algebraMap R S)) q

/-- The actual canonical map from the completed base to one completed local branch. -/
@[colib_tag "COL-0189",
  colib_ref "aglib_principal_euler_pin" "RingTheory/AdicCompletion/FiniteDedekindBranches.lean"
    "adaptation" "Canonical maps and actual completions; native lower interfaces"]
def localCompletionBaseMap (I : Ideal R)
    (q : IdealBranch (I.map (algebraMap R S))) :
    AdicCompletion I R →ₐ[R]
      AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
        (Localization.AtPrime q.val) where
  __ := adicCompletionMap (algebraMap R (Localization.AtPrime q.val)) I
    (maximalIdeal (Localization.AtPrime q.val)) (idealBranch_base_map_le_maximalIdeal I q)
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime q.val)
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.val)) (Localization.AtPrime q.val))]
    exact DFunLike.congr_fun (adicCompletionMap_comp_algebraMap
      (algebraMap R (Localization.AtPrime q.val)) I
      (maximalIdeal (Localization.AtPrime q.val)) (idealBranch_base_map_le_maximalIdeal I q)) r

/-- The completed-base action comes from the canonical map, not from a chosen inverse. -/
@[instance_reducible]
def localCompletionBaseAlgebra (I : Ideal R)
    (q : IdealBranch (I.map (algebraMap R S))) :
    Algebra (AdicCompletion I R)
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
        (Localization.AtPrime q.val)) :=
  (localCompletionBaseMap I q).toRingHom.toAlgebra

/-- This canonical action is compatible with the original base-ring action. -/
theorem localCompletionBaseIsScalarTower (I : Ideal R)
    (q : IdealBranch (I.map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra I q
    IsScalarTower R (AdicCompletion I R)
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
        (Localization.AtPrime q.val)) := by
  let := localCompletionBaseAlgebra I q
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact ((localCompletionBaseMap I q).commutes r).symm

/-- Every branch action has its original quotient map at every precision. -/
theorem eval_localCompletionBaseMap (I : Ideal R)
    (q : IdealBranch (I.map (algebraMap R S))) (n : ℕ) (x : AdicCompletion I R) :
    evalₐ (maximalIdeal (Localization.AtPrime q.val)) n (localCompletionBaseMap I q x) =
      Ideal.quotientMap ((maximalIdeal (Localization.AtPrime q.val)) ^ n)
        (algebraMap R (Localization.AtPrime q.val))
        (Ideal.map_le_iff_le_comap.mp (by
          rw [Ideal.map_pow]
          exact Ideal.pow_right_mono (idealBranch_base_map_le_maximalIdeal I q) n))
        (evalₐ I n x) :=
  adicCompletionMap_evalₐ _ _ _ (idealBranch_base_map_le_maximalIdeal I q) n x

/-- Decomposing the extended-ideal completion preserves the original completed-base map. -/
theorem dedekindBranchesAlgEquiv_completionMap (I : Ideal R)
    (hI : I.map (algebraMap R S) ≠ 0) (x : AdicCompletion I R)
    (q : IdealBranch (I.map (algebraMap R S))) :
    dedekindBranchesAlgEquiv (I.map (algebraMap R S)) hI (completionMap I x) q =
      localCompletionBaseMap I q x := by
  rw [dedekindBranchesAlgEquiv_apply]
  change adicCompletionMap (algebraMap S (Localization.AtPrime q.val))
      (I.map (algebraMap R S)) (maximalIdeal (Localization.AtPrime q.val))
      (idealBranch_map_le_maximalIdeal (I.map (algebraMap R S)) q)
      ((completionMap (B := S) I).toRingHom x) = _
  rw [completionMap_toRingHom]
  have hcomp := Rig.adicCompletionMap_comp (algebraMap R S)
    (algebraMap S (Localization.AtPrime q.val)) I (I.map (algebraMap R S))
    (maximalIdeal (Localization.AtPrime q.val)) le_rfl
    (idealBranch_map_le_maximalIdeal (I.map (algebraMap R S)) q)
    (by
      rw [← IsScalarTower.algebraMap_eq R S (Localization.AtPrime q.val)]
      exact idealBranch_base_map_le_maximalIdeal I q)
  change adicCompletionMap (algebraMap S (Localization.AtPrime q.val))
      (I.map (algebraMap R S)) (maximalIdeal (Localization.AtPrime q.val))
      (idealBranch_map_le_maximalIdeal (I.map (algebraMap R S)) q)
      (adicCompletionMap (algebraMap R S) I (I.map (algebraMap R S)) le_rfl x) =
    adicCompletionMap (algebraMap R (Localization.AtPrime q.val)) I
      (maximalIdeal (Localization.AtPrime q.val)) (idealBranch_base_map_le_maximalIdeal I q) x
  simpa only [RingHom.comp_apply, ← IsScalarTower.algebraMap_eq]
    using DFunLike.congr_fun hcomp x

variable [IsNoetherianRing R] [Module.Finite R S]

/-- The full tensor decomposition over every actual prime factor of the extended ideal. -/
@[colib_tag "COL-0189"]
def tensorEquivLocalCompletions (I : Ideal R) (hI : I.map (algebraMap R S) ≠ 0) :
    AdicCompletion I R ⊗[R] S ≃ₐ[R]
      ∀ q : IdealBranch (I.map (algebraMap R S)),
        AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
          (Localization.AtPrime q.val) :=
  (tensorEquivExtendedCompletion I).trans
    ((dedekindBranchesAlgEquiv (I.map (algebraMap R S)) hI).restrictScalars R)

/-- Every pure tensor enters a branch by the two specified canonical maps. -/
theorem tensorEquivLocalCompletions_tmul (I : Ideal R)
    (hI : I.map (algebraMap R S) ≠ 0) (x : AdicCompletion I R) (s : S)
    (q : IdealBranch (I.map (algebraMap R S))) :
    tensorEquivLocalCompletions I hI (x ⊗ₜ[R] s) q =
      localCompletionBaseMap I q x *
        algebraMap (Localization.AtPrime q.val)
          (AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
            (Localization.AtPrime q.val)) (algebraMap S (Localization.AtPrime q.val) s) := by
  simp only [tensorEquivLocalCompletions, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, tensorEquivExtendedCompletion_tmul, map_mul, Pi.mul_apply,
    dedekindBranchesAlgEquiv_completionMap, dedekindBranchesAlgEquiv_algebraMap]

/-- The original algebra element enters every actual local completion by its native maps. -/
@[simp]
theorem tensorEquivLocalCompletions_one_tmul (I : Ideal R)
    (hI : I.map (algebraMap R S) ≠ 0) (s : S)
    (q : IdealBranch (I.map (algebraMap R S))) :
    tensorEquivLocalCompletions I hI (1 ⊗ₜ[R] s) q =
      algebraMap (Localization.AtPrime q.val)
        (AdicCompletion (maximalIdeal (Localization.AtPrime q.val)) (Localization.AtPrime q.val))
        (algebraMap S (Localization.AtPrime q.val) s) := by
  rw [tensorEquivLocalCompletions_tmul, map_one, one_mul]

/-- The tensor identification is an equivalence over the actual completed base. -/
@[colib_tag "COL-0189"]
def tensorEquivLocalCompletionsBase (I : Ideal R) (hI : I.map (algebraMap R S) ≠ 0) :
    letI := fun q ↦ localCompletionBaseAlgebra (S := S) I q
    AdicCompletion I R ⊗[R] S ≃ₐ[AdicCompletion I R]
      ∀ q : IdealBranch (I.map (algebraMap R S)),
        AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
          (Localization.AtPrime q.val) := by
  let := fun q ↦ localCompletionBaseAlgebra (S := S) I q
  refine AlgEquiv.ofRingEquiv (f := (tensorEquivLocalCompletions I hI).toRingEquiv) ?_
  intro x
  funext q
  change tensorEquivLocalCompletions I hI (x ⊗ₜ[R] (1 : S)) q = localCompletionBaseMap I q x
  rw [tensorEquivLocalCompletions_tmul, map_one, map_one, mul_one]

/-- Each actual completed branch is finite over the canonical completed-base algebra. -/
@[colib_tag "COL-0189"]
theorem localCompletionBaseFinite (I : Ideal R) (hI : I.map (algebraMap R S) ≠ 0)
    (q : IdealBranch (I.map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra I q
    Module.Finite (AdicCompletion I R)
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
        (Localization.AtPrime q.val)) := by
  let := fun q ↦ localCompletionBaseAlgebra (S := S) I q
  have := Module.Finite.of_surjective
    (tensorEquivLocalCompletionsBase I hI).toLinearMap
    (tensorEquivLocalCompletionsBase I hI).surjective
  exact Module.Finite.of_pi (R := AdicCompletion I R)
    (fun q : IdealBranch (I.map (algebraMap R S)) ↦
      AdicCompletion (maximalIdeal (Localization.AtPrime q.val))
        (Localization.AtPrime q.val)) q

end AdicCompletion
