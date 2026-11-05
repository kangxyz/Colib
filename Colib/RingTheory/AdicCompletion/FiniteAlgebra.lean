/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap
public import StacksFrontier.RingTheory.AdicCompletion.OfTensorProductBijective
public import StacksFrontier.RingTheory.AdicCompletion.QuotEquivMapPow
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Completion of finite algebras as an actual algebra tensor product

For an arbitrary algebra `R → S` and ideal `I` of `R`, the canonical comparison
`AdicCompletion I R ⊗[R] S → AdicCompletion (I.map (algebraMap R S)) S` sends
`x ⊗ s` to `completionMap I x * algebraMap S _ s`. Its definition and its
compatibility with evaluation require neither Noetherianity nor finiteness.

When `R` is Noetherian and `S` is finite as an `R`-module, the comparison is an
algebra equivalence, both over `R` and over `AdicCompletion I R`. The latter action
is defined directly by `completionMap`, independently of the tensor comparison.
The ring universes remain independent.

The proof compares the actual algebra map with the public module comparison
`ofTensorProduct` through `adicCompletionLinearEquivMap`. No inverse-limit model
or alternative completion object is introduced.

## Source provenance

This adapts `Aglib/RingTheory/AdicCompletion/FiniteAlgebra.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`26e77744fd7d6f7f851523806a90df335c94bc7db607680bfbd73c684b1641df`.
Its original module is `Motivic.Aglib.RingTheory.AdicCompletion.FiniteAlgebra`,
recorded in Aglib's `docs/migration/motivic-milnor-k.json`.

The comparison with the module tensor map adapts the argument in
`StacksFrontier/RingTheory/AdicCompletion/FiniteAlgebra.lean`, lines 745–807,
at Stacks revision `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.
Only its public lower interfaces are imported; the private `ofTensorAlgHom`
and the finite-local-algebra application module are not dependencies.
The finite-module input is the arbitrary-universe form of EGA 0, 7.7.8
provided by `AdicCompletion.bijective_ofTensorProduct`.

Pinned Mathlib revision: `16edf57de7933555826307a3d81b4391a3657a09`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace AdicCompletion

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal R)

/-- The algebra completion map is the completion map of the underlying ring map.
This identifies the canonical maps before using ring-map functoriality. -/
theorem completionMap_toRingHom :
    (completionMap (B := S) I).toRingHom =
      adicCompletionMap (algebraMap R S) I (I.map (algebraMap R S)) le_rfl := by
  apply RingHom.ext
  intro x
  apply ext_evalₐ
  intro n
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  change evalₐ (I.map (algebraMap R S)) n (completionMap (B := S) I x) = _
  rw [evalₐ_completionMap (B := S) I n x r hr.symm, adicCompletionMap_evalₐ, ← hr]
  rfl

/-- The actual tensor-to-completion algebra map for an arbitrary algebra.
No Noetherian or finite-module hypothesis is needed. -/
@[colib_tag "COL-0185",
  colib_ref "aglib_principal_euler_pin" "RingTheory/AdicCompletion/FiniteAlgebra.lean"
    "adaptation" "Canonical maps and actual completions; native lower interfaces"]
def tensorToExtendedCompletionAlgHom :
    AdicCompletion I R ⊗[R] S →ₐ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  Algebra.TensorProduct.lift (completionMap (B := S) I)
    ({ algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) with
      commutes' := fun _ ↦ rfl } :
      S →ₐ[R] AdicCompletion (I.map (algebraMap R S)) S)
    (fun _ _ ↦ Commute.all _ _)

/-- The tensor comparison multiplies the completed base coefficient by the image
of the algebra coefficient. -/
@[simp]
theorem tensorToExtendedCompletionAlgHom_tmul (x : AdicCompletion I R) (s : S) :
    tensorToExtendedCompletionAlgHom I (x ⊗ₜ[R] s) =
      completionMap (B := S) I x *
        algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s := rfl

/-- The tensor comparison fixes the coefficients from `S`. -/
theorem tensorToExtendedCompletionAlgHom_one_tmul (s : S) :
    tensorToExtendedCompletionAlgHom I (1 ⊗ₜ[R] s) =
      algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s := by
  simp

/-- The tensor comparison restricts to `completionMap` on the completed base. -/
theorem tensorToExtendedCompletionAlgHom_tmul_one (x : AdicCompletion I R) :
    tensorToExtendedCompletionAlgHom (S := S) I (x ⊗ₜ[R] 1) =
      completionMap (B := S) I x := by
  simp

/-- At level `n`, the tensor comparison is the product of the level map from the
completed base with reduction of the coefficient from `S`. -/
theorem evalₐ_tensorToExtendedCompletionAlgHom_tmul (n : ℕ)
    (x : AdicCompletion I R) (s : S) :
    evalₐ (I.map (algebraMap R S)) n
        (tensorToExtendedCompletionAlgHom I (x ⊗ₜ[R] s)) =
      completionLevel (B := S) I n x *
        Ideal.Quotient.mk ((I.map (algebraMap R S)) ^ n) s := by
  rw [tensorToExtendedCompletionAlgHom_tmul, map_mul]
  simp [completionMap]

/-- If `r` represents the completed base coefficient at level `n`, the tensor
comparison is represented by `algebraMap R S r * s` at that level. -/
theorem evalₐ_tensorToExtendedCompletionAlgHom_tmul_eq_mk (n : ℕ)
    (x : AdicCompletion I R) (r : R) (s : S)
    (hr : evalₐ I n x = Ideal.Quotient.mk (I ^ n) r) :
    evalₐ (I.map (algebraMap R S)) n
        (tensorToExtendedCompletionAlgHom I (x ⊗ₜ[R] s)) =
      Ideal.Quotient.mk ((I.map (algebraMap R S)) ^ n) (algebraMap R S r * s) := by
  rw [tensorToExtendedCompletionAlgHom_tmul, map_mul, evalₐ_completionMap I n x r hr]
  simp

/-- The action of the completed base is induced by `completionMap` itself. This is
an explicit local algebra structure rather than an additional global instance. -/
@[instance_reducible]
def extendedCompletionAlgebra :
    Algebra (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R S)) S) :=
  (completionMap (B := S) I).toRingHom.toAlgebra

/-- With the canonical completed-base action, its algebra map is `completionMap`. -/
@[simp]
theorem extendedCompletionAlgebra_algebraMap (x : AdicCompletion I R) :
    letI := extendedCompletionAlgebra (S := S) I
    algebraMap (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R S)) S) x =
      completionMap (B := S) I x := rfl

/-- The canonical completed-base action extends the original `R`-action. -/
theorem extendedCompletionAlgebra_isScalarTower :
    letI := extendedCompletionAlgebra (S := S) I
    IsScalarTower R (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R S)) S) := by
  let := extendedCompletionAlgebra (S := S) I
  exact IsScalarTower.of_algebraMap_eq fun r ↦ ((completionMap (B := S) I).commutes r).symm

/-- The public module-to-ring completion comparison identifies the action of a
completed base coefficient on an integral coefficient with their product. -/
theorem adicCompletionLinearEquivMap_smul_of (x : AdicCompletion I R) (s : S) :
    adicCompletionLinearEquivMap I S (x • of I S s) =
      completionMap (B := S) I x *
        algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s := by
  refine Subtype.ext (funext fun n ↦ ?_)
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective (I ^ n • (⊤ : Submodule R R)) (x.val n)
  have hrs : r • s = algebraMap R S r * s := Algebra.smul_def r s
  have hL : (x • of I S s).val n =
      Submodule.Quotient.mk (algebraMap R S r * s) := by
    rw [smul_eval, ← hr, ← hrs]
    rfl
  have hR : (completionMap (B := S) I x).val n =
      Submodule.Quotient.mk (algebraMap R S r) :=
    val_completionMap I n x r hr.symm
  have hs : (algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s).val n =
      Submodule.Quotient.mk s := rfl
  rw [adicCompletionLinearEquivMap_val, hL, quotEquivMapPow_mk, val_mul, hR, hs]
  rfl

/-- The algebra comparison is the actual public module tensor comparison followed
by the public identification of module and extended-ideal completions. -/
theorem tensorToExtendedCompletionAlgHom_toLinearMap :
    (tensorToExtendedCompletionAlgHom (S := S) I).toLinearMap =
      (adicCompletionLinearEquivMap I S).toLinearMap.comp
        ((ofTensorProduct I S).restrictScalars R) := by
  apply TensorProduct.ext'
  intro x s
  change tensorToExtendedCompletionAlgHom I (x ⊗ₜ[R] s) =
    adicCompletionLinearEquivMap I S (x • of I S s)
  rw [tensorToExtendedCompletionAlgHom_tmul, adicCompletionLinearEquivMap_smul_of]

/-- The underlying linear map of the canonical tensor-to-completion algebra map. -/
def tensorToExtendedCompletion :
    AdicCompletion I R ⊗[R] S →ₗ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  (tensorToExtendedCompletionAlgHom I).toLinearMap

/-- The underlying linear comparison fixes the coefficients from `S`. -/
@[simp]
theorem tensorToExtendedCompletion_one_tmul (s : S) :
    tensorToExtendedCompletion I (1 ⊗ₜ[R] s) =
      algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s :=
  tensorToExtendedCompletionAlgHom_one_tmul I s

section Finite

variable [IsNoetherianRing R] [Module.Finite R S]

/-- For a finite algebra over a Noetherian ring, the actual tensor-to-completion
algebra map is bijective. The algebra and base may live in different universes. -/
@[ega "0 7.3.3" "finite algebra case", ega "0 7.7.8" "B = Â"]
theorem bijective_tensorToExtendedCompletionAlgHom :
    Function.Bijective (tensorToExtendedCompletionAlgHom (S := S) I) := by
  have hfun : ⇑(tensorToExtendedCompletionAlgHom (S := S) I) =
      ⇑(adicCompletionLinearEquivMap I S) ∘ ⇑(ofTensorProduct I S) := by
    funext z
    exact LinearMap.congr_fun (tensorToExtendedCompletionAlgHom_toLinearMap (S := S) I) z
  rw [hfun]
  exact (adicCompletionLinearEquivMap I S).bijective.comp (bijective_ofTensorProduct I S)

/-- Completion of a finite algebra over a Noetherian ring is the actual base-change
tensor product, as an `R`-algebra. -/
@[colib_tag "COL-0185"]
def tensorEquivExtendedCompletion :
    AdicCompletion I R ⊗[R] S ≃ₐ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  AlgEquiv.ofBijective (tensorToExtendedCompletionAlgHom I)
    (bijective_tensorToExtendedCompletionAlgHom I)

/-- The finite-algebra equivalence uses the canonical tensor comparison. -/
@[simp]
theorem tensorEquivExtendedCompletion_apply (z : AdicCompletion I R ⊗[R] S) :
    tensorEquivExtendedCompletion I z = tensorToExtendedCompletionAlgHom I z := rfl

/-- The finite-algebra equivalence has the canonical pure-tensor formula. -/
@[simp]
theorem tensorEquivExtendedCompletion_tmul (x : AdicCompletion I R) (s : S) :
    tensorEquivExtendedCompletion I (x ⊗ₜ[R] s) =
      completionMap (B := S) I x *
        algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s := rfl

/-- The finite-algebra equivalence fixes the coefficients from `S`. -/
theorem tensorEquivExtendedCompletion_one_tmul (s : S) :
    tensorEquivExtendedCompletion I (1 ⊗ₜ[R] s) =
      algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s := by
  simp

/-- The finite-algebra equivalence restricts to `completionMap` on the completed base. -/
theorem tensorEquivExtendedCompletion_tmul_one (x : AdicCompletion I R) :
    tensorEquivExtendedCompletion (S := S) I (x ⊗ₜ[R] 1) =
      completionMap (B := S) I x := by
  simp

/-- The same canonical equivalence over the completed base, whose target action is
defined directly by `completionMap`. -/
@[colib_tag "COL-0185"]
def tensorEquivExtendedCompletionBase :
    letI := extendedCompletionAlgebra (S := S) I
    AdicCompletion I R ⊗[R] S ≃ₐ[AdicCompletion I R]
      AdicCompletion (I.map (algebraMap R S)) S := by
  letI := extendedCompletionAlgebra (S := S) I
  refine AlgEquiv.ofRingEquiv (f := (tensorEquivExtendedCompletion (S := S) I).toRingEquiv) ?_
  intro x
  change tensorEquivExtendedCompletion I (x ⊗ₜ[R] 1) = completionMap (B := S) I x
  exact tensorEquivExtendedCompletion_tmul_one I x

/-- Changing the scalar ring does not change the underlying comparison map. -/
@[simp]
theorem tensorEquivExtendedCompletionBase_apply (z : AdicCompletion I R ⊗[R] S) :
    letI := extendedCompletionAlgebra (S := S) I
    tensorEquivExtendedCompletionBase I z = tensorToExtendedCompletionAlgHom I z := rfl

end Finite

end AdicCompletion
