/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjective
public import Colib.LinearAlgebra.Matrix.RightLinear
public import Mathlib.RingTheory.Finiteness.Projective

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/Aglib/Algebra/Category/ModuleCat/IdempotentMatrix.lean`.
The original hypotheses and maps are retained.

# Idempotent matrices and actual finite projective right modules

The image of an idempotent matrix on the right free module has an explicit
inclusion and retraction, so is finite projective over the opposite ring.
Conversely every finite projective right module is linearly isomorphic to one
of these actual images. Neither commutativity nor invariant basis number is
required. This supplies the object-level bridge for a Karoubi-envelope model.
-/
@[expose] public section

noncomputable section

universe u

namespace Matrix.RightModule

variable {R : Type u} [Ring R] {n : ℕ}

/-- The inclusion and the original idempotent restricted to its image split. -/
lemma rangeRestrict_comp_subtype (A : Matrix (Fin n) (Fin n) R) (hA : A * A = A) :
    (linearMap A).rangeRestrict.comp (linearMap A).range.subtype = LinearMap.id := by
  have hp : (linearMap A).comp (linearMap A) = linearMap A := by
    rw [← linearMap_mul, hA]
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change linearMap A x.val = x.val
  rw [← hy]
  exact DFunLike.congr_fun hp y

instance image_finite (A : Matrix (Fin n) (Fin n) R) :
    Module.Finite Rᵐᵒᵖ (linearMap A).range :=
  Module.Finite.of_surjective (linearMap A).rangeRestrict
    (linearMap A).surjective_rangeRestrict

/-- Idempotency gives projectivity of the actual image by an explicit split retraction. -/
lemma image_projective (A : Matrix (Fin n) (Fin n) R) (hA : A * A = A) :
    Module.Projective Rᵐᵒᵖ (linearMap A).range :=
  Module.Projective.of_split (linearMap A).range.subtype (linearMap A).rangeRestrict
    (rangeRestrict_comp_subtype A hA)

/-- The genuine image, packaged in the existing finite projective right-module category. -/
def image (A : Matrix (Fin n) (Fin n) R) (hA : A * A = A) :
    ModuleCat.FiniteProjective.Category.{u, u} Rᵐᵒᵖ :=
  ⟨ModuleCat.of Rᵐᵒᵖ (linearMap A).range, inferInstance, image_projective A hA⟩

/-- Every finite projective right module is the image of an actual finite idempotent matrix. -/
theorem exists_idempotent_image (M : ModuleCat.{u} Rᵐᵒᵖ)
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M] :
    ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) R),
      A * A = A ∧ Nonempty (M ≃ₗ[Rᵐᵒᵖ] (linearMap A).range) := by
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective Rᵐᵒᵖ M
  let e : (Fin n → R) ≃ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ) :=
    LinearEquiv.piCongrRight fun _ => MulOpposite.opLinearEquiv Rᵐᵒᵖ
  let f' := f.comp e.toLinearMap
  let g' := e.symm.toLinearMap.comp g
  have hfg' : f'.comp g' = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change f (e (e.symm (g x))) = x
    rw [e.apply_symm_apply]
    exact DFunLike.congr_fun hfg x
  let p := g'.comp f'
  have hp : p.comp p = p := by
    apply LinearMap.ext
    intro x
    change g' (f' (g' (f' x))) = g' (f' x)
    exact congrArg g' (DFunLike.congr_fun hfg' (f' x))
  let A := ofLinearMap p
  have hAp : linearMap A = p := linearMap_ofLinearMap p
  have hA : A * A = A := by
    apply equiv.injective
    change linearMap (A * A) = linearMap A
    rw [linearMap_mul, hAp]
    exact hp
  refine ⟨n, A, hA, ⟨{
    toFun := fun x => ⟨g' x, ?_⟩
    invFun := fun x => f' x.val
    left_inv := fun x => DFunLike.congr_fun hfg' x
    right_inv := ?_
    map_add' := fun x y => Subtype.ext (map_add g' x y)
    map_smul' := fun a x => Subtype.ext (map_smul g' a x) }⟩⟩
  · refine ⟨g' x, ?_⟩
    rw [hAp]
    exact congrArg g' (DFunLike.congr_fun hfg' x)
  · intro x
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change p x.val = x.val
    rw [← hy, hAp]
    exact DFunLike.congr_fun hp y

end Matrix.RightModule
