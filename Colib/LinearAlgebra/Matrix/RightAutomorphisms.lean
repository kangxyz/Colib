/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.RightLinear
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveComplement

/-!
Implementation provenance: `Quillen/Aglib/LinearAlgebra/Matrix/RightAutomorphisms.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Matrix units as automorphisms of finite free right modules

The finite matrix group acts on the actual finite free module over the opposite
ring. Entrywise opposition transports ordinary matrix multiplication on right
column vectors to the library's chosen free object. The concrete stabilization
square identifies `diag(g,1)` with the actual right rank-one biproduct action.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits
open scoped Matrix

namespace Matrix.RightModule

variable (R : Type u) [Ring R]

/-- Entrywise opposition identifies right columns with the chosen free opposite-ring module. -/
def columnsEquiv (n : ℕ) : (Fin n → R) ≃ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ) :=
  LinearEquiv.piCongrRight fun _ => MulOpposite.opLinearEquiv Rᵐᵒᵖ

/-- The actual module underlying the chosen finite free right-module object. -/
abbrev freeModule (n : ℕ) : ModuleCat Rᵐᵒᵖ :=
  (ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n).obj

/-- Matrices identify with endomorphisms of the library's actual finite free right module. -/
def freeEndRingEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) R ≃+* End (freeModule R n) :=
  ((endRingEquiv.trans (LinearEquiv.conjRingEquiv (columnsEquiv R n))).trans
    (ModuleCat.endRingEquiv (freeModule R n)).symm)

/-- Matrix units identify with actual module-category automorphisms. -/
def moduleAutEquiv (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R ≃* Aut (freeModule R n) :=
  (Units.mapEquiv (freeEndRingEquiv R n).toMulEquiv).trans (Aut.unitsEndEquivAut _)

/-- The identification is ordinary matrix multiplication on right column vectors. -/
@[simp] lemma moduleAutEquiv_hom_apply (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (x : Fin n → Rᵐᵒᵖ) (i : Fin n) :
    (moduleAutEquiv R n g).hom x i =
      MulOpposite.op ((g.val *ᵥ fun j => MulOpposite.unop (x j)) i) := rfl

/-- The same identification in the actual finite projective category. -/
def freeAutEquiv (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R ≃*
    Aut (ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n) :=
  let h := Functor.FullyFaithful.ofFullyFaithful (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι
  (moduleAutEquiv R n).trans
    (h.autMulEquivOfFullyFaithful (ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n)).symm


/-- Inclusion of the finite projective category retains the concrete matrix automorphism. -/
@[simp] lemma freeAutEquiv_map (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι.mapIso (freeAutEquiv R n g) =
      moduleAutEquiv R n g := by
  let h := Functor.FullyFaithful.ofFullyFaithful (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι
  exact (h.autMulEquivOfFullyFaithful
    (ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n)).apply_symm_apply _


/-- Stabilization acts by the original automorphism on the first coordinates. -/
lemma moduleAutEquiv_step_castSucc (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (x : Fin (n + 1) → Rᵐᵒᵖ) (i : Fin n) :
    (moduleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom x i.castSucc =
      (moduleAutEquiv R n g).hom (fun j => x j.castSucc) i := by
  simp [moduleAutEquiv_hom_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

/-- Stabilization fixes the added final coordinate. -/
lemma moduleAutEquiv_step_last (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (x : Fin (n + 1) → Rᵐᵒᵖ) :
    (moduleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom x (Fin.last n) =
      x (Fin.last n) := by
  simp [moduleAutEquiv_hom_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

/-- Split off the final rank-one coordinate, in the order used by matrix stabilization. -/
def splitLast (n : ℕ) : (Fin (n + 1) → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ]
    (Fin n → Rᵐᵒᵖ) × (Fin 1 → Rᵐᵒᵖ) where
  toFun x := (fun i => x i.castSucc, fun _ => x (Fin.last n))
  invFun x := Fin.snoc x.1 (x.2 0)
  left_inv x := by ext i; cases i using Fin.lastCases <;> simp
  right_inv x := by
    apply Prod.ext
    · ext i; simp
    · ext i; simp [Subsingleton.elim i (0 : Fin 1)]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Stabilization is the actual direct-product action, with identity on the new free summand. -/
lemma splitLast_stabilization (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (x : Fin (n + 1) → Rᵐᵒᵖ) :
    splitLast R n ((moduleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom x) =
      ((moduleAutEquiv R n g).hom (splitLast R n x).1, (splitLast R n x).2) := by
  apply Prod.ext
  · ext i
    exact moduleAutEquiv_step_castSucc R n g x i
  · ext i
    exact moduleAutEquiv_step_last R n g x

/-- The actual rank-one right direct-sum isomorphism in the module category. -/
def appendIso (n : ℕ) : freeModule R n ⊞ freeModule R 1 ≅ freeModule R (n + 1) :=
  ModuleCat.biprodIsoProd _ _ ≪≫ (splitLast R n).symm.toModuleIso

@[simp] lemma appendIso_inv_fst (n : ℕ) :
    (appendIso R n).inv ≫ biprod.fst =
      ModuleCat.ofHom ((LinearMap.fst Rᵐᵒᵖ _ _).comp (splitLast R n).toLinearMap) := by
  simp only [appendIso, Iso.trans_inv, Category.assoc,
    ModuleCat.biprodIsoProd_inv_comp_fst]
  rfl

@[simp] lemma appendIso_inv_snd (n : ℕ) :
    (appendIso R n).inv ≫ biprod.snd =
      ModuleCat.ofHom ((LinearMap.snd Rᵐᵒᵖ _ _).comp (splitLast R n).toLinearMap) := by
  simp only [appendIso, Iso.trans_inv, Category.assoc,
    ModuleCat.biprodIsoProd_inv_comp_snd]
  rfl

/-- The matrix stabilization square is the actual categorical rank-one direct-sum square. -/
lemma moduleAutEquiv_stabilization (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (moduleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom ≫ (appendIso R n).inv =
      (appendIso R n).inv ≫ biprod.map (moduleAutEquiv R n g).hom (𝟙 (freeModule R 1)) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst]
    rw [appendIso_inv_fst, ← Category.assoc, appendIso_inv_fst]
    ext x
    funext i
    exact moduleAutEquiv_step_castSucc R n g x i
  · simp only [Category.assoc, biprod.map_snd, Category.comp_id]
    rw [appendIso_inv_snd]
    ext x
    funext i
    exact moduleAutEquiv_step_last R n g x

/-- The entire stabilized automorphism is the conjugate of the actual direct-sum automorphism. -/
lemma moduleAutEquiv_step (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    moduleAutEquiv R (n + 1) (StableGeneralLinear.step R n g) =
      (appendIso R n).symm ≪≫
        biprod.mapIso (moduleAutEquiv R n g) (Iso.refl (freeModule R 1)) ≪≫ appendIso R n := by
  apply Iso.ext
  apply (cancel_mono (appendIso R n).inv).1
  simpa only [Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom, Iso.refl_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id] using moduleAutEquiv_stabilization R n g

end Matrix.RightModule
