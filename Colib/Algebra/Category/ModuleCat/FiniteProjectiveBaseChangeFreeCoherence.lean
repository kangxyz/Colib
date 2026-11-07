/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeFree
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeMonoidal
public import Colib.LinearAlgebra.Matrix.RightAutomorphismsLeft

/-!
Implementation provenance:
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveBaseChangeFreeCoherence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Coherence of the original finite-free change-of-rings isomorphisms

Rectangular matrix naturality retains the original finite bases. It supplies
compatibility with the actual coproduct inclusions and the chosen successor
isomorphisms, beyond naturality only for invertible square matrices.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents MonoidalCategory
open scoped Matrix
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  preservesBinaryBiproducts_of_preservesBiproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
  ModuleCat.FiniteProjective.rightBaseChangeMonoidal
namespace Matrix.RightModule
variable {R S : Type u} [Ring R] [Ring S]

/-- A rectangular matrix between the original identity summands. -/
def rectMatrixHom {n m : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    (toKaroubi (FreeCategory R)).obj ⟨n⟩ ⟶
      (toKaroubi (FreeCategory R)).obj ⟨m⟩ :=
  (toKaroubi (FreeCategory R)).map A

/-- The original rectangular matrix map on the chosen actual finite free modules. -/
def freeRectHom {n m : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n ⟶ ModuleCat.FiniteProjective.free m :=
  (freeImageIso n).inv ≫ imageFunctor.map (rectMatrixHom A) ≫ (freeImageIso m).hom

/-- The rectangular free map is ordinary matrix multiplication on the original columns. -/
lemma freeRectHom_apply {n m : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (x : Fin n → Rᵐᵒᵖ) (i : Fin m) :
    (freeRectHom A).hom x i =
      MulOpposite.op ((A *ᵥ fun j => MulOpposite.unop (x j)) i) := rfl

/-- The identity-summand comparison retains arbitrary rectangular matrix entries. -/
lemma baseChange_rectMatrixHom (f : R →+* S) {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) R) :
    (baseChange f).map (rectMatrixHom A) ≫ (eqToIso (baseChange_toKaroubi f m)).hom =
      (eqToIso (baseChange_toKaroubi f n)).hom ≫ rectMatrixHom (A.map f) := by
  apply Karoubi.Hom.ext
  simp only [Karoubi.comp_f, eqToIso.hom, Karoubi.eqToHom_f]
  change ((1 : Matrix (Fin m) (Fin m) S) * (1 : Matrix (Fin m) (Fin m) R).map f) *
      A.map f = A.map f *
        ((1 : Matrix (Fin n) (Fin n) S) * (1 : Matrix (Fin n) (Fin n) R).map f)
  simp only [Matrix.map_one f f.map_zero f.map_one, Matrix.one_mul, Matrix.mul_one]

/-- The prescribed finite-free comparison is natural for every original rectangular matrix. -/
lemma freeBaseChangeIso_rect_naturality (f : R →+* S) {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) R) :
    (ModuleCat.FiniteProjective.rightBaseChange f).map (freeRectHom A) ≫
        (freeBaseChangeIso f m).hom =
      (freeBaseChangeIso f n).hom ≫ freeRectHom (A.map f) := by
  let F := ModuleCat.FiniteProjective.rightBaseChange f
  let a := rectMatrixHom A
  have hN := (imageBaseChangeIso f).hom.naturality a
  change F.map (imageFunctor.map a) ≫ ((imageBaseChangeIso f).app _).hom =
    ((imageBaseChangeIso f).app _).hom ≫ imageFunctor.map ((baseChange f).map a) at hN
  have hC := congrArg imageFunctor.map (baseChange_rectMatrixHom f A)
  simp only [Functor.map_comp] at hC
  simp only [freeRectHom, freeBaseChangeIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc,
    Iso.hom_inv_id_assoc]
  change F.map (freeImageIso n).inv ≫ F.map (imageFunctor.map a) ≫
      ((imageBaseChangeIso f).app _).hom ≫
        imageFunctor.map (eqToIso (baseChange_toKaroubi f m)).hom ≫
          (freeImageIso m).hom =
    F.map (freeImageIso n).inv ≫ ((imageBaseChangeIso f).app _).hom ≫
      imageFunctor.map (eqToIso (baseChange_toKaroubi f n)).hom ≫
        imageFunctor.map (rectMatrixHom (A.map f)) ≫ (freeImageIso m).hom
  rw [reassoc_of% hN]
  rw [reassoc_of% hC]

/-- The chosen successor inverse reads the original first coordinate. -/
lemma freeSuccIso_inv_fst_apply (n : ℕ) (x : Fin (n + 1) → Rᵐᵒᵖ) (i : Fin 1) :
    ((ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv ≫ biprod.fst).hom x i = x 0 := by
  let I := (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι
  have hp : (I.mapBiprod (ModuleCat.FiniteProjective.free 1)
      (ModuleCat.FiniteProjective.free n)).inv ≫ I.map biprod.fst = biprod.fst := by
    rw [Functor.mapBiprod_inv]
    apply biprod.hom_ext' <;> simp [← I.map_comp]
  have hs : I.map (ModuleCat.FiniteProjective.freeSuccIso n).inv =
      (prependIso R n).inv ≫
        (I.mapBiprod (ModuleCat.FiniteProjective.free 1) (ModuleCat.FiniteProjective.free n)).inv :=
    congrArg Iso.inv (freeSuccIso_map R n)
  have hm : I.map ((ModuleCat.FiniteProjective.freeSuccIso n).inv ≫ biprod.fst) =
      (prependIso R n).inv ≫ biprod.fst := by
    rw [I.map_comp, hs, Category.assoc, hp]
    rfl
  refine (congrArg (fun k : freeModule R (n + 1) ⟶ freeModule R 1 =>
    k x i) hm).trans ?_
  simp only [prependIso, Iso.trans_inv, Category.assoc,
    ModuleCat.biprodIsoProd_inv_comp_fst]
  rfl

/-- The chosen successor inverse reads the original remaining coordinates. -/
lemma freeSuccIso_inv_snd_apply (n : ℕ) (x : Fin (n + 1) → Rᵐᵒᵖ) (i : Fin n) :
    ((ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv ≫ biprod.snd).hom x i =
      x i.succ := by
  let I := (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι
  have hp : (I.mapBiprod (ModuleCat.FiniteProjective.free 1)
      (ModuleCat.FiniteProjective.free n)).inv ≫ I.map biprod.snd = biprod.snd := by
    rw [Functor.mapBiprod_inv]
    apply biprod.hom_ext' <;> simp [← I.map_comp]
  have hs : I.map (ModuleCat.FiniteProjective.freeSuccIso n).inv =
      (prependIso R n).inv ≫
        (I.mapBiprod (ModuleCat.FiniteProjective.free 1) (ModuleCat.FiniteProjective.free n)).inv :=
    congrArg Iso.inv (freeSuccIso_map R n)
  have hm : I.map ((ModuleCat.FiniteProjective.freeSuccIso n).inv ≫ biprod.snd) =
      (prependIso R n).inv ≫ biprod.snd := by
    rw [I.map_comp, hs, Category.assoc, hp]
    rfl
  refine (congrArg (fun k : freeModule R (n + 1) ⟶ freeModule R n =>
    k x i) hm).trans ?_
  simp only [prependIso, Iso.trans_inv, Category.assoc,
    ModuleCat.biprodIsoProd_inv_comp_snd]
  rfl

/-- The original matrix inserting the first rank-one coordinate. -/
def prependInlMatrix (R : Type u) [Ring R] (n : ℕ) : Matrix (Fin (n + 1)) (Fin 1) R :=
  fun i _ => if i = 0 then 1 else 0

/-- The original matrix inserting all following coordinates. -/
def prependInrMatrix (R : Type u) [Ring R] (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) R :=
  fun i j => if i = j.succ then 1 else 0

/-- Changing entries preserves the original first-coordinate matrix. -/
lemma prependInlMatrix_map (f : R →+* S) (n : ℕ) :
    (prependInlMatrix R n).map f = prependInlMatrix S n := by
  ext i j
  simp [prependInlMatrix, Matrix.map_apply]

/-- Changing entries preserves the original tail-coordinate matrix. -/
lemma prependInrMatrix_map (f : R →+* S) (n : ℕ) :
    (prependInrMatrix R n).map f = prependInrMatrix S n := by
  ext i j
  simp [prependInrMatrix, Matrix.map_apply]

/-- The first-coordinate matrix is the original biproduct inclusion followed by the successor. -/
lemma freeRectHom_prependInl (n : ℕ) :
    freeRectHom (prependInlMatrix R n) =
      biprod.inl ≫ (ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).hom := by
  apply (cancel_mono (ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.inl_fst]
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change ((ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv ≫ biprod.fst).hom
      ((freeRectHom (prependInlMatrix R n)).hom x) i = x i
    rw [freeSuccIso_inv_fst_apply, freeRectHom_apply]
    simp [prependInlMatrix, Matrix.mulVec, dotProduct, Subsingleton.elim i (0 : Fin 1)]
  · simp only [Category.assoc, biprod.inl_snd]
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change ((ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv ≫ biprod.snd).hom
      ((freeRectHom (prependInlMatrix R n)).hom x) i = 0
    rw [freeSuccIso_inv_snd_apply, freeRectHom_apply]
    simp [prependInlMatrix, Matrix.mulVec, dotProduct]

/-- The tail-coordinate matrix is the original biproduct inclusion followed by the successor. -/
lemma freeRectHom_prependInr (n : ℕ) :
    freeRectHom (prependInrMatrix R n) =
      biprod.inr ≫ (ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).hom := by
  apply (cancel_mono (ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.inr_fst]
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change ((ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv ≫ biprod.fst).hom
      ((freeRectHom (prependInrMatrix R n)).hom x) i = 0
    rw [freeSuccIso_inv_fst_apply, freeRectHom_apply]
    simp [prependInrMatrix, Matrix.mulVec, dotProduct, eq_comm]
  · simp only [Category.assoc, biprod.inr_snd]
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change ((ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv ≫ biprod.snd).hom
      ((freeRectHom (prependInrMatrix R n)).hom x) i = x i
    rw [freeSuccIso_inv_snd_apply, freeRectHom_apply]
    simp [prependInrMatrix, Matrix.mulVec, dotProduct]

/-- The prescribed comparison regarded as an actual isomorphism in the projective core. -/
def freeCoreBaseChangeIso (f : R →+* S) (n : ℕ) :
    (ModuleCat.FiniteProjective.rightBaseChange f).core.obj
        (ModuleCat.FiniteProjective.freeIso Rᵐᵒᵖ n) ≅
      ModuleCat.FiniteProjective.freeIso Sᵐᵒᵖ n :=
  Core.isoMk (freeBaseChangeIso f n)

/-- The actual successor comparison commutes with the original coproduct tensorator. -/
lemma freeCoreBaseChangeIso_successor (f : R →+* S) (n : ℕ) :
    Functor.LaxMonoidal.μ (ModuleCat.FiniteProjective.rightBaseChange f).core
        (ModuleCat.FiniteProjective.freeIso Rᵐᵒᵖ 1) (ModuleCat.FiniteProjective.freeIso Rᵐᵒᵖ n) ≫
      (ModuleCat.FiniteProjective.rightBaseChange f).core.map
        (ModuleCat.FiniteProjective.freeIsoSucc Rᵐᵒᵖ n).hom ≫
          (freeCoreBaseChangeIso f (n + 1)).hom =
      ((freeCoreBaseChangeIso f 1).hom ⊗ₘ (freeCoreBaseChangeIso f n).hom) ≫
        (ModuleCat.FiniteProjective.freeIsoSucc Sᵐᵒᵖ n).hom := by
  let F := ModuleCat.FiniteProjective.rightBaseChange f
  have hl := freeBaseChangeIso_rect_naturality f (prependInlMatrix R n)
  rw [prependInlMatrix_map, freeRectHom_prependInl, freeRectHom_prependInl] at hl
  have hr := freeBaseChangeIso_rect_naturality f (prependInrMatrix R n)
  rw [prependInrMatrix_map, freeRectHom_prependInr, freeRectHom_prependInr] at hr
  apply Core.hom_ext
  change coprodComparison F
      (ModuleCat.FiniteProjective.free 1) (ModuleCat.FiniteProjective.free n) ≫
      F.map ((biprod.isoCoprod (ModuleCat.FiniteProjective.free 1)
        (ModuleCat.FiniteProjective.free n)).inv ≫ (ModuleCat.FiniteProjective.freeSuccIso n).hom) ≫
          (freeBaseChangeIso f (n + 1)).hom =
      coprod.map (freeBaseChangeIso f 1).hom (freeBaseChangeIso f n).hom ≫
        (biprod.isoCoprod (ModuleCat.FiniteProjective.free 1)
          (ModuleCat.FiniteProjective.free n)).inv ≫ (ModuleCat.FiniteProjective.freeSuccIso n).hom
  apply coprod.hom_ext
  · simp only [coprodComparison_inl_assoc, coprod.inl_map_assoc]
    rw [← Functor.map_comp_assoc]
    simpa only [biprod.isoCoprod_inv, coprod.inl_desc_assoc] using hl
  · simp only [coprodComparison_inr_assoc, coprod.inr_map_assoc]
    rw [← Functor.map_comp_assoc]
    simpa only [biprod.isoCoprod_inv, coprod.inr_desc_assoc] using hr

/-- The explicit permutation matrix reversing the original finite basis. -/
def reverseMatrix (R : Type u) [Ring R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if j = i.rev then 1 else 0

/-- The explicit basis reversal in the original finite projective category. -/
def freeReverseIso (R : Type u) [Ring R] (n : ℕ) :
    ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n ≅ ModuleCat.FiniteProjective.free n :=
  (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).isoMk (reverseIso R n)

/-- Entrywise change of rings retains the explicit reversal matrix. -/
lemma reverseMatrix_map (f : R →+* S) (n : ℕ) :
    (reverseMatrix R n).map f = reverseMatrix S n := by
  ext i j
  simp [reverseMatrix, Matrix.map_apply]

/-- Matrix reversal is exactly the already chosen finite-basis reversal. -/
lemma freeRectHom_reverse (n : ℕ) :
    freeRectHom (reverseMatrix R n) = (freeReverseIso R n).hom := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  change (freeRectHom (reverseMatrix R n)).hom x i = x i.rev
  rw [freeRectHom_apply]
  simp [reverseMatrix, Matrix.mulVec, dotProduct]

/-- The chosen reversal is involutive also as an original projective morphism. -/
lemma freeReverseIso_inv (n : ℕ) :
    (freeReverseIso R n).inv = (freeReverseIso R n).hom := rfl

/-- The prescribed free comparison intertwines the original finite coordinate reversal. -/
lemma freeBaseChangeIso_reverse (f : R →+* S) (n : ℕ) :
    (ModuleCat.FiniteProjective.rightBaseChange f).map (freeReverseIso R n).hom ≫
        (freeBaseChangeIso f n).hom =
      (freeBaseChangeIso f n).hom ≫ (freeReverseIso S n).hom := by
  simpa only [reverseMatrix_map, freeRectHom_reverse] using
    freeBaseChangeIso_rect_naturality f (reverseMatrix R n)

/-- The pre-existing left action is exactly conjugation by the original reversal. -/
lemma leftFreeAutEquiv_hom_conjugation (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (leftFreeAutEquiv R n g).hom =
      (freeReverseIso R n).inv ≫ (freeAutEquiv R n g).hom ≫ (freeReverseIso R n).hom := by
  let I := (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι
  apply I.map_injective
  simp only [Functor.map_comp]
  have hl := congrArg Iso.hom (leftFreeAutEquiv_map R n g)
  have hr := congrArg Iso.hom (freeAutEquiv_map R n g)
  change I.map (leftFreeAutEquiv R n g).hom = (leftModuleAutEquiv R n g).hom at hl
  change I.map (freeAutEquiv R n g).hom = (moduleAutEquiv R n g).hom at hr
  rw [hl, hr]
  rfl

/-- The original free comparison intertwines the reversal-aligned matrix action. -/
lemma freeBaseChangeIso_left_action (f : R →+* S) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (ModuleCat.FiniteProjective.rightBaseChange f).map (leftFreeAutEquiv R n g).hom ≫
        (freeBaseChangeIso f n).hom =
      (freeBaseChangeIso f n).hom ≫
        (leftFreeAutEquiv S n (StableGeneralLinear.finiteMap f n g)).hom := by
  rw [leftFreeAutEquiv_hom_conjugation, leftFreeAutEquiv_hom_conjugation]
  simp only [freeReverseIso_inv, Functor.map_comp, Category.assoc]
  rw [freeBaseChangeIso_reverse f n,
    reassoc_of% freeBaseChangeIso_matrix_action f n g,
    reassoc_of% freeBaseChangeIso_reverse f n]

end Matrix.RightModule
