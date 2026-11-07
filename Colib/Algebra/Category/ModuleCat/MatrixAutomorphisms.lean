/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.MatrixBaseChange
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Mathlib.Data.Matrix.Block

/-!
Implementation provenance: `Quillen/Aglib/Algebra/Category/ModuleCat/MatrixAutomorphisms.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Actual automorphisms and retracts of matrix summands

The underlying compatible matrices extend by the identity on their
complement. Presentation isomorphisms give literal block involutions,
and a specified retract retains its actual composite-idempotent presentation.
No stable elementary quotient is used.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Idempotents
namespace Matrix.RightModule
variable {R : Type u} [Ring R]

/-- The underlying matrix of a compatible summand morphism. -/
abbrev homMatrix {P Q : ProjectiveMatrices R} (f : P ⟶ Q) :
    Matrix (Fin Q.X.rank) (Fin P.X.rank) R := f.f

/-- The original idempotent matrix of a chosen summand presentation. -/
abbrev idempotentMatrix (P : ProjectiveMatrices R) :
    Matrix (Fin P.X.rank) (Fin P.X.rank) R := P.p

/-- Extend a summand automorphism by the identity on the complementary idempotent. -/
def extendAut {P : ProjectiveMatrices R} (g : Aut P) :
    Matrix.GeneralLinearGroup (Fin P.X.rank) R where
  val := homMatrix g.hom + (1 - idempotentMatrix P)
  inv := homMatrix g.inv + (1 - idempotentMatrix P)
  val_inv := by
    have hp : idempotentMatrix P * idempotentMatrix P = idempotentMatrix P := P.idem
    have hgi : homMatrix g.hom * homMatrix g.inv = idempotentMatrix P :=
      congrArg (fun f => homMatrix f) g.inv_hom_id
    have hg : homMatrix g.hom * idempotentMatrix P = homMatrix g.hom := Karoubi.p_comp g.hom
    have hi : idempotentMatrix P * homMatrix g.inv = homMatrix g.inv := Karoubi.comp_p g.inv
    simp [mul_add, add_mul, mul_sub, sub_mul, hp, hgi, hg, hi]
  inv_val := by
    have hp : idempotentMatrix P * idempotentMatrix P = idempotentMatrix P := P.idem
    have hgi : homMatrix g.inv * homMatrix g.hom = idempotentMatrix P :=
      congrArg (fun f => homMatrix f) g.hom_inv_id
    have hg : homMatrix g.inv * idempotentMatrix P = homMatrix g.inv := Karoubi.p_comp g.inv
    have hi : idempotentMatrix P * homMatrix g.hom = homMatrix g.hom := Karoubi.comp_p g.hom
    simp [mul_add, add_mul, mul_sub, sub_mul, hp, hgi, hg, hi]

/-- The identity-extension construction preserves multiplication of automorphisms. -/
lemma extendAut_mul {P : ProjectiveMatrices R} (g h : Aut P) :
    extendAut (g * h) = extendAut g * extendAut h := by
  apply Units.ext
  have hp : idempotentMatrix P * idempotentMatrix P = idempotentMatrix P := P.idem
  have hg : homMatrix g.hom * idempotentMatrix P = homMatrix g.hom := Karoubi.p_comp g.hom
  have hh : idempotentMatrix P * homMatrix h.hom = homMatrix h.hom := Karoubi.comp_p h.hom
  change homMatrix g.hom * homMatrix h.hom + (1 - idempotentMatrix P) =
    (homMatrix g.hom + (1 - idempotentMatrix P)) *
      (homMatrix h.hom + (1 - idempotentMatrix P))
  simp [mul_add, add_mul, mul_sub, sub_mul, hp, hg, hh]

/-- Isomorphic summand presentations yield an explicit stable matrix involution. -/
def presentationSwap {P Q : ProjectiveMatrices R} (e : P ≅ Q) :
    (Matrix (Fin P.X.rank ⊕ Fin Q.X.rank) (Fin P.X.rank ⊕ Fin Q.X.rank) R)ˣ := by
  let p := idempotentMatrix P
  let q := idempotentMatrix Q
  let a := homMatrix e.inv
  let b := homMatrix e.hom
  have hp : p * p = p := P.idem
  have hq : q * q = q := Q.idem
  have hab : a * b = p := congrArg homMatrix e.hom_inv_id
  have hba : b * a = q := congrArg homMatrix e.inv_hom_id
  have hpa : p * a = a := Karoubi.comp_p e.inv
  have haq : a * q = a := Karoubi.p_comp e.inv
  have hqb : q * b = b := Karoubi.comp_p e.hom
  have hbp : b * p = b := Karoubi.p_comp e.hom
  have hw : Matrix.fromBlocks (1 - p) a b (1 - q) *
      Matrix.fromBlocks (1 - p) a b (1 - q) = 1 := by
    simp [Matrix.fromBlocks_multiply, Matrix.mul_sub, Matrix.sub_mul,
      hp, hq, hab, hba, hpa, haq, hqb, hbp]
  exact ⟨Matrix.fromBlocks (1 - p) a b (1 - q),
    Matrix.fromBlocks (1 - p) a b (1 - q), hw, hw⟩

/-- An original matrix unit as an automorphism of the identity-idempotent presentation. -/
def matrixUnitAut (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    Aut ((toKaroubi (FreeCategory R)).obj ⟨n⟩) where
  hom := ⟨g.val, by
    change (1 : Matrix (Fin n) (Fin n) R) * (g.val : Matrix (Fin n) (Fin n) R) *
      (1 : Matrix (Fin n) (Fin n) R) = g.val
    simp⟩
  inv := ⟨g.inv, by
    change (1 : Matrix (Fin n) (Fin n) R) * (g.inv : Matrix (Fin n) (Fin n) R) *
      (1 : Matrix (Fin n) (Fin n) R) = g.inv
    simp⟩
  hom_inv_id := by apply Karoubi.Hom.ext; exact g.inv_val
  inv_hom_id := by apply Karoubi.Hom.ext; exact g.val_inv

/-- A retract inside another matrix summand has its actual composite idempotent presentation. -/
def retractPresentation {P Q : ProjectiveMatrices R} (i : P ⟶ Q) (r : Q ⟶ P)
    (hr : i ≫ r = 𝟙 P) : ProjectiveMatrices R where
  X := Q.X
  p := homMatrix i * homMatrix r
  idem := by
    have h : homMatrix r * homMatrix i = idempotentMatrix P := congrArg homMatrix hr
    have hi : homMatrix i * idempotentMatrix P = homMatrix i := Karoubi.p_comp i
    change (homMatrix i * homMatrix r) * (homMatrix i * homMatrix r) = _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (homMatrix r), h, ← Matrix.mul_assoc, hi]

/-- The original retract maps identify it with its composite-idempotent image. -/
def retractPresentationIso {P Q : ProjectiveMatrices R} (i : P ⟶ Q) (r : Q ⟶ P)
    (hr : i ≫ r = 𝟙 P) : P ≅ retractPresentation i r hr := by
  have h : homMatrix r * homMatrix i = idempotentMatrix P := congrArg homMatrix hr
  have hi : homMatrix i * idempotentMatrix P = homMatrix i := Karoubi.p_comp i
  have hr' : idempotentMatrix P * homMatrix r = homMatrix r := Karoubi.comp_p r
  refine ⟨⟨i.f, ?_⟩, ⟨r.f, ?_⟩, ?_, ?_⟩
  · change ((homMatrix i * homMatrix r) * homMatrix i) * idempotentMatrix P = homMatrix i
    rw [Matrix.mul_assoc (homMatrix i) (homMatrix r) (homMatrix i), h, hi, hi]
  · change (idempotentMatrix P * homMatrix r) * (homMatrix i * homMatrix r) = homMatrix r
    rw [hr', ← Matrix.mul_assoc, h, hr']
  · apply Karoubi.Hom.ext
    exact h
  · apply Karoubi.Hom.ext
    rfl

end Matrix.RightModule
