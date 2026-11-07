/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Colib.LinearAlgebra.Matrix.RightLinear

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/Aglib/Algebra/Category/ModuleCat/MatrixBaseChange.lean`.
The original hypotheses and maps are retained.

# Change of rings on finite free matrices and their formal summands

Objects are natural-number ranks; morphisms act on right-module column vectors.
Composition is therefore reverse matrix multiplication. Entrywise application
of any ring homomorphism gives an actual functor and extends to the Karoubi
envelope. No commutativity or invariant basis number is used.
-/
@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Idempotents

namespace Matrix.RightModule

/-- A rank-labelled category of finite free right modules, expressed by matrices. -/
structure FreeCategory (_R : Type u) where
  /-- The chosen rank, without any uniqueness assertion. -/
  rank : ℕ

instance {R : Type u} [Ring R] : Category (FreeCategory R) where
  Hom n m := Matrix (Fin m.rank) (Fin n.rank) R
  id _ := 1
  comp f g := g * f
  id_comp f := Matrix.mul_one f
  comp_id f := Matrix.one_mul f
  assoc f g h := (Matrix.mul_assoc h g f).symm

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]

/-- Entrywise change of rings on the column-matrix category. -/
def freeBaseChange (f : R →+* S) : FreeCategory R ⥤ FreeCategory S where
  obj n := ⟨n.rank⟩
  map A := A.map f
  map_id _ := Matrix.map_one f f.map_zero f.map_one
  map_comp _ _ := Matrix.map_mul

/-- Formal direct summands of finite free right modules. -/
abbrev ProjectiveMatrices (R : Type u) [Ring R] := Karoubi (FreeCategory R)

/-- Ring homomorphisms carry actual idempotents and their compatible matrices to idempotents. -/
def baseChange (f : R →+* S) : ProjectiveMatrices R ⥤ ProjectiveMatrices S where
  obj P :=
    { X := (freeBaseChange f).obj P.X
      p := (freeBaseChange f).map P.p
      idem := by rw [← Functor.map_comp, P.idem] }
  map a :=
    { f := (freeBaseChange f).map a.f
      comm := by rw [← Functor.map_comp, ← Functor.map_comp, a.comm] }
  map_id _ := rfl
  map_comp _ _ := by apply Karoubi.Hom.ext; exact (freeBaseChange f).map_comp _ _

@[simp] lemma baseChange_obj_matrix (f : R →+* S) (P : ProjectiveMatrices R) :
    ((baseChange f).obj P).p = P.p.map f := rfl

@[simp] lemma baseChange_map_matrix (f : R →+* S) {P Q : ProjectiveMatrices R}
    (a : P ⟶ Q) : ((baseChange f).map a).f = a.f.map f := rfl

@[simp] lemma freeBaseChange_id : freeBaseChange (RingHom.id R) = 𝟭 (FreeCategory R) := rfl

@[simp] lemma freeBaseChange_comp (f : R →+* S) (g : S →+* T) :
    freeBaseChange (g.comp f) = freeBaseChange f ⋙ freeBaseChange g := rfl

@[simp] lemma baseChange_id : baseChange (RingHom.id R) = 𝟭 (ProjectiveMatrices R) := rfl

@[simp] lemma baseChange_comp (f : R →+* S) (g : S →+* T) :
    baseChange (g.comp f) = baseChange f ⋙ baseChange g := rfl

end Matrix.RightModule
