/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Stable general linear groups over arbitrary rings

The finite stages are units of square matrices. Stabilization adjoins a final
identity entry, and the stable group is their directed limit. No commutativity,
nontriviality, or invariant basis number assumption is used.

The canonical `of` maps are injective and admit bundled compatible `lift`s.
Finite families admit a common finite-stage representative. `transition_val_fromBlocks`
identifies arbitrary transitions with block diagonal extension, and `map` supplies
functorial entrywise change of coefficients for unital ring homomorphisms.

These are algebraic foundations for the usual stable general linear group in
Quillen's plus construction; this file does not construct the plus construction
or identify its higher homotopy groups.

## Implementation provenance

Adapted from `Quillen/Algebra/Group/StableGeneralLinear.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. This is Mathlib's `DirectLimit` of
its native finite general linear groups under the specified block stabilization.
-/
@[expose] public section

universe u

namespace StableGeneralLinear

variable (R : Type u) [Ring R]

/-- The stable general linear group, formed as a genuine directed limit. -/
abbrev Group := DirectLimit ((fun n => Matrix.GeneralLinearGroup (Fin n) R)) (transition R)

noncomputable section

/-- The canonical homomorphism from a finite stage. -/
def of (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R →* Group R where
  toFun g := ⟦⟨n, g⟩⟧
  map_one' := (DirectLimit.one_def n).symm
  map_mul' _ _ := (DirectLimit.mul_def ..).symm

@[simp] lemma of_transition {n m : ℕ} (h : n ≤ m) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    of R m (transition R n m h g) = of R n g := DirectLimit.mk_apply ..

/-- Equality in the stable group is equality at a common finite stage. -/
lemma of_eq_iff {n m : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R) (h :
  Matrix.GeneralLinearGroup (Fin m) R) :
    of R n g = of R m h ↔
      ∃ k, ∃ (hn : n ≤ k) (hm : m ≤ k), transition R n k hn g = transition R m k hm h :=
  Quotient.eq

lemma of_injective (n : ℕ) : Function.Injective (of R n) :=
  DirectLimit.mk_injective _ (transition_injective R) n

/-- Every stable matrix has a finite-stage representative. -/
lemma exists_of (g : Group R) : ∃ n, ∃ a : Matrix.GeneralLinearGroup (Fin n) R, g = of R n a :=
  DirectLimit.exists_eq_mk _ g

/-- Two stable matrices can always be represented at one common finite stage. -/
lemma exists_of₂ (g h : Group R) :
    ∃ n, ∃ a b : Matrix.GeneralLinearGroup (Fin n) R, g = of R n a ∧ h = of R n b :=
  DirectLimit.exists_eq_mk₂ _ g h

/-- Compatible finite-stage homomorphisms induce a stable homomorphism. -/
def lift {H : Type*} [_root_.Group H] (f : ∀ n, Matrix.GeneralLinearGroup (Fin n) R →* H)
    (hf : ∀ n m (h : n ≤ m) g, f n g = f m (transition R n m h g)) : Group R →* H where
  toFun := DirectLimit.lift (transition R) (fun n => f n) hf
  map_one' := DirectLimit.lift_one f hf
  map_mul' := DirectLimit.lift_mul f hf

@[simp] lemma lift_of {H : Type*} [_root_.Group H] (f : ∀ n, Matrix.GeneralLinearGroup (Fin n)
  R →* H)
    (hf : ∀ n m (h : n ≤ m) g, f n g = f m (transition R n m h g))
    (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) : lift R f hf (of R n g) = f n g := rfl

@[simp] lemma lift_comp_of {H : Type*} [_root_.Group H] (f : ∀ n, Matrix.GeneralLinearGroup
  (Fin n) R →* H)
    (hf : ∀ n m (h : n ≤ m) g, f n g = f m (transition R n m h g)) (n : ℕ) :
    (lift R f hf).comp (of R n) = f n := rfl

/-- Every finite family admits representatives at a single finite rank. -/
lemma exists_of_family {ι : Type*} [Finite ι] (g : ι → Group R) :
    ∃ n, ∃ a : ι → Matrix.GeneralLinearGroup (Fin n) R, ∀ i, g i = of R n (a i) := by
  classical
  let := Fintype.ofFinite ι
  choose n a h using fun i => exists_of R (g i)
  refine ⟨Finset.univ.sup n,
    fun i => transition R (n i) _ (Finset.le_sup (Finset.mem_univ i)) (a i), ?_⟩
  intro i
  rw [of_transition, h i]

/-- Homomorphisms out of the stable group are determined by finite stages. -/
@[ext] lemma hom_ext {H : Type*} [_root_.Group H] {f g : Group R →* H}
    (h : ∀ n a, f (of R n a) = g (of R n a)) : f = g := by
  ext x
  obtain ⟨n, a, rfl⟩ := exists_of R x
  exact h n a

/-- The compatible lift is the unique homomorphism with the prescribed finite stages. -/
lemma lift_unique {H : Type*} [_root_.Group H] (f : ∀ n, Matrix.GeneralLinearGroup (Fin n) R →* H)
    (hf : ∀ n m (h : n ≤ m) g, f n g = f m (transition R n m h g))
    (φ : Group R →* H) (hφ : ∀ n, φ.comp (of R n) = f n) : φ = lift R f hf := by
  apply hom_ext
  intro n g
  exact DFunLike.congr_fun (hφ n) g

section RingMap

variable {R} {S : Type*} [Ring S] {T : Type*} [Ring T]

/-- The stable general linear group is functorial for all unital ring homomorphisms. -/
def map (f : R →+* S) : Group R →* Group S :=
  lift R (fun n => (of S n).comp (finiteMap f n)) (by
    intro n m h g
    simp only [MonoidHom.comp_apply, finiteMap_transition, of_transition])

@[simp] lemma map_of (f : R →+* S) (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    map f (of R n g) = of S n (finiteMap f n g) := rfl

@[simp] lemma map_id : map (RingHom.id R) = MonoidHom.id (Group R) := by
  apply hom_ext
  intro n g
  simp only [map_of, MonoidHom.id_apply]
  congr 1

@[simp] lemma map_comp (f : R →+* S) (g : S →+* T) :
    map (g.comp f) = (map g).comp (map f) := by
  apply hom_ext
  intro n a
  simp only [map_of, MonoidHom.comp_apply]
  congr 1

/-- An injective map of coefficient rings induces an injective stable group map. -/
lemma map_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro x y h
  obtain ⟨n, a, b, rfl, rfl⟩ := exists_of₂ R x y
  rw [map_of, map_of] at h
  have h' := of_injective S n h
  congr 1
  apply Units.ext
  ext i j
  apply hf
  exact congrFun (congrFun (congrArg (fun a : Matrix.GeneralLinearGroup (Fin n) S => a.val) h') i) j

end RingMap

end

end StableGeneralLinear
