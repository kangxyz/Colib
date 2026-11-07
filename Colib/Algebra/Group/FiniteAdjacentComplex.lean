/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Data.Fin.VecNotation

/-! # Finite adjacent-coordinate incidence and alternating Euler maps

For an actual commutative group, a disk coordinate contributes to its two
adjacent term coordinates. The original incidence map is injective, and its
image is exactly the kernel of the alternating Euler homomorphism.
These are group calculations, with no K-theory or fibration assertion as input.


Implementation provenance:
`Quillen/Aglib/Algebra/Group/FiniteAdjacentComplex.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

noncomputable section
universe u
namespace MonoidHom.FiniteAdjacentComplex
variable (G : Type u) [CommGroup G]

/-- Original first coordinate of a nonempty finite tuple. -/
def headHom (n : ℕ) : (Fin (n + 1) → G) →* G where
  toFun x := x 0
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Delete the actual first coordinate. -/
def tailHom (n : ℕ) : (Fin (n + 1) → G) →* (Fin n → G) where
  toFun := Fin.tail
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Alternating Euler product, starting with the original first coordinate. -/
def euler : (n : ℕ) → (Fin n → G) →* G
  | 0 => 1
  | n + 1 => headHom G n / (euler n).comp (tailHom G n)

@[simp] theorem euler_zero (x : Fin 0 → G) : euler G 0 x = 1 := rfl
@[simp] theorem euler_succ (n : ℕ) (x : Fin (n + 1) → G) :
    euler G (n + 1) x = x 0 / euler G n (Fin.tail x) := rfl
theorem euler_cons (n : ℕ) (x : G) (xs : Fin n → G) :
    euler G (n + 1) (Fin.cons x xs) = x / euler G n xs := by simp

/-- Extend the actual disk tuple by a unit at its initial boundary. -/
def prependOne (n : ℕ) : (Fin n → G) →* (Fin (n + 1) → G) where
  toFun x := Fin.cons 1 x
  map_one' := by ext i; cases i using Fin.cases <;> simp
  map_mul' x y := by ext i; cases i using Fin.cases <;> simp

/-- Extend the actual disk tuple by a unit at its terminal boundary. -/
def appendOne (n : ℕ) : (Fin n → G) →* (Fin (n + 1) → G) where
  toFun x := Fin.snoc x 1
  map_one' := by ext i; cases i using Fin.lastCases <;> simp
  map_mul' x y := by ext i; cases i using Fin.lastCases <;> simp

/-- The original two adjacent coordinate contributions, with unit boundary values. -/
def incidence (n : ℕ) : (Fin n → G) →* (Fin (n + 1) → G) :=
  prependOne G n * appendOne G n

@[simp] theorem incidence_apply (n : ℕ) (x : Fin n → G) (i : Fin (n + 1)) :
    incidence G n x i =
      (Fin.cons 1 x : Fin (n + 1) → G) i * (Fin.snoc x 1 : Fin (n + 1) → G) i := rfl

/-- At the initial term, only the original first disk contributes. -/
theorem incidence_zero (n : ℕ) (x : Fin (n + 1) → G) :
    incidence G (n + 1) x 0 = x 0 := by simp [incidence, prependOne, appendOne]

/-- At the terminal term, only the original last disk contributes. -/
theorem incidence_last (n : ℕ) (x : Fin (n + 1) → G) :
    incidence G (n + 1) x (Fin.last (n + 1)) = x (Fin.last n) := by simp [incidence, prependOne,
        appendOne]

/-- The exact recurrence of the original incidence matrix. -/
theorem incidence_cons (n : ℕ) (x : G) (xs : Fin n → G) :
    incidence G (n + 1) (Fin.cons x xs) =
      Fin.cons x (Fin.cons x (1 : Fin n → G) * incidence G n xs) := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    cases i using Fin.cases with
    | zero => simp [incidence, prependOne, appendOne, ← Fin.cons_snoc_eq_snoc_cons]
    | succ i => simp [incidence, prependOne, appendOne, ← Fin.cons_snoc_eq_snoc_cons]

/-- Every actual adjacent disk has trivial alternating Euler product. -/
theorem euler_incidence (n : ℕ) (x : Fin n → G) :
    euler G (n + 1) (incidence G n x) = 1 := by
  induction n with
  | zero =>
    have hx : x = (1 : Fin 0 → G) := Subsingleton.elim _ _
    rw [hx, map_one, map_one]
  | succ n ih =>
    rw [← Fin.cons_self_tail x, incidence_cons, euler_cons, map_mul,
      euler_cons, map_one, div_one, ih, mul_one, div_self']

/-- The original adjacent-coordinate incidence is injective, even at length zero. -/
theorem incidence_injective (n : ℕ) : Function.Injective (incidence G n) := by
  induction n with
  | zero => intro x y h; exact Subsingleton.elim x y
  | succ n ih =>
    intro x y h
    have h0 : x 0 = y 0 := by simpa using congrFun h 0
    have ht : Fin.tail x = Fin.tail y := by
      apply ih
      have ht := congrArg Fin.tail h
      rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, incidence_cons,
        incidence_cons] at ht
      simpa [h0] using ht
    exact (Fin.cons_self_tail x).symm.trans ((congrArg₂ Fin.cons h0 ht).trans
        (Fin.cons_self_tail y))

/-- Unit Euler product is exactly membership in the image of the original
adjacent disk-incidence homomorphism. -/
theorem euler_eq_one_iff (n : ℕ) (y : Fin (n + 1) → G) :
    euler G (n + 1) y = 1 ↔ ∃ x : Fin n → G, incidence G n x = y := by
  constructor
  · intro h
    induction n with
    | zero =>
      refine ⟨1, ?_⟩
      rw [map_one]
      ext i
      rw [Fin.eq_zero i]
      simpa using h.symm
    | succ n ih =>
      let z : Fin (n + 1) → G := Fin.tail y / Fin.cons (y 0) (1 : Fin n → G)
      have hz : euler G (n + 1) z = 1 := by
        have hy : euler G (n + 1) (Fin.tail y) = y 0 := by
          exact (div_eq_one.mp h).symm
        simp [z, map_div, hy]
      obtain ⟨x, hx⟩ := ih z hz
      refine ⟨Fin.cons (y 0) x, ?_⟩
      rw [incidence_cons, hx]
      have hz' : Fin.cons (y 0) (1 : Fin n → G) * z = Fin.tail y := by
        dsimp [z]
        simp
      rw [hz', Fin.cons_self_tail]
  · rintro ⟨x, rfl⟩
    exact euler_incidence G n x

/-- A singleton in the initial term is an explicit section of Euler. -/
def initialTerm (n : ℕ) : G →* (Fin (n + 1) → G) where
  toFun x := Fin.cons x 1
  map_one' := by ext i; cases i using Fin.cases <;> simp
  map_mul' x y := by ext i; cases i using Fin.cases <;> simp

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem initialTerm_head_div_euler_tail (n : ℕ) (x : G) :
    initialTerm G n x 0 / euler G n (Fin.tail (initialTerm G n x)) = x := by
  simp [initialTerm]


theorem euler_surjective (n : ℕ) : Function.Surjective (euler G (n + 1)) :=
  fun x => ⟨initialTerm G n x, by
    simpa only [euler_succ] using initialTerm_head_div_euler_tail G n x⟩

end MonoidHom.FiniteAdjacentComplex
