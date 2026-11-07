/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Group.FiniteAdjacentComplex
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Nat.Even

/-!
# A canonical representative at any finite term coordinate

Euler on the literal single-coordinate inclusion is identity or inversion,
according to the coordinate parity. Its actual inverse gives a section at
any specified coordinate. Every term tuple has a unique decomposition into
an original adjacent-incidence image times that single-coordinate term.


Implementation provenance:
`Quillen/Aglib/Algebra/Group/FiniteAdjacentSection.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section


noncomputable section
universe u
namespace MonoidHom.FiniteAdjacentComplex
variable (G : Type u) [CommGroup G]

/-- The original single-coordinate inclusion into a finite tuple. -/
def singleCoordinate {n : ℕ} (i : Fin n) : G →* (Fin n → G) :=
  MonoidHom.mulSingle (fun _ : Fin n => G) i

@[simp] theorem singleCoordinate_apply {n : ℕ} (i : Fin n) (x : G) :
    singleCoordinate G i x = Pi.mulSingle i x := rfl

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem mulSingle_zero (n : ℕ) (x : G) :
    Pi.mulSingle (M := fun _ => G) (0 : Fin (n + 1)) x = Fin.cons x 1 := by
  ext j
  cases j using Fin.cases <;> simp


/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem mulSingle_succ {n : ℕ} (i : Fin n) (x : G) :
    Pi.mulSingle (M := fun _ => G) i.succ x = Fin.cons 1 (Pi.mulSingle (M := fun _ => G) i x) := by
  ext j
  cases j using Fin.cases <;> simp [Pi.mulSingle_apply]


/-- The sign at a coordinate, as an actual automorphism of the original group. -/
def coordinateSign (k : ℕ) : G ≃* G :=
  if Even k then MulEquiv.refl G else MulEquiv.inv G

@[simp] theorem coordinateSign_apply (k : ℕ) (x : G) :
    coordinateSign G k x = if Even k then x else x⁻¹ := by
  by_cases h : Even k <;> simp [coordinateSign, h]

@[simp] theorem coordinateSign_symm (k : ℕ) :
    (coordinateSign G k).symm = coordinateSign G k := by
  by_cases h : Even k <;> simp [coordinateSign, h]

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem ite_even_succ (k : ℕ) (x : G) :
    (if Even (k + 1) then x else x⁻¹) = (coordinateSign G k x)⁻¹ := by
  by_cases h : Even k <;> simp [coordinateSign_apply, Nat.even_add_one, h]


/-- Euler restricted to the actual single coordinate is the alternating sign
automorphism. No surjectivity or K-theory statement is assumed. -/
theorem euler_singleCoordinate {n : ℕ} (i : Fin n) (x : G) :
    euler G n (singleCoordinate G i x) = coordinateSign G i.val x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      have hzero : singleCoordinate G (0 : Fin (n + 1)) x = Fin.cons x 1 := by
        simpa only [singleCoordinate_apply] using mulSingle_zero G n x
      rw [hzero, euler_cons, map_one, div_one]
      simp [coordinateSign_apply]
    | succ i =>
      have hsucc : singleCoordinate G i.succ x = Fin.cons 1 (singleCoordinate G i x) := by
        simpa only [singleCoordinate_apply] using mulSingle_succ G i x
      simp only [hsucc, euler_cons, one_div, ih, Fin.val_succ]
      simpa only [coordinateSign_apply] using (ite_even_succ G i.val x).symm

/-- In every position, Euler on the original single-coordinate inclusion is
bijective, including the unique coordinate of a length-one tuple. -/
theorem euler_singleCoordinate_bijective {n : ℕ} (i : Fin n) :
    Function.Bijective ((euler G n).comp (singleCoordinate G i)) := by
  have h : (euler G n).comp (singleCoordinate G i) = (coordinateSign G i.val).toMonoidHom := by
    ext x
    exact euler_singleCoordinate G i x
  rw [h]
  exact (coordinateSign G i.val).bijective

/-- The canonical coefficient of the representative in the specified coordinate. -/
def coordinateValue (n : ℕ) (i : Fin (n + 1)) : (Fin (n + 1) → G) →* G :=
  (coordinateSign G i.val).symm.toMonoidHom.comp (euler G (n + 1))

@[simp] theorem coordinateValue_apply (n : ℕ) (i : Fin (n + 1))
    (y : Fin (n + 1) → G) :
    coordinateValue G n i y =
      if Even i.val then euler G (n + 1) y else (euler G (n + 1) y)⁻¹ := by
  change (coordinateSign G i.val).symm (euler G (n + 1) y) = _
  rw [coordinateSign_symm, coordinateSign_apply]

/-- An actual section of Euler supported at the specified coordinate. -/
def coordinateSection (n : ℕ) (i : Fin (n + 1)) : G →* (Fin (n + 1) → G) :=
  (singleCoordinate G i).comp (coordinateSign G i.val).symm.toMonoidHom

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem coordinateSection_head_div_euler_tail (n : ℕ) (i : Fin (n + 1)) (x : G) :
    coordinateSection G n i x 0 / euler G n (Fin.tail (coordinateSection G n i x)) = x := by
  change euler G (n + 1) (singleCoordinate G i ((coordinateSign G i.val).symm x)) = x
  rw [euler_singleCoordinate, MulEquiv.apply_symm_apply]


/-- The canonical representative of the original incidence coset. -/
def coordinateRepresentative (n : ℕ) (i : Fin (n + 1)) :
    (Fin (n + 1) → G) →* (Fin (n + 1) → G) :=
  (coordinateSection G n i).comp (euler G (n + 1))

@[simp] theorem coordinateRepresentative_apply (n : ℕ) (i : Fin (n + 1))
    (y : Fin (n + 1) → G) :
    coordinateRepresentative G n i y = Pi.mulSingle i (coordinateValue G n i y) := rfl

/-- The representative has the same original Euler product. -/
@[simp] theorem mulSingle_head_div_euler_tail (n : ℕ) (i : Fin (n + 1)) (x : G) :
    Pi.mulSingle (M := fun _ => G) i x 0 / euler G n (Fin.tail (Pi.mulSingle (M := fun _ => G) i
        x)) =
      if Even i.val then x else x⁻¹ := by
  simpa only [singleCoordinate_apply, euler_succ, coordinateSign_apply]
    using euler_singleCoordinate G i x


/-- There is a unique original adjacent-disk tuple taking the canonical
single-coordinate representative to the given term tuple. -/
theorem existsUnique_incidence_representative (n : ℕ) (i : Fin (n + 1))
    (y : Fin (n + 1) → G) :
    ∃! d : Fin n → G, incidence G n d * coordinateRepresentative G n i y = y := by
  have h : euler G (n + 1) (y / coordinateRepresentative G n i y) = 1 := by
    rw [map_div]
    change euler G (n + 1) y /
      (coordinateSection G n i (euler G (n + 1) y) 0 /
        euler G n (Fin.tail (coordinateSection G n i (euler G (n + 1) y)))) = 1
    rw [coordinateSection_head_div_euler_tail, div_self']
  obtain ⟨d, hd⟩ := (euler_eq_one_iff G n _).mp h
  refine ⟨d, ?_, ?_⟩
  · change incidence G n d * coordinateRepresentative G n i y = y
    rw [hd, div_mul_cancel]
  · intro d' hd'
    apply incidence_injective G n
    apply mul_right_cancel (b := coordinateRepresentative G n i y)
    exact hd'.trans (by rw [hd, div_mul_cancel])

/-- The single-coordinate coefficient is uniquely determined modulo the
image of the original incidence homomorphism. -/
theorem existsUnique_coordinateValue (n : ℕ) (i : Fin (n + 1))
    (y : Fin (n + 1) → G) :
    ∃! c : G, ∃ d : Fin n → G, incidence G n d * singleCoordinate G i c = y := by
  obtain ⟨d, hd, _⟩ := existsUnique_incidence_representative G n i y
  refine ⟨coordinateValue G n i y, ⟨d, hd⟩, ?_⟩
  rintro c ⟨d', hd'⟩
  apply (coordinateSign G i.val).injective
  have h := congrArg (euler G (n + 1)) hd'
  rw [map_mul, euler_incidence, one_mul, euler_singleCoordinate] at h
  exact h.trans (by
    change euler G (n + 1) y = coordinateSign G i.val
      ((coordinateSign G i.val).symm (euler G (n + 1) y))
    rw [MulEquiv.apply_symm_apply])

/-- Full uniqueness of the original incidence term and its single-coordinate
representative; this includes the empty disk tuple `n = 0`. -/
theorem existsUnique_incidence_coordinate (n : ℕ) (i : Fin (n + 1))
    (y : Fin (n + 1) → G) :
    ∃! p : (Fin n → G) × G, incidence G n p.1 * singleCoordinate G i p.2 = y := by
  obtain ⟨d, hd, hu⟩ := existsUnique_incidence_representative G n i y
  refine ⟨(d, coordinateValue G n i y), hd, ?_⟩
  rintro ⟨d', c⟩ hc
  have he : c = coordinateValue G n i y :=
    (existsUnique_coordinateValue G n i y).unique ⟨d', hc⟩ ⟨d, hd⟩
  subst c
  exact Prod.ext (hu d' hc) rfl

end MonoidHom.FiniteAdjacentComplex
