/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.FixedBounds
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.IdentityDisk
public import Colib.Algebra.Homology.CochainComplex.Cycles

/-! # Actual interior cycles of an acyclic finite-term stratum

For genuine term bounds [a,b], acyclicity forces cycles in every degree ≤ a
to vanish, while term vanishing forces cycles in every degree > b to vanish.
Thus the free cycle indices are precisely the interior degrees a+1,...,b.
The identity disk in degrees n,n+1 has just its upper cycle as a free object.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteCycleBounds`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Exactness and a genuinely zero preceding term force the actual cycles to vanish. -/
theorem cycles_isZero_of_prev_isZero (K : CochainComplex A ℤ) (n : ℤ)
    (hn : K.ExactAt n) (hz : IsZero (K.X (n - 1))) : IsZero (K.cycles n) := by
  let : Epi (K.toCycles (n - 1) ((n - 1) + 1)) :=
    _root_.CochainComplex.epi_toCycles_of_exactAt K (n - 1) (by simpa only [sub_add_cancel]
      using hn)
  simpa only [sub_add_cancel] using IsZero.of_epi (K.toCycles (n - 1) ((n - 1) + 1)) hz

/-- The lower-end cycle, and every earlier cycle, really is zero. -/
theorem HasTermBounds.cycles_isZero_of_le {K : CochainComplex A ℤ} {a b n : ℤ}
    (hK : HasTermBounds K a b) (hn : K.ExactAt n) (ha : n ≤ a) : IsZero (K.cycles n) :=
  cycles_isZero_of_prev_isZero K n hn (hK (n - 1) (Or.inl (by omega)))

/-- Cycles above the upper term bound are zero without an acyclicity hypothesis. -/
theorem HasTermBounds.cycles_isZero_of_gt {K : CochainComplex A ℤ} {a b n : ℤ}
    (hK : HasTermBounds K a b) (hb : b < n) : IsZero (K.cycles n) :=
  IsZero.of_mono (K.iCycles n) (hK n (Or.inr hb))

/-- Every actual cycle outside the interior interval vanishes. -/
theorem HasTermBounds.cycles_isZero_outside {K : CochainComplex A ℤ} {a b n : ℤ}
    (hK : HasTermBounds K a b) (ha : K.Acyclic) (hn : n ≤ a ∨ b < n) : IsZero (K.cycles n) :=
  hn.elim (hK.cycles_isZero_of_le (ha n)) hK.cycles_isZero_of_gt

/-- The original smart truncation retains every specified actual term bound. -/
theorem HasTermBounds.truncLE {K : CochainComplex A ℤ} {a b : ℤ}
    (hK : HasTermBounds K a b) (n : ℤ) : HasTermBounds (K.truncLE n) a b := by
  intro i hi
  let : Mono ((K.ιTruncLE n).f i) := (truncationDegree_shortExact K n i).mono_f
  exact IsZero.of_mono ((K.ιTruncLE n).f i) (hK i hi)

/-- For an acyclic complex the original smart truncation is already zero
at the lower term bound, rather than only strictly below that bound. -/
theorem truncLE_isZero_at_lower_bound (K : CochainComplex A ℤ) (a b : ℤ)
    (hK : HasTermBounds K a b) (ha : K.Acyclic) : IsZero (K.truncLE a) := by
  rw [IsZero.iff_id_eq_zero]
  ext i
  rcases lt_trichotomy i a with hi | he | hi
  · let : Mono ((K.ιTruncLE a).f i) := (truncationDegree_shortExact K a i).mono_f
    exact (IsZero.of_mono ((K.ιTruncLE a).f i) (hK i (Or.inl hi))).eq_of_src _ _
  · subst i
    exact ((hK.cycles_isZero_of_le (ha a) le_rfl).of_iso (K.truncLEXIsoCycles a)).eq_of_src _ _
  · exact ((K.truncLE a).isZero_of_isStrictlyLE a i hi).eq_of_src _ _

/-- The actual disk has its original strict two-term bounds. -/
theorem identityDisk_hasTermBounds (n : ℤ) (X : A) : HasTermBounds (identityDisk n X) n (n + 1) :=
  fun i hi ↦ identityDisk_isZero n X i (by omega) (by omega)

/-- Every other actual cycle of the identity disk is zero. -/
theorem identityDisk_cycles_isZero (n : ℤ) (X : A) (j : ℤ) (hj : j ≠ n + 1) :
    IsZero ((identityDisk n X).cycles j) :=
  (identityDisk_hasTermBounds n X).cycles_isZero_outside (identityDisk_acyclic n X) (by omega)

/-- The original upper cycle inclusion identifies the disk's unique free cycle. -/
def identityDiskCyclesIso (n : ℤ) (X : A) : (identityDisk n X).cycles (n + 1) ≅ X :=
  (identityDisk n X).iCyclesIso (n + 1) (n + 2) (by simp; omega)
    ((identityDisk_isZero n X (n + 2) (by omega) (by omega)).eq_of_tgt _ _) ≪≫ identityDiskIso₁ n X

@[simp] theorem identityDiskCyclesIso_hom (n : ℤ) (X : A) :
    (identityDiskCyclesIso n X).hom = (identityDisk n X).iCycles (n + 1) ≫ (identityDiskIso₁ n
      X).hom := rfl

/-- The actual unique disk-cycle coordinate is natural for every original map. -/
def identityDiskCyclesNatIso (n : ℤ) :
    identityDiskFunctor (A := A) n ⋙ cyclesFunctor A (ComplexShape.up ℤ) (n + 1) ≅ 𝟭 A :=
  NatIso.ofComponents (identityDiskCyclesIso n) (by
    intro X Y f
    change cyclesMap (identityDiskMap n f) (n + 1) ≫ (identityDiskCyclesIso n Y).hom =
      (identityDiskCyclesIso n X).hom ≫ f
    rw [identityDiskCyclesIso_hom, identityDiskCyclesIso_hom, ← Category.assoc, cyclesMap_i]
    simp [identityDiskMap_f₁])

end CochainComplex
