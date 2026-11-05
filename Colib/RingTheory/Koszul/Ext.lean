/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Abelian.Projective.Ext
public import Colib.Util.References
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import StacksFrontier.RingTheory.Koszul.TorComparison.QuotientTor

/-!
# Ext bounds from the native Koszul resolution

A weakly regular finite sequence gives its ideal quotient projective dimension
at most its length. Native Ext above this length vanishes for arbitrary
coefficients and every supported Ext universe. We use Stacks' exterior-power
Koszul complex, its actual augmentation, and its existing projective resolution.
No Noetherianity, nontriviality, or properness of the generated ideal is assumed.

The list endpoints adapt `Aglib.Algebra.Homology.Koszul.Ext` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The recursive tensor model of that source
is not imported or reconstructed. Only the list and finite-function indexing and
the equal generated ideals are identified; the endpoints refer to the same
quotient object and the native Ext classes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-- Every Ext class above the length of a weakly regular sequence vanishes. -/
theorem ext_eq_zero_of_isWeaklyRegular [HasExt.{w} (ModuleCat.{u} R)]
    (f : Fin r → R) (hf : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f))
    (N : ModuleCat.{u} R) (n : ℕ) (hn : r < n)
    (e : Ext (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) N n) : e = 0 := by
  have hreg : IsKoszulRegular f := (isKoszulRegularOn_self_iff f).mp
    (isKoszulRegularOn_and_isKoszulRegular_of_regular.1 hf)
  exact (seqProjectiveResolution f hreg).ext_eq_zero_of_isZero_X n
    (seqComplex_isZero_of_lt f n hn) e

/-- The quotient by a weakly regular sequence has projective dimension at most its length. -/
theorem hasProjectiveDimensionLE_quotient_of_isWeaklyRegular
    (f : Fin r → R) (hf : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f)) :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) r := by
  let := HasExt.standard (ModuleCat.{u} R)
  apply HasProjectiveDimensionLT.mk
  intro n hn N e
  exact ext_eq_zero_of_isWeaklyRegular f hf N n (by omega) e

/-- The quotient by a weakly regular list has projective dimension at most the
list length, including the empty list. -/
theorem quotient_hasProjectiveDimensionLE_of_weaklyRegular
    (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.ofList s)) s.length := by
  have hI : Ideal.span (Set.range s.get) = Ideal.ofList s := by
    congr 1
    ext x
    exact List.mem_iff_get.symm
  have hs' : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s.get) := by
    simpa only [List.ofFn_get] using hs
  rw [← hI]
  exact hasProjectiveDimensionLE_quotient_of_isWeaklyRegular s.get hs'

/-- Every Ext class above the length of a weakly regular list vanishes, with no
restriction on the coefficient module or supported Ext universe. -/
theorem ext_eq_zero_above_length [HasExt.{w} (ModuleCat.{u} R)]
    (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (N : ModuleCat.{u} R) (n : ℕ) (hn : s.length < n)
    (e : Ext (ModuleCat.of R (R ⧸ Ideal.ofList s)) N n) : e = 0 := by
  let := quotient_hasProjectiveDimensionLE_of_weaklyRegular s hs
  exact e.eq_zero_of_hasProjectiveDimensionLT (s.length + 1) (by omega)

attribute [colib_tag "COL-0021"] ext_eq_zero_of_isWeaklyRegular
  hasProjectiveDimensionLE_quotient_of_isWeaklyRegular
  quotient_hasProjectiveDimensionLE_of_weaklyRegular ext_eq_zero_above_length

add_to_stacks 062F
  "Ingredient only: weak regularity gives Koszul acyclicity; Ext vanishing follows"
  ext_eq_zero_above_length
add_to_stacks 0CXC
  "Ingredient only: a finite projective resolution gives the projective dimension bound"
  quotient_hasProjectiveDimensionLE_of_weaklyRegular

end Koszul
