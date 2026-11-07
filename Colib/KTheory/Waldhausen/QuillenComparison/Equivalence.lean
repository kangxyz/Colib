/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.QuillenComparison.RowEssentialSurjective
public import Colib.KTheory.Waldhausen.QuillenComparison.Factorization
public import Colib.KTheory.Waldhausen.QuillenComparison.ExactNaturality
public import Colib.Topology.Realization.BisimplicialEquivalence
public import Colib.Topology.ClassifyingSpace.MixedNerve
public import Colib.Topology.Realization.ChainCoreNerve

/-! # The canonical exact-category Q/S equivalence

The row comparison is an actual categorical equivalence, proved by
full-faithful span reconstruction and essential surjectivity. Rowwise
realization equivalence, partial edgewise subdivision and classification
diagonal contraction then prove that the prescribed Q/S map realizes to a
homotopy equivalence. Both sides of its based zigzag retain the chosen zero
vertices, giving the canonical isomorphism on the already-defined K-groups.

The mathematical comparison is due to Waldhausen, Section 1.9, pp. 375-376.
The construction here retains the prescribed map in the unnormalized
IsZero-diagonal model; the earlier Lean implementation is credited separately.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/QuillenComparison/Equivalence.lean at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual native weak rows,
   chain-core nerve and prescribed comparison map are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuillenComparison
open QuotientRows SSet

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- The rowwise categorical equivalences give an equivalence of the actual
bisimplicial diagonal realizations. -/
def rowComparisonHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      |diagonalSSet (EdgewiseSubdivision.ε.op ⋙ weakRowNerve (ofExactCategory E))|
      |diagonalSSet (chainCoreNerve (QConstruction E.deflation E.inflation))| :=
  SSet.BisimplicialRealization.diagonalRealizationHomotopyEquiv (rowChainNerveMap E)
    (fun n ↦ MixedNerve.realizationEquivalence.{u, v, max u v} (rowChainEquivalence E ⦋n⦌))
    (fun _ ↦ rfl)

@[simp]
theorem rowComparisonHomotopyEquiv_toFun :
    (rowComparisonHomotopyEquiv E).toFun =
      (SSet.toTop.map (diagonalMap (rowChainNerveMap E))).hom := rfl

/-- The row-coordinate Q comparison is an actual realization homotopy equivalence. -/
def rowsToQHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      |diagonalSSet (EdgewiseSubdivision.ε.op ⋙ weakRowNerve (ofExactCategory E))|
      |nerve (QConstruction E.deflation E.inflation)| :=
  (rowComparisonHomotopyEquiv E).trans
    (SSet.ChainCore.realizationHomotopyEquiv (QConstruction E.deflation E.inflation))

@[simp]
theorem rowsToQHomotopyEquiv_toFun :
    (rowsToQHomotopyEquiv E).toFun = (SSet.toTop.map (rowsToQ E)).hom := by
  simp only [rowsToQHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans,
    rowComparisonHomotopyEquiv_toFun, SSet.ChainCore.realizationHomotopyEquiv_toFun,
    rowsToQ, Functor.map_comp]
  rfl

/-- The canonical Q/S comparison map itself realizes to a homotopy equivalence. -/
def realizationComparisonHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (SubdivisionSpace E) E.KSpace := by
  let h := (subdivisionToRowsHomotopyEquiv E).trans (rowsToQHomotopyEquiv E)
  have hh : h.toFun = (realizationComparison E).hom := by
    change (rowsToQHomotopyEquiv E).toFun.comp (subdivisionToRowsHomotopyEquiv E).toFun = _
    rw [rowsToQHomotopyEquiv_toFun, subdivisionToRowsHomotopyEquiv_toFun]
    change (SSet.toTop.map (subdivisionToRows E) ≫ SSet.toTop.map (rowsToQ E)).hom = _
    rw [← Functor.map_comp, comparisonMap_factorization]
    rfl
  exact {
    toFun := (realizationComparison E).hom
    invFun := h.invFun
    left_inv := by rw [← hh]; exact h.left_inv
    right_inv := by rw [← hh]; exact h.right_inv }

@[simp]
theorem realizationComparisonHomotopyEquiv_toFun :
    (realizationComparisonHomotopyEquiv E).toFun = (realizationComparison E).hom := rfl

theorem realizationComparisonHomotopyEquiv_basepoint :
    realizationComparisonHomotopyEquiv E (subdivisionBasepoint E) = E.kBasepoint :=
  realizationComparison_basepoint E

/-- The original exact-category S-delooping and Quillen Q-space have the same
homotopy type, by the canonical comparison zigzag. -/
def deloopingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ofExactCategory E).Delooping E.KSpace :=
  (EdgewiseSubdivision.realizationHomotopyEquiv
    (sSet E.inflation (MorphismProperty.isomorphisms C))).symm.trans
      (realizationComparisonHomotopyEquiv E)

/-- The right leg of the canonical based comparison zigzag is a K-group isomorphism. -/
def subdivisionComparisonKEquiv (n : ℕ) : SubdivisionK E n ≃* E.K n :=
  Topology.homotopyEquivPiEquiv (realizationComparisonHomotopyEquiv E)
    (realizationComparison_basepoint E) n

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem subdivisionComparisonKEquiv_coe (n : ℕ) :
    (↑(subdivisionComparisonKEquiv E n) : SubdivisionK E n →* E.K n) = subdivisionComparisonK E
        n := rfl


/-- The canonical comparison between the already-defined Waldhausen and
Quillen K-groups, with no equivalence hypothesis among its inputs. -/
def comparisonKEquiv (n : ℕ) : (ofExactCategory E).K n ≃* E.K n :=
  (subdivisionKEquiv E n).symm.trans (subdivisionComparisonKEquiv E n)

/-- Its underlying map is exactly the previously constructed canonical comparison. -/
@[simp] theorem comparisonKEquiv_coe (n : ℕ) :
    (↑(comparisonKEquiv E n) : (ofExactCategory E).K n →* E.K n) = comparisonK E n := rfl


variable {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
  {E' : ExactCategory.ExactStructure D}

/-- The actual based Q/S isomorphism commutes with both original canonical K-maps,
without an extra pushout-preservation, strict-zero or equivalence hypothesis. -/
theorem comparisonKEquiv_exactFunctor_naturality (F : ExactCategory.ExactFunctor E E') (n : ℕ) :
    (comparisonKEquiv E' n).toMonoidHom.comp (Waldhausen.KMap F.waldhausenExact n) =
      (F.KMap n).comp (comparisonKEquiv E n).toMonoidHom := comparisonK_naturality F n

end CategoryTheory.Waldhausen.QuillenComparison

attribute [colib_tag "COL-0243",
  colib_ref "quillen" "Quillen/Waldhausen/QuillenComparison/Equivalence.lean"
    "adaptation" "Actual Q/S homotopy equivalence and the canonical all-degree K-isomorphism"]
  CategoryTheory.Waldhausen.QuillenComparison.realizationComparisonHomotopyEquiv
  CategoryTheory.Waldhausen.QuillenComparison.realizationComparisonHomotopyEquiv_toFun
  CategoryTheory.Waldhausen.QuillenComparison.deloopingHomotopyEquiv
  CategoryTheory.Waldhausen.QuillenComparison.subdivisionComparisonKEquiv
  CategoryTheory.Waldhausen.QuillenComparison.comparisonKEquiv
  CategoryTheory.Waldhausen.QuillenComparison.comparisonKEquiv_coe

attribute [colib_tag "COL-0243",
  colib_ref "quillen" "Quillen/Waldhausen/QuillenComparison/ExactNaturality.lean"
    "adaptation" "Unconditional naturality with both original canonical exact-functor K-map APIs"]
  CategoryTheory.Waldhausen.QuillenComparison.comparisonKEquiv_exactFunctor_naturality

attribute [colib_tag "COL-0243",
  colib_ref "quillen" "Quillen/Waldhausen/QuillenComparison/RowEssentialSurjective.lean"
    "adaptation" "The native weak-row comparison is an actual categorical equivalence"]
  CategoryTheory.Waldhausen.QuillenComparison.rowChainEquivalence

attribute [colib_ref "Waldhausen1985" "Section 1.9, pp. 375-376" "adaptation"
  "Waldhausen's edgewise-subdivision Q/S comparison, adapted to the unnormalized \
  IsZero-diagonal model and retaining the prescribed comparison map"]
  CategoryTheory.Waldhausen.QuillenComparison.realizationComparisonHomotopyEquiv
  CategoryTheory.Waldhausen.QuillenComparison.deloopingHomotopyEquiv
  CategoryTheory.Waldhausen.QuillenComparison.comparisonKEquiv
