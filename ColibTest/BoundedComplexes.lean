module

import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.SingleInsertion
import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationExact

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open HomologicalComplex CochainComplex

universe v u

variable {A : Type (max u v)} [Category.{v} A] [Abelian A]

example (K : CochainComplex A ℤ) (a b : ℤ) :
    HasTermBounds K a b ↔ K.IsStrictlyGE a ∧ K.IsStrictlyLE b :=
  hasTermBounds_iff_isStrictlyGE_isStrictlyLE K a b

example (K : CochainComplex A ℤ) :
    TermBounded K ↔ ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b :=
  termBounded_iff_exists_isStrictlyGE_isStrictlyLE K

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

example (n : ℤ) (X : P.FullSubcategory) :
    ((boundedTermsSingleFunctor P n).obj X).obj =
      (single A (ComplexShape.up ℤ) n).obj X.obj := rfl

example (n : ℤ) (X : P.FullSubcategory) :
    (((boundedTermsSingleFunctor P n).obj X).obj).X n ≅ X.obj :=
  singleObjXSelf (ComplexShape.up ℤ) n X.obj

example (n : ℤ) {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((boundedTermsSingleFunctor P n).map f).hom =
      (single A (ComplexShape.up ℤ) n).map f.hom :=
  boundedTermsSingleFunctor_map P n f

section Exact

attribute [local instance] Abelian.hasFiniteBiproducts

variable [(abelianExactStructure A).IsExtensionClosed P]

local instance : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

example (n : ℤ) {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((boundedTermsSingleExactFunctor P n).toFunctor.map f).hom =
      (single A (ComplexShape.up ℤ) n).map f.hom :=
  boundedTermsSingleFunctor_map P n f

variable [(abelianExactStructure A).IsKernelClosed P]

example (n : ℤ) {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    ((acyclicTruncationSequenceFunctor P n).map f).τ₂ = f :=
  acyclicTruncationSequenceFunctor_map_middle P n f

example (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    (boundedAcyclicExactStructure P).conflation
      ((acyclicTruncationSequenceFunctor P n).obj K) :=
  acyclicTruncationSequenceFunctor_conflation P n K

end Exact
