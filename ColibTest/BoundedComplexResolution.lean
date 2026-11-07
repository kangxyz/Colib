module

public import Colib.CategoryTheory.ExactCategory.Resolution.BoundedComplex
public import Colib.CategoryTheory.ExactCategory.Resolution.LiftSubcategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  [(abelianExactStructure C).IsKernelClosed P]
  (K : CochainComplex C ℤ) (M : C)
  (f : K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) [QuasiIso f]
  (hterms : ∀ i, P (K.X i))

-- Arbitrary ambient object/hom universes and separate bounds are retained.
example (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    (abelianExactStructure C).FiniteResolution P M :=
  K.finiteResolutionOfQuasiIsoSingle P M f hterms a b

-- Objectwise bounds, not a uniform dimension bound, suffice.
example (hbounded : (∃ a : ℤ, K.IsStrictlyGE a) ∧ ∃ b : ℤ, K.IsStrictlyLE b) :
    Nonempty ((abelianExactStructure C).FiniteResolution P M) :=
  K.nonempty_finiteResolution_of_quasiIso_single P M f hterms hbounded

-- The construction also works when the interval is concentrated in degree zero.
example [K.IsStrictlyGE 0] [K.IsStrictlyLE 0] :
    (abelianExactStructure C).FiniteResolution P M :=
  K.finiteResolutionOfQuasiIsoSingle P M f hterms 0 0

-- The proof imposes no a <= b premise, even for an empty support interval.
example [K.IsStrictlyGE 2] [K.IsStrictlyLE (-2)] :
    (abelianExactStructure C).FiniteResolution P M :=
  K.finiteResolutionOfQuasiIsoSingle P M f hterms 2 (-2)

variable (Q : ObjectProperty C) [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  [Q.IsClosedUnderFiniteProducts] [(abelianExactStructure C).IsExtensionClosed Q]
  [(abelianExactStructure C).IsKernelClosed Q]

-- Lifting retains the actual tower length, rather than only existence.
example (hPQ : ∀ X, P X → Q X) (R : (abelianExactStructure C).FiniteResolution P M)
    (hM : Q M) : (R.liftToSubcategory hPQ hM).length = R.length :=
  R.length_liftToSubcategory hPQ hM
