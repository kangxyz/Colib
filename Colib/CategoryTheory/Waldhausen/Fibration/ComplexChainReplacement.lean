/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.Fibration.MixedChainReplacement
public import Colib.CategoryTheory.Waldhausen.SplitComplexes.Approximation
public import Colib.CategoryTheory.Waldhausen.SplitComplexes.FunctorialFactorization

/-! # The genuine isomorphism/quasi-isomorphism finite-chain replacement

The actual identity-cone factorization is retained on any cone-closed exact
full complex subcategory. Its inherited ambient cofibration property follows
from its already-proved split cofibration property. Fine preservation is
proved from actual functoriality on squares with isomorphic endpoints; the
projection is only asserted to be a genuine quasi-isomorphism.
-/
/-! Adapted from `Quillen.Waldhausen.Fibration.ComplexChainReplacement`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The actual fine isomorphisms and coarse quasi-isomorphisms on the inherited exact category. -/
def complexSubcategoryNested : NestedWeakEquivalences
    (ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)) where
  coarse := complexSubcategory P
  cof_eq := rfl
  zero_eq := rfl
  le_weq := by
    intro X Y f hf
    let : IsIso f := hf
    change QuasiIso f.hom
    infer_instance

variable (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
  ∀ f : K ⟶ L, P (mappingCone f))

/-- The unchanged identity-cone factorization, with the actual inherited ambient cofibration
class. -/
def complexSubcategoryFactorization : FunctorialFactorization (complexSubcategory P) where
  middle := subcategoryMiddleFunctor P hcone
  inclusion := (splitSubcategoryFunctorialFactorization P hcone).inclusion
  projection := (splitSubcategoryFunctorialFactorization P hcone).projection
  factorization := (splitSubcategoryFunctorialFactorization P hcone).factorization
  cofibration f := ((splitSubcategoryFunctorialFactorization P hcone).cofibration f).1
  weak := (splitSubcategoryFunctorialFactorization P hcone).weak

/-- Both original cylinder factors and the middle functor are unchanged. -/
@[simp] theorem complexSubcategoryFactorization_middle :
    (complexSubcategoryFactorization P hcone).middle = subcategoryMiddleFunctor P hcone := rfl

@[simp] theorem complexSubcategoryFactorization_inclusion (f : Arrow P.FullSubcategory) :
    ((complexSubcategoryFactorization P hcone).inclusion.app f).hom =
      CochainComplex.SplitFactorization.inclusion f.hom.hom := rfl

@[simp] theorem complexSubcategoryFactorization_projection (f : Arrow P.FullSubcategory) :
    ((complexSubcategoryFactorization P hcone).projection.app f).hom =
      CochainComplex.SplitFactorization.projection f.hom.hom := rfl

/-- A square with genuinely isomorphic endpoints induces an isomorphism of the actual cylinders. -/
theorem complexSubcategoryFactorization_fineSquares :
    MixedChainReplacement.PreservesFineSquares (complexSubcategoryNested P)
      (complexSubcategoryFactorization P hcone) := by
  intro f g α hαl hαr
  let : IsIso α.left := hαl
  let : IsIso α.right := hαr
  let : IsIso α := Arrow.isIso_of_isIso_left_of_isIso_right α
  change IsIso ((subcategoryMiddleFunctor P hcone).map α)
  infer_instance

/-- The original finite cylinder replacement preserves every pointwise chain isomorphism. -/
theorem complexFiniteReplacement_map_fine (n : ℕ)
    {F G : ComposableArrows P.FullSubcategory n} (α : F ⟶ G)
    (hα : ∀ i, IsIso (α.app i)) (i : Fin (n + 1)) :
    IsIso (((FunctorialFactorization.finiteReplacement
      (complexSubcategoryFactorization P hcone) n).map α).app i) :=
  MixedChainReplacement.finiteReplacement_map_fine (complexSubcategoryNested P)
    (complexSubcategoryFactorization P hcone) (complexSubcategoryFactorization_fineSquares P hcone)
    n α hα i

/-- Original quasi-isomorphism chains become actual inherited cofibration/quasi-isomorphism
chains. -/
theorem complexFiniteReplacement_map_cof_quasi (n : ℕ)
    (F : ComposableArrows P.FullSubcategory n)
    (hF : ∀ {i j : Fin (n + 1)} (f : i ⟶ j), QuasiIso (F.map f).hom)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    subcategoryCofibrations P (((FunctorialFactorization.finiteReplacement
      (complexSubcategoryFactorization P hcone) n).obj F).map f) ∧
    QuasiIso ((((FunctorialFactorization.finiteReplacement
      (complexSubcategoryFactorization P hcone) n).obj F).map f).hom) := by
  let : (complexSubcategoryNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated P
  exact MixedChainReplacement.finiteReplacement_map_cof_coarse (complexSubcategoryNested P)
    (complexSubcategoryFactorization P hcone) n F hF f

/-- The original finite projection remains an actual quasi-isomorphism at each vertex. -/
theorem complexFiniteProjection_quasi (n : ℕ)
    (F : ComposableArrows P.FullSubcategory n) (i : Fin (n + 1)) :
    QuasiIso ((((FunctorialFactorization.finiteProjection
      (complexSubcategoryFactorization P hcone) n).app F).app i).hom) :=
  MixedChainReplacement.finiteProjection_coarse (complexSubcategoryNested P)
    (complexSubcategoryFactorization P hcone) n F i

end CategoryTheory.Waldhausen.Fibration
