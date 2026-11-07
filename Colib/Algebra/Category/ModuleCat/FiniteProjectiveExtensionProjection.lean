/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionLinear
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionLocalization

/-!
Implementation provenance:
`Quillen/KTheory/Plus/ProjectiveExtensionProjection.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The actual localized extension projection to the original Q-construction -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
attribute [local instance] MonoidalLeftAction.trivial extensionProjectionLinear

/-- Ignore the projective denominator and take the original extension quotient. -/
def extensionPairProjection : IsoCategory R × (exactStructure R).ExtensionTotal ⥤
    QConstruction (exactStructure R).deflation (exactStructure R).inflation :=
  CategoryTheory.Prod.snd _ _ ⋙ (exactStructure R).extensionProjection

/-- The pair projection carries the genuine quotient lineator. -/
@[instance_reducible]
def extensionPairProjectionLinear : (extensionPairProjection R).LaxLeftLinear (IsoCategory R) where
  μₗ S x := Functor.LaxLeftLinear.μₗ (exactStructure R).extensionProjection S x.2
  μₗ_naturality_left f x :=
    Functor.LaxLeftLinear.μₗ_naturality_left (exactStructure R).extensionProjection f x.2
  μₗ_naturality_right S _ _ f :=
    Functor.LaxLeftLinear.μₗ_naturality_right (exactStructure R).extensionProjection S f.2
  μₗ_associativity S T x :=
    Functor.LaxLeftLinear.μₗ_associativity (exactStructure R).extensionProjection S T x.2
  μₗ_unitality x :=
    Functor.LaxLeftLinear.μₗ_unitality (exactStructure R).extensionProjection x.2

attribute [local instance] extensionPairProjectionLinear

/-- The actual Grayson localized total category maps to the original Q-category.
The arrow map descends through the existing localization relation. -/
def localizedExtensionProjection : LocalizedExtensionCategory R ⥤
    QConstruction (exactStructure R).deflation (exactStructure R).inflation :=
  GroupCompletion.ActionLocalization.mapFunctor (extensionPairProjection R) ⋙
    GroupCompletion.ActionLocalization.TrivialAction.forgetFunctor _ _

@[simp]
theorem localizedExtensionProjection_obj (A : IsoCategory R)
    (x : (exactStructure R).ExtensionTotal) :
    (localizedExtensionProjection R).obj (localizedExtensionPair R A x) =
      (exactStructure R).extensionProjectionQObj x := rfl

/-- On a representative, first remove the common direct summand from the
quotient and then apply the original Q-span projection. -/
theorem localizedExtensionProjection_map_mkHom
    {A B : IsoCategory R} {x y : (exactStructure R).ExtensionTotal}
    (S : IsoCategory R) (f : S ⊗ A ⟶ B) (g : S ⊙ₗ x ⟶ y) :
    (localizedExtensionProjection R).map
        (GroupCompletion.Localization.mkHom (X := (A, x)) (Y := (B, y)) S f g) =
      ((exactStructure R).qIsoOfIso (directSumExtensionQuotientIso R S x)).inv ≫
        (exactStructure R).extensionProjectionQMap g := rfl

end ModuleCat.FiniteProjective
