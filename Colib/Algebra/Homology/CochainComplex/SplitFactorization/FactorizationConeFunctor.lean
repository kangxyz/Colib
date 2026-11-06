/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationFunctor
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationSign
public import Colib.Algebra.Homology.MappingCone.ShortExact

/-!
# Functorial original signed factorization sequences

The original middle-object maps intertwine the original sign-adjusted quotient with the literal
cone maps. For an actual natural transformation this gives its original inclusion, projection and
signed cone quotient as natural transformations. The middle functor preserves arbitrary short
exact coefficient sequences, using actual identity cones and binary biproducts.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationConeFunctor`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
universe u v u' v'
namespace CochainComplex.SplitFactorization
variable {A : Type u} [Category.{v} A] [Abelian A]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The original signed quotient is natural for the actual commuting square. -/
theorem quotientToCone_naturality {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g) :
    middleFunctor.map α ≫ quotientToCone g.hom =
      quotientToCone f.hom ≫ mappingCone.map f.hom g.hom α.left α.right α.w.symm := by
  apply biprod.hom_ext'
  · ext n
    simp [middleFunctor, identityConeFunctor, quotientToCone, quotientMap,
      CochainComplex.mappingConeNegIso, mappingCone.map,
      mappingCone.ext_from_iff _ (n + 1) n rfl]
    simp only [← comp_f, ← Category.assoc, α.w]
  · ext n
    simp [middleFunctor, quotientToCone, quotientMap,
      CochainComplex.mappingConeNegIso, mappingCone.map]

variable {D : Type u'} [Category.{v'} D] {F G : D ⥤ CochainComplex A ℤ} (α : F ⟶ G)

/-- The actual arrow and commuting square of the original natural transformation. -/
def natTransArrowFunctor : D ⥤ Arrow (CochainComplex A ℤ) where
  obj X := Arrow.mk (α.app X)
  map f := Arrow.homMk (F.map f) (G.map f) (α.naturality f)
  map_id X := by apply Arrow.hom_ext <;> simp
  map_comp f g := by apply Arrow.hom_ext <;> simp

/-- The original middle functor on the actual squares of a natural transformation. -/
def middleNatTransFunctor : D ⥤ CochainComplex A ℤ :=
  natTransArrowFunctor α ⋙ middleFunctor

/-- The literal first factor is natural in the coefficient. -/
def inclusionNatTrans : F ⟶ middleNatTransFunctor α where
  app X := inclusion (α.app X)
  naturality X Y f :=
    (inclusion_naturality (Arrow.homMk (f := Arrow.mk (α.app X)) (g := Arrow.mk (α.app Y))
      (F.map f) (G.map f) (α.naturality f))).symm

/-- The literal fine weak projection is natural in the coefficient. -/
def projectionNatTrans : middleNatTransFunctor α ⟶ G where
  app X := projection (α.app X)
  naturality X Y f :=
    projection_naturality (Arrow.homMk (f := Arrow.mk (α.app X)) (g := Arrow.mk (α.app Y))
      (F.map f) (G.map f) (α.naturality f))

/-- The original signed quotient, into the actual cone functor. -/
def quotientToConeNatTrans : middleNatTransFunctor α ⟶ mappingConeNatTransFunctor α where
  app X := quotientToCone (α.app X)
  naturality X Y f :=
    quotientToCone_naturality (Arrow.homMk (f := Arrow.mk (α.app X)) (g := Arrow.mk (α.app Y))
      (F.map f) (G.map f) (α.naturality f))

/-- The two original factors retain precisely the input natural transformation. -/
theorem inclusionNatTrans_projection : inclusionNatTrans α ≫ projectionNatTrans α = α := by
  apply NatTrans.ext
  funext X
  exact inclusion_projection (α.app X)

/-- The unchanged inclusion and signed quotient compose to zero. -/
theorem inclusionNatTrans_quotientToCone :
    inclusionNatTrans α ≫ quotientToConeNatTrans α = 0 := by
  apply NatTrans.ext
  funext X
  exact inclusion_quotientToCone (α.app X)

variable [Preadditive D] [F.Additive] [G.Additive]

instance identityConeFunctor_additive : (identityConeFunctor (A := A)).Additive where
  map_add {X Y} f g := by
    ext n
    simp [identityConeFunctor, mappingCone.map,
      mappingCone.ext_from_iff _ (n + 1) n rfl, Preadditive.comp_add, Preadditive.add_comp]

instance middleNatTransFunctor_additive : (middleNatTransFunctor α).Additive where
  map_add {X Y} f g := by
    apply biprod.hom_ext <;>
      simp [middleNatTransFunctor, natTransArrowFunctor, middleFunctor,
        Preadditive.comp_add, Preadditive.add_comp]

/-- Actual identity-cone and target sequences give genuine middle-object short exactness. -/
theorem middleNatTransFunctor_shortExact (S : ShortComplex D)
    (hF : (S.map F).ShortExact) (hG : (S.map G).ShortExact) :
    (S.map (middleNatTransFunctor α)).ShortExact := by
  have hI := mappingConeNatTransFunctor_shortExact (𝟙 F) S hF hF
  let e : S.map (middleNatTransFunctor α) ≅
      ShortComplex.biprodMap (S.map (mappingConeNatTransFunctor (𝟙 F))) (S.map G) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [middleNatTransFunctor, natTransArrowFunctor, middleFunctor, identityConeFunctor,
        mappingConeNatTransFunctor, ShortComplex.biprodMap])
      (by simp [middleNatTransFunctor, natTransArrowFunctor, middleFunctor, identityConeFunctor,
        mappingConeNatTransFunctor, ShortComplex.biprodMap])
  exact ShortComplex.shortExact_of_iso e.symm (ShortComplex.shortExact_biprodMap hI hG)

end CochainComplex.SplitFactorization
