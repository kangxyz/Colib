/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.MappingCone.Identity
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.JointEndpoints
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Actual additive comparison of the common complex cylinder

The original mapping-cone comparison is natural for actual commuting squares.
Together with the original additive biproduct comparison, it identifies the
identity-cone cylinder under every additive functor, retaining both endpoint
maps, the projection, the joint endpoint arrow and full arrow naturality.
No exactness or quasi-isomorphism preservation is required.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.AdditiveMap`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace CochainComplex.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]

/-- The original mapping-cone comparison is natural for genuine commuting squares. -/
lemma coneMapIso_naturality {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) :
    (F.mapHomologicalComplex (.up ℤ)).map (mappingCone.map f g a b h) ≫
        (mappingCone.mapHomologicalComplexIso g F).hom =
      (mappingCone.mapHomologicalComplexIso f F).hom ≫
        mappingCone.map ((F.mapHomologicalComplex (.up ℤ)).map f)
          ((F.mapHomologicalComplex (.up ℤ)).map g)
          ((F.mapHomologicalComplex (.up ℤ)).map a)
          ((F.mapHomologicalComplex (.up ℤ)).map b)
          (by simpa only [← CategoryTheory.Functor.map_comp] using
            congrArg (F.mapHomologicalComplex (.up ℤ)).map h) := by
  ext n
  dsimp [mappingCone.mapHomologicalComplexIso]
  rw [mappingCone.ext_to_iff _ n (n + 1) rfl]
  constructor <;>
    simp [mappingCone.mapHomologicalComplexXIso, mappingCone.mapHomologicalComplexXIso',
      mappingCone.map, Preadditive.comp_add, Preadditive.add_comp,
      -CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp_assoc]
  all_goals
    congr 1
    simp [mappingCone.ext_from_iff _ (n + 1) n rfl]

/-- Equality of the original chain map gives its literal mapping-cone comparison. -/
def coneIsoOfEq {K L : CochainComplex D ℤ} {f g : K ⟶ L} (h : f = g) :
    mappingCone f ≅ mappingCone g := eqToIso (congrArg (fun f : K ⟶ L => mappingCone f) h)

@[reassoc (attr := simp)]
lemma coneIsoOfEq_inr {K L : CochainComplex D ℤ} {f g : K ⟶ L} (h : f = g) :
    mappingCone.inr f ≫ (coneIsoOfEq h).hom = mappingCone.inr g := by
  subst h
  simp [coneIsoOfEq]

/-- Literal cone equality comparisons retain actual square maps. -/
lemma coneIsoOfEq_naturality {K L K' L' : CochainComplex D ℤ}
    {f g : K ⟶ L} {f' g' : K' ⟶ L'} (h : f = g) (h' : f' = g')
    (a : K ⟶ K') (b : L ⟶ L') (hf : f ≫ b = a ≫ f') (hg : g ≫ b = a ≫ g') :
    mappingCone.map f f' a b hf ≫ (coneIsoOfEq h').hom =
      (coneIsoOfEq h).hom ≫ mappingCone.map g g' a b hg := by
  subst h
  subst h'
  simp [coneIsoOfEq]

/-- The actual identity cone commutes with every additive functor. -/
def identityConeMapIso (K : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.identityConeFunctor.obj K) ≅
      CochainComplex.identityConeFunctor.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
  mappingCone.mapHomologicalComplexIso (𝟙 K) F ≪≫
    coneIsoOfEq ((F.mapHomologicalComplex (.up ℤ)).map_id K)

@[reassoc (attr := simp)]
lemma identityConeMapIso_inr (K : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (mappingCone.inr (𝟙 K)) ≫
      (identityConeMapIso F K).hom =
    mappingCone.inr (𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj K)) := by
  rw [identityConeMapIso, Iso.trans_hom, ← Category.assoc, mappingCone.map_inr, coneIsoOfEq_inr]

/-- Naturality of the actual identity-cone comparison. -/
lemma identityConeMapIso_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.identityConeFunctor.map f) ≫
        (identityConeMapIso F L).hom =
      (identityConeMapIso F K).hom ≫
        CochainComplex.identityConeFunctor.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  change (F.mapHomologicalComplex (.up ℤ)).map (mappingCone.map (𝟙 K) (𝟙 L) f f (by simp)) ≫ _ = _
  rw [identityConeMapIso, identityConeMapIso, Iso.trans_hom, Iso.trans_hom,
    ← Category.assoc, coneMapIso_naturality, Category.assoc,
    coneIsoOfEq_naturality ((F.mapHomologicalComplex (.up ℤ)).map_id K)
      ((F.mapHomologicalComplex (.up ℤ)).map_id L) _ _ _ (by simp)]
  rw [Category.assoc]
  rfl

/-- The cylinder middle comparison uses the actual biproduct and cone comparisons. -/
def middleMapIso {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).obj (middle f) ≅
      middle ((F.mapHomologicalComplex (.up ℤ)).map f) :=
  (F.mapHomologicalComplex (.up ℤ)).mapBiprod _ _ ≪≫
    biprod.mapIso (identityConeMapIso F K) (Iso.refl _)

@[reassoc (attr := simp)]
lemma middleMapIso_projection {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (middleMapIso F f).hom ≫ projection ((F.mapHomologicalComplex (.up ℤ)).map f) =
      (F.mapHomologicalComplex (.up ℤ)).map (projection f) := by
  simp [middleMapIso, projection]

@[reassoc (attr := simp)]
lemma middleMapIso_section {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map (biprod.inr : L ⟶ middle f) ≫
      (middleMapIso F f).hom = biprod.inr := by
  apply biprod.hom_ext <;>
    simp [middleMapIso, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp_assoc]

@[reassoc (attr := simp)]
lemma middleMapIso_inclusion {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map (inclusion f) ≫ (middleMapIso F f).hom =
      inclusion ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  apply biprod.hom_ext <;>
    simp [middleMapIso, inclusion, ← CategoryTheory.Functor.map_comp, ←
      CategoryTheory.Functor.map_comp_assoc]

/-- The middle comparison is natural on the actual arrow category. -/
lemma middleMapIso_naturality {f g : Arrow (CochainComplex C ℤ)} (α : f ⟶ g) :
    (F.mapHomologicalComplex (.up ℤ)).map (middleFunctor.map α) ≫ (middleMapIso F g.hom).hom =
      (middleMapIso F f.hom).hom ≫ middleFunctor.map ((F.mapHomologicalComplex (.up
        ℤ)).mapArrow.map α) := by
  apply biprod.hom_ext
  · simp only [middleMapIso, middleFunctor, Iso.trans_hom, biprod.uniqueUpToIso_hom,
      Functor.mapBinaryBicone_pt, Functor.mapBinaryBicone_fst, BinaryBiproduct.bicone_fst,
      Functor.mapBinaryBicone_snd, BinaryBiproduct.bicone_snd, biprod.mapIso_hom,
      Iso.refl_hom, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
      ← CategoryTheory.Functor.map_comp_assoc, Functor.mapArrow_obj, Arrow.mk_left,
      Arrow.mk_right, Arrow.mk_hom, Functor.mapArrow_map, Arrow.homMk_left,
      Arrow.homMk_right, biprod.map_fst_assoc]
    rw [CategoryTheory.Functor.map_comp, Category.assoc, identityConeMapIso_naturality,
      ← Category.assoc]
  · simp [middleMapIso, middleFunctor, ← CategoryTheory.Functor.map_comp]

/-- The two-endpoint arrow retains the actual additive biproduct comparison. -/
lemma middleMapIso_jointInclusion {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map (jointInclusion f) ≫ (middleMapIso F f).hom =
      ((F.mapHomologicalComplex (.up ℤ)).mapBiprod K L).hom ≫
        jointInclusion ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).mapBiprod K L).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply biprod.hom_ext' <;>
    simp [jointInclusion, ← Category.assoc, ← CategoryTheory.Functor.map_comp]

end CochainComplex.SplitFactorization
