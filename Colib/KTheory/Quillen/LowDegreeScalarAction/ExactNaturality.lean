/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Quillen.LowDegreeScalarAction.IdentityAutomorphism
public import Colib.Topology.ClassifyingSpace.Naturality
public import Colib.KTheory.Quillen.Map.CommonAmbient

/-!
# Exact-functor naturality of identity-automorphism operations

An ordinary componentwise compatibility equation for identity natural
automorphisms gives a strict square for their whole original normalized-Q
self-homotopies. The raw Q-square follows from preservation of Q-isomorphisms.
Naturality of the target identity automorphism then conjugates this square
through the actual zero rebase isomorphism. The original normalized identity
self-homotopy agrees pointwise with this identity-Q homotopy, because natural
automorphisms of the identity commute with the rebase comparison.

Realized whiskering yields the whole square, while the original fixed-zero
homotopies and normalized Q-map retain their given basedness. Consequently the
original K-maps preserve the operations in degree (1,1), with their
unchanged representative orientation. The displayed universe condition covers
the native finite-module and finite-projective categories and their chosen
upper SmallModels. The common-ambient extension also permits different hom
universes while retaining the actual normalized Q-map and identity tracks.
Product and localization-boundary compatibility are separate statements.
-/
/-! Implementation source: `Quillen/KTheory/LowDegreeScalarAction/ExactNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original normalized-Q maps,
whole identity tracks, upper SmallK and tensor-extension formulas are retained.
Unused degree-zero and optional matrix-cube calibrations are not imported. -/
@[expose] public section

noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject
universe u v w u' v'
namespace CategoryTheory.ExactCategory.IdentityAutomorphism

private def castSelfIso {A : Type w} [Category.{v'} A]
    {F : A ⥤ A} (h : F = 𝟭 A) (α : F ≅ F) : 𝟭 A ≅ 𝟭 A :=
  (eqToIso h.symm) ≪≫ α ≪≫ eqToIso h

private theorem castSelfIso_homotopy {A : Type w} [Category.{v'} A]
    {F : A ⥤ A} (h : F = 𝟭 A) (α : F ≅ F)
    (t : unitInterval) (z : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy (castSelfIso h α).hom (t, z) =
      classifyingSpaceNaturalTransformationHomotopy α.hom (t, z) := by
  subst F
  simp [castSelfIso]

private theorem castSelfIso_conjugate {A : Type w} [Category.{v'} A]
    {F G : A ⥤ A} (hF : F = 𝟭 A) (hG : G = 𝟭 A)
    (e : F ≅ G) (α : F ≅ F) :
    castSelfIso hG (e.symm ≪≫ α ≪≫ e) = castSelfIso hF α := by
  subst F
  subst G
  simp only [castSelfIso, eqToIso_refl, Iso.refl_trans, Iso.trans_refl]
  apply Iso.ext
  apply NatTrans.ext
  funext A
  change e.inv.app A ≫ α.hom.app A ≫ e.hom.app A = α.hom.app A
  have hn := α.hom.naturality (e.hom.app A)
  change e.hom.app A ≫ α.hom.app A = α.hom.app A ≫ e.hom.app A at hn
  rw [← hn, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

section QCompatibility
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The actual identity automorphism of the original Q-category. -/
def identityQAut (E : ExactStructure C) (u : 𝟭 C ≅ 𝟭 C) :
    𝟭 E.QCategory ≅ 𝟭 E.QCategory :=
  NatIso.ofComponents (fun A => E.qIsoOfIso (u.app A.obj.of)) (by
    rintro ⟨⟨A⟩⟩ ⟨⟨B⟩⟩ f
    have h := (ExactFunctor.mapQIso (F := ExactFunctor.id E)
      (G := ExactFunctor.id E) u).hom.naturality f
    change (ExactFunctor.id E).mapQ.map f ≫ (E.qIsoOfIso (u.app B)).hom =
      (E.qIsoOfIso (u.app A)).hom ≫ (ExactFunctor.id E).mapQ.map f at h
    have hf : (ExactFunctor.id E).mapQ.map f = f := by
      cases f using Quotient.inductionOn
      rfl
    rw [hf] at h
    exact h)

private theorem cast_mapQIso (E : ExactStructure C) (u : 𝟭 C ≅ 𝟭 C) :
    castSelfIso (ExactFunctor.mapQ_id E)
      (ExactFunctor.mapQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u) =
        identityQAut E u := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  simp [castSelfIso, identityQAut, ExactFunctor.mapQIso]

private theorem cast_normalizedQIso (E : ExactStructure C) (u : 𝟭 C ≅ 𝟭 C) :
    castSelfIso (IdentityAutomorphism.normalizedIdentityQ E)
      (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E) u) =
        identityQAut E u := by
  unfold ExactFunctor.normalizedQIso rebaseFunctorNatIso
  exact (castSelfIso_conjugate (ExactFunctor.mapQ_id E)
    (IdentityAutomorphism.normalizedIdentityQ E) _ _).trans (cast_mapQIso E u)

/-- The identity-Q automorphism realizes the original normalized identity track. -/
theorem identityQAut_homotopy (E : ExactStructure C) (u : 𝟭 C ≅ 𝟭 C)
    (t : unitInterval) (z : E.KSpace) :
    classifyingSpaceNaturalTransformationHomotopy (identityQAut E u).hom (t, z) =
      IdentityAutomorphism.homotopy E u (t, z) := by
  rw [← cast_normalizedQIso E u, castSelfIso_homotopy]
  rfl

private theorem mapQ_identityQAut (F : ExactFunctor EC ED)
    (u : 𝟭 C ≅ 𝟭 C) (v : 𝟭 D ≅ 𝟭 D)
    (h : ∀ A, F.toFunctor.map (u.hom.app A) = v.hom.app (F.toFunctor.obj A))
    (A : EC.QCategory) :
    F.mapQ.map ((identityQAut EC u).hom.app A) =
      (identityQAut ED v).hom.app (F.mapQ.obj A) := by
  have hi : F.toFunctor.mapIso (u.app A.obj.of) = v.app (F.toFunctor.obj A.obj.of) := by
    apply Iso.ext
    exact h A.obj.of
  change F.mapQ.map (EC.qIsoOfIso (u.app A.obj.of)).hom =
    (ED.qIsoOfIso (v.app (F.toFunctor.obj A.obj.of))).hom
  exact (congrArg Iso.hom (F.mapQ_qIsoOfIso (u.app A.obj.of))).trans
    (congrArg (fun e => (ED.qIsoOfIso e).hom) hi)

private theorem normalizedQ_identityQAut (F : ExactFunctor EC ED)
    (u : 𝟭 C ≅ 𝟭 C) (v : 𝟭 D ≅ 𝟭 D)
    (h : ∀ A, F.toFunctor.map (u.hom.app A) = v.hom.app (F.toFunctor.obj A))
    (A : EC.QCategory) :
    (rebaseFunctor F.mapQ EC.qZero ED.qZero
      (ED.qIsoOfIso F.toFunctor.mapZeroObject)).map ((identityQAut EC u).hom.app A) =
      (identityQAut ED v).hom.app ((rebaseFunctor F.mapQ EC.qZero ED.qZero
      (ED.qIsoOfIso F.toFunctor.mapZeroObject)).obj A) := by
  let e := rebaseFunctorIso F.mapQ EC.qZero ED.qZero
    (ED.qIsoOfIso F.toFunctor.mapZeroObject)
  change e.inv.app A ≫ F.mapQ.map ((identityQAut EC u).hom.app A) ≫ e.hom.app A = _
  rw [mapQ_identityQAut F u v h]
  have hn := (identityQAut ED v).hom.naturality (e.hom.app A)
  change e.hom.app A ≫ (identityQAut ED v).hom.app ((rebaseFunctor F.mapQ EC.qZero ED.qZero
      (ED.qIsoOfIso F.toFunctor.mapZeroObject)).obj A) =
    (identityQAut ED v).hom.app (F.mapQ.obj A) ≫ e.hom.app A at hn
  rw [← hn, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end QCompatibility

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- Ordinary componentwise compatibility gives a strict square for the whole
original normalized-Q identity self-homotopies, at every time and point. -/
theorem identityHomotopy_natural (F : ExactFunctor EC ED)
    (u : 𝟭 C ≅ 𝟭 C) (v : 𝟭 D ≅ 𝟭 D)
    (h : ∀ A, F.toFunctor.map (u.hom.app A) = v.hom.app (F.toFunctor.obj A))
    (t : unitInterval) (z : EC.KSpace) :
    classifyingSpaceMap F.normalizedQ (IdentityAutomorphism.homotopy EC u (t, z)) =
      IdentityAutomorphism.homotopy ED v (t, classifyingSpaceMap F.normalizedQ z) := by
  have hw : Functor.whiskerRight (identityQAut EC u).hom F.normalizedQ =
      Functor.whiskerLeft F.normalizedQ (identityQAut ED v).hom := by
    apply NatTrans.ext
    funext A
    exact normalizedQ_identityQAut F u v h A
  rw [← identityQAut_homotopy EC u, ← identityQAut_homotopy ED v,
    ← classifyingSpaceNaturalTransformationHomotopy_whiskerRight, hw,
    classifyingSpaceNaturalTransformationHomotopy_whiskerLeft]

/-- The original K-map commutes with the operation of compatible actual
identity natural automorphisms, with no change to the original track cubes. -/
theorem operation_natural (F : ExactFunctor EC ED)
    (u : 𝟭 C ≅ 𝟭 C) (v : 𝟭 D ≅ 𝟭 D)
    (h : ∀ A, F.toFunctor.map (u.hom.app A) = v.hom.app (F.toFunctor.obj A))
    (m : ℕ) (a : EC.K m) :
    F.KMap (m + 1)
      (IdentityTrack.operation (IdentityAutomorphism.homotopy EC u).toHomotopy
        (IdentityAutomorphism.homotopy_fixed EC u) m a) =
      IdentityTrack.operation (IdentityAutomorphism.homotopy ED v).toHomotopy
        (IdentityAutomorphism.homotopy_fixed ED v) m (F.KMap m a) :=
  IdentityTrack.operation_natural (IdentityAutomorphism.homotopy EC u).toHomotopy
    (IdentityAutomorphism.homotopy_fixed EC u)
    (IdentityAutomorphism.homotopy ED v).toHomotopy
    (IdentityAutomorphism.homotopy_fixed ED v)
    (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point
    (identityHomotopy_natural F u v h) m a

/-- Degree-(1,1) exact-functor naturality of the actual identity-automorphism
operation on the original K-groups. -/
theorem kOneAction_natural (F : ExactFunctor EC ED)
    (u : 𝟭 C ≅ 𝟭 C) (v : 𝟭 D ≅ 𝟭 D)
    (h : ∀ A, F.toFunctor.map (u.hom.app A) = v.hom.app (F.toFunctor.obj A))
    (a : EC.K 1) :
    F.KMap 2 (IdentityAutomorphism.kOneAction EC u a) =
      IdentityAutomorphism.kOneAction ED v (F.KMap 1 a) :=
  operation_natural F u v h 1 a

section CommonAmbient
variable {A B : Type (max u v)} [Category.{u} A] [Category.{v} B]
  [Preadditive A] [HasFiniteBiproducts A]
  [Preadditive B] [HasFiniteBiproducts B]
  {EA : ExactStructure A} {EB : ExactStructure B}

/-- In a common realization universe, the actual normalized Q-map intertwines
compatible identity automorphisms as whole self-homotopies. -/
theorem identityHomotopy_commonAmbient_natural (F : ExactFunctor EA EB)
    (a : 𝟭 A ≅ 𝟭 A) (b : 𝟭 B ≅ 𝟭 B)
    (h : ∀ P, F.toFunctor.map (a.hom.app P) = b.hom.app (F.toFunctor.obj P))
    (t : unitInterval) (z : EA.KSpace) :
    classifyingSpaceMap F.commonAmbientNormalizedQ
      (IdentityAutomorphism.homotopy EA a (t, z)) =
      IdentityAutomorphism.homotopy EB b
        (t, classifyingSpaceMap F.commonAmbientNormalizedQ z) := by
  have hw : Functor.whiskerRight (identityQAut EA a).hom F.commonAmbientNormalizedQ =
      Functor.whiskerLeft F.commonAmbientNormalizedQ (identityQAut EB b).hom := by
    apply NatTrans.ext
    funext P
    exact normalizedQ_identityQAut F a b h P
  rw [← identityQAut_homotopy EA a, ← identityQAut_homotopy EB b,
    ← classifyingSpaceNaturalTransformationHomotopy_whiskerRight, hw,
    classifyingSpaceNaturalTransformationHomotopy_whiskerLeft]

/-- The original common-ambient K-map preserves the literal degree-(1,1)
identity-track operation, even when the two original hom universes differ. -/
theorem kOneAction_commonAmbient_natural (F : ExactFunctor EA EB)
    (a : 𝟭 A ≅ 𝟭 A) (b : 𝟭 B ≅ 𝟭 B)
    (h : ∀ P, F.toFunctor.map (a.hom.app P) = b.hom.app (F.toFunctor.obj P))
    (x : EA.K 1) :
    F.commonAmbientKMap 2 (IdentityAutomorphism.kOneAction EA a x) =
      IdentityAutomorphism.kOneAction EB b (F.commonAmbientKMap 1 x) :=
  IdentityTrack.operation_natural (IdentityAutomorphism.homotopy EA a).toHomotopy
    (IdentityAutomorphism.homotopy_fixed EA a)
    (IdentityAutomorphism.homotopy EB b).toHomotopy
    (IdentityAutomorphism.homotopy_fixed EB b)
    (classifyingSpaceMap F.commonAmbientNormalizedQ).hom F.commonAmbientNormalizedQ_map_point
    (identityHomotopy_commonAmbient_natural F a b h) 1 x

end CommonAmbient

end CategoryTheory.ExactCategory.IdentityAutomorphism
