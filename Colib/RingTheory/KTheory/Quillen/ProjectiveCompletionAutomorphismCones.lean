/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Automorphism.Class
public import Colib.Topology.ClassifyingSpace.ExtensionTotal
public import Colib.CategoryTheory.ExactCategory.ExtensionIdentityFunctor
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionIsomorphism
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionCokernelComparison

/-!
Implementation provenance: `Quillen/KTheory/Plus/ProjectiveCompletionAutomorphismCones.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, tracks,
hypotheses, and signs are retained under native mathematical ownership.

# The actual Q-cones in the extension-category contraction

The identity-to-initial-raise and constant-to-initial-raise arrows of the
subdivision contraction project to the full-apex and zero-apex Q-spans.
Canonical cokernel endpoint isomorphisms identify the whole natural families
with the existing automorphism cones. No localized-completion or capped-sphere
comparison is asserted: these are the categorical arms needed for that proof.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open Topology HomotopyGroup
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject
namespace CategoryTheory.ExactCategory.Automorphism
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The actual initial-raise of an identity extension in the subdivision model. -/
def raisedIdentity (A : C) : E.ExtensionTotal :=
  (Subdivision.initialRaise (E.inflationZeroIsInitial)).obj (E.identityExtension A)

/-- The identity-to-raise arm of the original subdivision contraction. -/
def identityRaiseArrow (A : C) : E.identityExtension A ⟶ raisedIdentity E A :=
  (Subdivision.identityToInitialRaise E.inflationZeroIsInitial).app (E.identityExtension A)

/-- The constant-zero-to-raise arm of the original subdivision contraction. -/
def zeroRaiseArrow (A : C) : E.extensionTotalPoint ⟶ raisedIdentity E A :=
  (Subdivision.constantToInitialRaise E.inflationZeroIsInitial).app (E.identityExtension A)

/-- The full-apex span, retaining the source quotient’s canonical zero isomorphism. -/
def identityRaiseSpan (A : C) :
    Span E.deflation E.inflation (E.extensionProjectionObject (E.identityExtension A))
      (E.extensionProjectionObject (raisedIdentity E A)) where
  apex := E.extensionProjectionObject (raisedIdentity E A)
  l := 0 ≫ (E.identityQuotientIsoZero A).inv
  r := 𝟙 _
  wl := E.deflation_comp _ _ (E.deflation_zero _)
    (E.deflation_of_iso (E.identityQuotientIsoZero A).symm)
  wr := E.inflation_id _

/-- The original identity-to-raise projection is exactly its full-apex Q-span. -/
theorem identityRaise_projection (A : C) :
    E.extensionProjectionQMap (identityRaiseArrow E A) =
      QConstruction.mkHom E.deflation E.inflation (identityRaiseSpan E A) := by
  refine E.extensionProjectionQMap_eq_of_cokernel (identityRaiseArrow E A)
    (identityRaiseSpan E A) (E.extensionQuotientData (raisedIdentity E A)).π ?_ ?_ ?_ ?_
  · have hz : (Subdivision.domainMap (identityRaiseArrow E A)).hom = 0 :=
      (isZero_zero C).eq_of_src _ _
    rw [hz, zero_comp, zero_comp]
  · have hi : (Subdivision.domainMap (identityRaiseArrow E A)).hom ≫
        (E.identityExtension A).fiber.unop.hom.hom =
        (raisedIdentity E A).fiber.unop.hom.hom := by
      change _ ≫ 𝟙 A = _
      exact Category.comp_id _
    exact CokernelCofork.isColimitOfIsColimitOfIff'
      ((E.extensionQuotientData (raisedIdentity E A)).isColimit E) _
      (by intro W a; rw [hi])
  · change (E.extensionQuotientData (raisedIdentity E A)).π ≫
      (0 ≫ (E.identityQuotientIsoZero A).inv) =
      (E.extensionQuotientData (E.identityExtension A)).π
    have h := (E.extensionQuotientData (E.identityExtension A)).zero
    change (𝟙 A) ≫ _ = 0 at h
    simpa only [Category.id_comp, comp_zero, zero_comp] using h.symm
  · simp [identityRaiseSpan, identityRaiseArrow, Subdivision.identityToInitialRaise,
      Subdivision.mkHom]

/-- The zero-apex span, retaining the chosen zero quotient and its original identity leg. -/
def zeroRaiseSpan (A : C) :
    Span E.deflation E.inflation (E.extensionProjectionObject E.extensionTotalPoint)
      (E.extensionProjectionObject (raisedIdentity E A)) where
  apex := E.extensionProjectionObject E.extensionTotalPoint
  l := 𝟙 _
  r := (E.identityQuotientIsoZero (0 : C)).hom ≫ 0
  wl := E.deflation_id _
  wr := E.inflation_comp _ _ (E.inflation_of_iso (E.identityQuotientIsoZero (0 : C)))
    (E.inflation_zero _)

/-- The original zero-to-raise projection is exactly its zero-apex Q-span. -/
theorem zeroRaise_projection (A : C) :
    E.extensionProjectionQMap (zeroRaiseArrow E A) =
      QConstruction.mkHom E.deflation E.inflation (zeroRaiseSpan E A) := by
  refine E.extensionProjectionQMap_eq_of_cokernel (zeroRaiseArrow E A)
    (zeroRaiseSpan E A) (E.extensionQuotientData E.extensionTotalPoint).π ?_ ?_ ?_ ?_
  · have hd : (Subdivision.domainMap (zeroRaiseArrow E A)).hom = 𝟙 (0 : C) := rfl
    rw [hd]
    change (𝟙 (0 : C) ≫ 𝟙 (0 : C)) ≫ _ = _
    rw [Category.id_comp]
    exact (E.extensionQuotientData E.extensionTotalPoint).zero
  · exact CokernelCofork.isColimitOfIsColimitOfIff'
      ((E.extensionQuotientData E.extensionTotalPoint).isColimit E) _
      (by
        intro W a
        change 𝟙 (0 : C) ≫ a = 0 ↔ (𝟙 (0 : C) ≫ 𝟙 (0 : C)) ≫ a = 0
        simp only [Category.id_comp])
  · simp [zeroRaiseSpan]
  · have hz : (zeroRaiseArrow E A).base.hom = 0 := (isZero_zero C).eq_of_src _ _
    simp [zeroRaiseSpan, hz]

/-- The chosen quotient of the raised zero inflation is canonically its middle object. -/
def raisedQuotientIso (A : C) : E.extensionProjectionObject (raisedIdentity E A) ≅ A :=
  ((E.extensionQuotientData (raisedIdentity E A)).isColimit E).coconePointUniqueUpToIso
    (CokernelCofork.IsColimit.ofId _ ((isZero_zero C).eq_of_src _ _))

/-- The canonical quotient comparison sends the actual quotient map to the identity. -/
@[reassoc]
theorem raisedQuotientIso_π (A : C) :
    (E.extensionQuotientData (raisedIdentity E A)).π ≫ (raisedQuotientIso E A).hom = 𝟙 A :=
  ((E.extensionQuotientData (raisedIdentity E A)).isColimit E).comp_coconePointUniqueUpToIso_hom
    _ WalkingParallelPair.one

end CategoryTheory.ExactCategory.Automorphism

namespace CategoryTheory.ExactCategory.Automorphism
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Canonical endpoint comparisons identify the first contraction arm
with the actual full-apex Q-arrow. -/
theorem identityRaise_normalized (A : C) :
    (E.identityProjectionIsoZero A).inv ≫ E.extensionProjectionQMap (identityRaiseArrow E A) ≫
      (E.qIsoOfIso (raisedQuotientIso E A)).hom = E.fromZeroTotal (QConstruction.of _ _ A) := by
  rw [identityRaise_projection]
  have h : (E.identityProjectionIsoZero A).inv ≫
      QConstruction.mkHom E.deflation E.inflation (identityRaiseSpan E A) =
        E.fromZeroTotal
          (QConstruction.of _ _ (E.extensionProjectionObject (raisedIdentity E A))) := by
    let e := E.identityQuotientIsoZero A
    let Y := E.extensionProjectionObject (raisedIdentity E A)
    let sq : IsPullback (0 : Y ⟶ (0 : C)) (𝟙 Y) e.inv (0 ≫ e.inv) :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    let : HasPullback e.inv (0 ≫ e.inv : Y ⟶ _) := sq.hasPullback
    change QConstruction.mkHom _ _
      (Span.comp (QConstruction.isoSpan _ _ e.symm _) (identityRaiseSpan E A)) = _
    symm
    apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
    · change sq.isoPullback.hom ≫ pullback.fst _ _ ≫ 𝟙 _ = 0
      simp
    · change sq.isoPullback.hom ≫ pullback.snd _ _ ≫ 𝟙 _ = 𝟙 Y
      simp
  rw [← Category.assoc, h]
  exact fullFromZero_iso E (raisedQuotientIso E A)

/-- The same endpoint comparisons identify the second contraction arm with fromZero. -/
theorem zeroRaise_normalized (A : C) :
    (E.identityProjectionIsoZero (0 : C)).inv ≫
      E.extensionProjectionQMap (zeroRaiseArrow E A) ≫
      (E.qIsoOfIso (raisedQuotientIso E A)).hom = E.fromZero (QConstruction.of _ _ A) := by
  rw [zeroRaise_projection]
  have h : (E.identityProjectionIsoZero (0 : C)).inv ≫
      QConstruction.mkHom E.deflation E.inflation (zeroRaiseSpan E A) =
        E.fromZero (QConstruction.of _ _ (E.extensionProjectionObject (raisedIdentity E A))) := by
    let e := E.identityQuotientIsoZero (0 : C)
    let sq : IsPullback (𝟙 (0 : C)) e.inv e.inv (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
    let : HasPullback e.inv (𝟙 _) := sq.hasPullback
    change QConstruction.mkHom _ _
      (Span.comp (QConstruction.isoSpan _ _ e.symm _) (zeroRaiseSpan E A)) = _
    symm
    apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
    · change sq.isoPullback.hom ≫ pullback.fst _ _ ≫ 𝟙 _ = 𝟙 (0 : C)
      simp
    · change sq.isoPullback.hom ≫ pullback.snd _ _ ≫ (e.hom ≫ 0) = 0
      simp
  rw [← Category.assoc, h]
  exact fromZero_iso E (raisedQuotientIso E A)


/-- Apply the original initial-raise functor to the entire identity-extension diagram. -/
def raisedIdentityFunctor : Core C ⥤ E.ExtensionTotal :=
  E.identityExtensionFunctor ⋙ Subdivision.initialRaise E.inflationZeroIsInitial

/-- The inverse quotient comparison is the original chosen quotient map. -/
lemma raisedQuotientIso_inv (A : C) :
    (raisedQuotientIso E A).inv = (E.extensionQuotientData (raisedIdentity E A)).π := by
  apply (cancel_mono (raisedQuotientIso E A).hom).1
  rw [Iso.inv_hom_id, raisedQuotientIso_π]

/-- The whole raised quotient diagram is naturally the original core Q-diagram. -/
def raisedProjectionIso : raisedIdentityFunctor E ⋙ E.extensionProjection ≅ coreQ E :=
  NatIso.ofComponents (fun A => E.qIsoOfIso (raisedQuotientIso E A.of)) (by
    intro A B f
    let g := (raisedIdentityFunctor E).map f
    have : Epi (Subdivision.domainMap g).hom := by
      change Epi (𝟙 (0 : C))
      infer_instance
    have hg : E.extensionProjectionQMap g =
        (E.qIsoOfIso (raisedQuotientIso E A.of ≪≫ f.iso ≪≫
          (raisedQuotientIso E B.of).symm)).hom := by
      apply E.extensionProjectionQMap_eq_qIsoOfIso g
      change (E.extensionQuotientData (raisedIdentity E A.of)).π ≫
        ((raisedQuotientIso E A.of).hom ≫ f.iso.hom ≫ (raisedQuotientIso E B.of).inv) =
        f.iso.hom ≫ (E.extensionQuotientData (raisedIdentity E B.of)).π
      erw [raisedQuotientIso_π_assoc, Category.id_comp, raisedQuotientIso_inv]
    change E.extensionProjectionQMap g ≫ (E.qIsoOfIso (raisedQuotientIso E B.of)).hom =
      (E.qIsoOfIso (raisedQuotientIso E A.of)).hom ≫ (E.qIsoOfIso f.iso).hom
    rw [hg]
    simp only [ExactStructure.qIsoOfIso_trans, Iso.trans_hom, Category.assoc]
    change (E.qIsoOfIso (raisedQuotientIso E A.of)).hom ≫
      (E.qIsoOfIso f.iso).hom ≫ (E.qIsoOfIso (raisedQuotientIso E B.of)).inv ≫
        (E.qIsoOfIso (raisedQuotientIso E B.of)).hom = _
    rw [Iso.inv_hom_id, Category.comp_id])

/-- Projection of the identity-to-raise contraction arm, including its endpoint isomorphisms. -/
def normalizedIdentityRaiseCone : (Functor.const (Core C)).obj E.qZero ⟶ coreQ E :=
  E.identityExtensionProjectionIsoZero.inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft E.identityExtensionFunctor
        (Subdivision.identityToInitialRaise E.inflationZeroIsInitial)) E.extensionProjection ≫
      (raisedProjectionIso E).hom

/-- The normalized identity-to-raise family is the original full-apex natural cone. -/
theorem normalizedIdentityRaiseCone_eq : normalizedIdentityRaiseCone E = fullCone E := by
  apply NatTrans.ext
  funext A
  exact identityRaise_normalized E A.of


/-- The constant zero-extension diagram retains its canonical quotient isomorphism. -/
def constantIdentityProjectionIso :
    (E.identityExtensionFunctor ⋙
      (Functor.const E.ExtensionTotal).obj E.extensionTotalPoint) ⋙ E.extensionProjection ≅
      (Functor.const (Core C)).obj E.qZero :=
  NatIso.ofComponents (fun _ => E.identityProjectionIsoZero (0 : C)) (by
    intro A B f
    change E.extensionProjection.map (𝟙 E.extensionTotalPoint) ≫ _ = _ ≫ 𝟙 E.qZero
    erw [E.extensionProjection.map_id, Category.id_comp, Category.comp_id])

/-- Projection of the constant-to-raise arm uses the same actual quotient comparisons. -/
def normalizedZeroRaiseCone : (Functor.const (Core C)).obj E.qZero ⟶ coreQ E :=
  (constantIdentityProjectionIso E).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft E.identityExtensionFunctor
        (Subdivision.constantToInitialRaise E.inflationZeroIsInitial)) E.extensionProjection ≫
      (raisedProjectionIso E).hom

/-- The normalized constant-to-raise family is the original zero-apex natural cone. -/
theorem normalizedZeroRaiseCone_eq : normalizedZeroRaiseCone E = zeroCone E := by
  apply NatTrans.ext
  funext A
  exact zeroRaise_normalized E A.of

end CategoryTheory.ExactCategory.Automorphism
