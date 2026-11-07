/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Abelian.Devissage.CommaLayers
public import Colib.CategoryTheory.QConstruction.Connected
public import Colib.CategoryTheory.ExactCategory.QIsomorphisms
public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic

/-!
# Complete layer invariants of abelian Q-arrows

Extracted from the general Q-arrow portion of
`Quillen/Localization/Serre/LocalizationComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual span classes, subobjects,
isomorphisms and factorization equations are retained. No Serre quotient is used.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.QConstruction
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- An invertible abelian Q-arrow has invertible legs in every span
representative. The proof uses both inverse identities and actual pullbacks. -/
theorem isIso_legs_of_isIso {X Y : C} (s : QConstruction.AbelianSpan X Y)
    [IsIso (QConstruction.mkHom _ _ s)] : IsIso s.l ∧ IsIso s.r := by
  obtain ⟨t, ht⟩ := Quotient.exists_rep (inv (QConstruction.mkHom _ _ s))
  change QConstruction.AbelianSpan Y X at t
  change QConstruction.mkHom _ _ t = inv (QConstruction.mkHom _ _ s) at ht
  have h₁ : QConstruction.mkHom _ _ (Span.comp s t) = QConstruction.mkHom _ _ (Span.id X) := by
    change QConstruction.mkHom _ _ s ≫ QConstruction.mkHom _ _ t = 𝟙 _
    rw [ht]
    exact IsIso.hom_inv_id _
  have h₂ : QConstruction.mkHom _ _ (Span.comp t s) = QConstruction.mkHom _ _ (Span.id Y) := by
    change QConstruction.mkHom _ _ t ≫ QConstruction.mkHom _ _ s = 𝟙 _
    rw [ht]
    exact IsIso.inv_hom_id _
  obtain ⟨e₁, hl₁, _⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ _ _).1 h₁
  obtain ⟨e₂, _, hr₂⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ _ _).1 h₂
  have hl : pullback.fst s.r t.l ≫ s.l = e₁.hom := by simpa [Span.comp] using hl₁.symm
  have hr : pullback.snd t.r s.l ≫ s.r = e₂.hom := by simpa [Span.comp] using hr₂.symm
  have : Mono (pullback.fst s.r t.l) := mono_of_mono_fac hl
  have : IsIso (pullback.fst s.r t.l) := isIso_of_mono_of_epi _
  have : IsIso (pullback.fst s.r t.l ≫ s.l) := by rw [hl]; infer_instance
  have hleft : IsIso s.l := IsIso.of_isIso_comp_left (pullback.fst s.r t.l) s.l
  have : Epi s.r := epi_of_epi_fac hr
  exact ⟨hleft, isIso_of_mono_of_epi _⟩

set_option backward.isDefEq.respectTransparency false in
/-- If a span's two legs are invertible, its Q-class is exactly the ordinary
isomorphism obtained by inverting the left leg and following the right leg. -/
theorem mkHom_eq_qIsoOfIso {X Y : C} (s : QConstruction.AbelianSpan X Y) [IsIso s.l] [IsIso s.r] :
    QConstruction.mkHom _ _ s =
      ((abelianExactStructure C).qIsoOfIso ((asIso s.l).symm ≪≫ asIso s.r)).hom := by
  apply QConstruction.mkHom_eq_of_apexIso _ _ s _ (asIso s.l)
  · simp [QConstruction.isoSpan]
  · simp [QConstruction.isoSpan]

set_option backward.isDefEq.respectTransparency false in
/-- Every invertible abelian Q-arrow comes from an actual ambient isomorphism. -/
theorem exists_iso_of_isIso {X Y : C}
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y)
    [hf : IsIso f] : ∃ e : X ≅ Y, ((abelianExactStructure C).qIsoOfIso e).hom = f := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep f
  change QConstruction.AbelianSpan X Y at s
  change QConstruction.mkHom _ _ s = f at hs
  have : IsIso (QConstruction.mkHom _ _ s) := by rw [hs]; infer_instance
  obtain ⟨hl, hr⟩ := isIso_legs_of_isIso s
  let := hl
  let := hr
  exact ⟨(asIso s.l).symm ≪≫ asIso s.r, (mkHom_eq_qIsoOfIso s).symm.trans hs⟩

/-- Changing the source and apex of a span by compatible isomorphisms
preserves its lower endpoint as an actual subobject of the target. -/
theorem spanLower_eq_of_iso {X Y M : C} (s : QConstruction.AbelianSpan X M) (t :
  QConstruction.AbelianSpan Y M)
    (e : X ≅ Y) (a : s.apex ≅ t.apex)
    (hl : s.l ≫ e.hom = a.hom ≫ t.l) (hr : s.r = a.hom ≫ t.r) :
    Abelian.Devissage.spanLower s = Abelian.Devissage.spanLower t := by
  apply Subobject.mk_eq_mk_of_comm _ _ (kernel.mapIso s.l t.l a e hl)
  simp [Category.assoc, hr]

/-- The upper endpoint has the same invariance under compatible isomorphisms. -/
theorem spanUpper_eq_of_iso {X Y M : C} (s : QConstruction.AbelianSpan X M) (t :
  QConstruction.AbelianSpan Y M)
    (a : s.apex ≅ t.apex) (hr : s.r = a.hom ≫ t.r) :
    Abelian.Devissage.spanUpper s = Abelian.Devissage.spanUpper t :=
  Subobject.mk_eq_mk_of_comm _ _ a hr.symm

set_option backward.isDefEq.respectTransparency false in
/-- The lower subobject of a Q-arrow, independent of its representative. -/
def arrowLower {X M : C}
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    Subobject M := by
  refine Quotient.liftOn f (fun s : QConstruction.AbelianSpan X M => Abelian.Devissage.spanLower
    s) ?_
  intro s t h
  change QConstruction.AbelianSpan X M at s t
  obtain ⟨a, hl, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ s t).1 (Quotient.sound h)
  exact spanLower_eq_of_iso s t (Iso.refl X) a (by simpa using hl.symm) hr.symm

set_option backward.isDefEq.respectTransparency false in
/-- The upper subobject of a Q-arrow, independent of its representative. -/
def arrowUpper {X M : C}
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    Subobject M := by
  refine Quotient.liftOn f (fun s : QConstruction.AbelianSpan X M => Abelian.Devissage.spanUpper
    s) ?_
  intro s t h
  change QConstruction.AbelianSpan X M at s t
  obtain ⟨a, _, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ s t).1 (Quotient.sound h)
  exact spanUpper_eq_of_iso s t a hr.symm

/-- The two endpoints of a Q-arrow form a genuine interval. -/
theorem arrowLower_le_upper {X M : C}
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    arrowLower f ≤ arrowUpper f := by
  induction f using Quotient.inductionOn with | _ s =>
  exact Abelian.Devissage.spanLower_le_upper s

set_option backward.isDefEq.respectTransparency false in
/-- Source isomorphisms do not change the lower endpoint of a Q-arrow. -/
theorem arrowLower_comp_iso {X Y M : C} (e : X ≅ Y)
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      Y ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    arrowLower (((abelianExactStructure C).qIsoOfIso e).hom ≫ f) = arrowLower f := by
  induction f using Quotient.inductionOn with | _ s =>
  change QConstruction.AbelianSpan Y M at s
  let c := QConstruction.isoSpan (abelianExactStructure C).deflation (abelianExactStructure
    C).inflation
    e ((abelianExactStructure C).inflation_of_iso e)
  have : IsIso (pullback.snd e.hom s.l) :=
    (IsPullback.of_hasPullback e.hom s.l).isIso_snd_of_isIso
  apply spanLower_eq_of_iso (Span.comp c s) s e (asIso (pullback.snd e.hom s.l))
  · simpa [Span.comp, c, QConstruction.isoSpan] using pullback.condition (f := e.hom) (g := s.l)
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- The upper endpoint is likewise unchanged by source isomorphisms. -/
theorem arrowUpper_comp_iso {X Y M : C} (e : X ≅ Y)
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      Y ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    arrowUpper (((abelianExactStructure C).qIsoOfIso e).hom ≫ f) = arrowUpper f := by
  induction f using Quotient.inductionOn with | _ s =>
  change QConstruction.AbelianSpan Y M at s
  let c := QConstruction.isoSpan (abelianExactStructure C).deflation (abelianExactStructure
    C).inflation
    e ((abelianExactStructure C).inflation_of_iso e)
  have : IsIso (pullback.snd e.hom s.l) :=
    (IsPullback.of_hasPullback e.hom s.l).isIso_snd_of_isIso
  exact spanUpper_eq_of_iso (Span.comp c s) s (asIso (pullback.snd e.hom s.l)) rfl

/-- The lower-endpoint invariant respects every invertible Q-arrow, since
such an arrow is proved to arise from an ambient isomorphism. -/
theorem arrowLower_comp_of_isIso {X Y M : C}
    (e : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y)
    [IsIso e]
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      Y ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    arrowLower (e ≫ f) = arrowLower f := by
  obtain ⟨a, rfl⟩ := exists_iso_of_isIso e
  exact arrowLower_comp_iso a f

/-- The upper-endpoint invariant respects every invertible Q-arrow. -/
theorem arrowUpper_comp_of_isIso {X Y M : C}
    (e : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y)
    [IsIso e]
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      Y ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    arrowUpper (e ≫ f) = arrowUpper f := by
  obtain ⟨a, rfl⟩ := exists_iso_of_isIso e
  exact arrowUpper_comp_iso a f

/-- A span with arbitrary source, regarded as an object of the unrestricted
Q-inclusion comma category. -/
def allSpanComma {X M : C} (s : QConstruction.AbelianSpan X M) :
    Abelian.Devissage.QComma (⊤ : ObjectProperty C) M :=
  Abelian.Devissage.spanComma (⊤ : ObjectProperty C) M (X := ⟨X, trivial⟩) s

/-- The canonical layer presentation is isomorphic to the original span
in the unrestricted inclusion comma category. -/
def allSpanLayerCommaIso {X M : C} (s : QConstruction.AbelianSpan X M) :
    (Abelian.Devissage.spanLayer (⊤ : ObjectProperty C) s trivial).comma ≅ allSpanComma s :=
  Abelian.Devissage.spanCommaIsoOfIso (⊤ : ObjectProperty C) M
    (X := ⟨(Abelian.Devissage.spanLayer (⊤ : ObjectProperty C) s trivial).quotient, trivial⟩)
    (Y := ⟨X, trivial⟩)
    (Abelian.Devissage.spanLayer (⊤ : ObjectProperty C) s trivial).span s
    (Abelian.Devissage.spanLayerQuotientIso (⊤ : ObjectProperty C) s trivial)
    (Subobject.underlyingIso s.r)
    (Abelian.Devissage.cokernel_π_spanLayerQuotientIso_hom (⊤ : ObjectProperty C) s trivial).symm
    (Subobject.underlyingIso_hom_comp_eq_mk s.r)

set_option backward.isDefEq.respectTransparency false in
/-- Equal layer endpoints identify two Q-arrows up to a source Q-isomorphism.
Thus the endpoint invariant is complete, not just an invariant of chosen spans. -/
theorem exists_qIso_of_endpoints_eq {X Y M : C}
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (g : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      Y ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (hl : arrowLower f = arrowLower g) (hu : arrowUpper f = arrowUpper g) :
    ∃ e : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ≅
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y,
      e.hom ≫ g = f := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  obtain ⟨t, rfl⟩ := Quotient.exists_rep g
  change QConstruction.AbelianSpan X M at s
  change QConstruction.AbelianSpan Y M at t
  have h : Abelian.Devissage.spanLayer (⊤ : ObjectProperty C) s trivial =
      Abelian.Devissage.spanLayer (⊤ : ObjectProperty C) t trivial := by
    apply Abelian.Devissage.Layer.ext
    · exact hl
    · exact hu
  let e : allSpanComma s ≅ allSpanComma t :=
    (allSpanLayerCommaIso s).symm ≪≫
      eqToIso (congrArg (fun A : Abelian.Devissage.Layer (⊤ : ObjectProperty C) M => A.comma) h) ≪≫
      allSpanLayerCommaIso t
  refine ⟨(Abelian.Devissage.mapQ (⊤ : ObjectProperty C)).mapIso
    ((CostructuredArrow.proj (Abelian.Devissage.mapQ (⊤ : ObjectProperty C)) (QConstruction.of _ _
      M)).mapIso e), ?_⟩
  exact CostructuredArrow.w e.hom

set_option backward.isDefEq.respectTransparency false in
/-- Factorization of Q-arrows implies the interval order on their endpoints. -/
theorem endpoints_order_of_fac {X Y M : C}
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (g : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      Y ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (k : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y)
    (w : k ≫ g = f) : arrowLower g ≤ arrowLower f ∧ arrowUpper f ≤ arrowUpper g := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  obtain ⟨t, rfl⟩ := Quotient.exists_rep g
  change QConstruction.AbelianSpan X M at s
  change QConstruction.AbelianSpan Y M at t
  let h : allSpanComma s ⟶ allSpanComma t :=
    CostructuredArrow.homMk ((Abelian.Devissage.mapQ (⊤ : ObjectProperty C)).preimage k) (by
      rw [Functor.map_preimage]
      exact w)
  exact Abelian.Devissage.Layer.le_of_comma_hom
    ((allSpanLayerCommaIso s).hom ≫ h ≫ (allSpanLayerCommaIso t).inv)

set_option backward.isDefEq.respectTransparency false in
/-- Every inequality of endpoint intervals comes from an actual Q-factorization. -/
theorem exists_factor_of_endpoints_order {X Y M : C}
    (f : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (g : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      Y ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
    (hl : arrowLower g ≤ arrowLower f) (hu : arrowUpper f ≤ arrowUpper g) :
    ∃ k : QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation
      X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y,
      k ≫ g = f := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  obtain ⟨t, rfl⟩ := Quotient.exists_rep g
  change QConstruction.AbelianSpan X M at s
  change QConstruction.AbelianSpan Y M at t
  have hle : Abelian.Devissage.spanLayer (⊤ : ObjectProperty C) s trivial ≤
      Abelian.Devissage.spanLayer (⊤ : ObjectProperty C) t trivial := ⟨hl, hu⟩
  let h : allSpanComma s ⟶ allSpanComma t :=
    (allSpanLayerCommaIso s).inv ≫ Abelian.Devissage.Layer.commaMap hle ≫
      (allSpanLayerCommaIso t).hom
  exact ⟨(Abelian.Devissage.mapQ (⊤ : ObjectProperty C)).map h.left, CostructuredArrow.w h⟩

/-- Recovering endpoints from a canonical layer span returns the given layer. -/
theorem spanLayer_span {M : C} (A : Abelian.Devissage.Layer (⊤ : ObjectProperty C) M) :
    Abelian.Devissage.spanLayer (⊤ : ObjectProperty C) A.span trivial = A := by
  apply le_antisymm
  · exact Abelian.Devissage.Layer.le_of_comma_hom (allSpanLayerCommaIso A.span).hom
  · exact Abelian.Devissage.Layer.le_of_comma_hom (allSpanLayerCommaIso A.span).inv

@[simp]
theorem arrowLower_layerSpan {M : C} (A : Abelian.Devissage.Layer (⊤ : ObjectProperty C) M) :
    arrowLower (QConstruction.mkHom _ _ A.span) = A.lower :=
  congrArg Abelian.Devissage.Layer.lower (spanLayer_span A)

@[simp]
theorem arrowUpper_layerSpan {M : C} (A : Abelian.Devissage.Layer (⊤ : ObjectProperty C) M) :
    arrowUpper (QConstruction.mkHom _ _ A.span) = A.upper :=
  congrArg Abelian.Devissage.Layer.upper (spanLayer_span A)

set_option backward.isDefEq.respectTransparency false in
/-- A Q-arrow from zero is precisely a subobject: take the monomorphism
forming the right leg of any span representative. -/
def zeroArrowSubobject {M : C}
    (f : (abelianExactStructure C).qZero ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) :
    Subobject M := by
  refine Quotient.liftOn f (fun s : QConstruction.AbelianSpan (0 : C) M => Subobject.mk s.r) ?_
  intro s t h
  change QConstruction.AbelianSpan (0 : C) M at s t
  let : Mono s.r := (abelianExactStructure C).mono_of_inflation s.wr
  let : Mono t.r := (abelianExactStructure C).mono_of_inflation t.wr
  obtain ⟨e, _, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ s t).1 (Quotient.sound h)
  exact Subobject.mk_eq_mk_of_comm _ _ e hr

/-- Present a subobject by the Q-span whose left leg is the map to zero. -/
def zeroArrowOfSubobject {M : C} (S : Subobject M) :
    (abelianExactStructure C).qZero ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M :=
  QConstruction.mkHom _ _ ⟨S, 0, S.arrow, (abelianExactStructure C).deflation_zero _,
    (abelianExactStructure_inflation_iff C _).2 inferInstance⟩

@[simp]
theorem zeroArrowSubobject_ofSubobject {M : C} (S : Subobject M) :
    zeroArrowSubobject (zeroArrowOfSubobject S) = S := Subobject.mk_arrow S

/-- The subobject completely determines the Q-arrow from zero, including its
apex-isomorphism quotient class. -/
theorem zeroArrowSubobject_injective {M : C} :
    Function.Injective (zeroArrowSubobject (C := C) (M := M)) := by
  intro f g h
  induction f using Quotient.inductionOn with | _ s =>
  induction g using Quotient.inductionOn with | _ t =>
  change Subobject.mk s.r = Subobject.mk t.r at h
  apply QConstruction.mkHom_eq_of_apexIso _ _ s t (Subobject.isoOfMkEqMk s.r t.r h)
  · exact (isZero_zero C).eq_of_tgt _ _
  · simp

/-- Actual subobjects classify all Q-arrows from the zero vertex. -/
def zeroArrowSubobjectEquiv (M : C) :
    ((abelianExactStructure C).qZero ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M) ≃
      Subobject M where
  toFun := zeroArrowSubobject
  invFun := zeroArrowOfSubobject
  left_inv _ := zeroArrowSubobject_injective (zeroArrowSubobject_ofSubobject _)
  right_inv := zeroArrowSubobject_ofSubobject

/-- Precomposing a span by an original zero-object isomorphism leaves its
classified subobject unchanged: the pullback projection is an isomorphism. -/
theorem zeroArrowSubobject_comp_iso {X M : C} (e : (0 : C) ≅ X)
    (s : QConstruction.AbelianSpan X M) :
    zeroArrowSubobject (((abelianExactStructure C).qIsoOfIso e).hom ≫ QConstruction.mkHom _ _ s) =
      Subobject.mk s.r := by
  have : IsIso (pullback.snd e.hom s.l) :=
    (IsPullback.of_hasPullback e.hom s.l).isIso_snd_of_isIso
  change Subobject.mk (pullback.snd e.hom s.l ≫ s.r) = Subobject.mk s.r
  exact Subobject.mk_eq_mk_of_comm _ _ (asIso (pullback.snd e.hom s.l)) rfl

end CategoryTheory.QConstruction
