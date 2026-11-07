/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.CofibrationClosedSubcategory
public import Colib.CategoryTheory.Waldhausen.FunctorialFactorization.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Colib.CategoryTheory.Waldhausen.Approximation.Basic

/-! # The actual weak image and its genuine Waldhausen closure

The target predicate is existence of an actual weak comparison from an
original functor image. A restricted factorization condition applies only
to targets carrying such a witness. It proves actual cofibration-pushout
closure by lifting both legs from one source representative and gluing.
No all-target App2, image closure, derived essential-image identification,
or density/cofinality conclusion is assumed.

Implementation provenance: `Quillen/Waldhausen/Approximation/WeakImage.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ApproximationImage
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (W : Structure C) (V : Structure D) (F : C ⥤ D)

/-- Objects admitting an actual original weak comparison from an image object. -/
def objects : ObjectProperty D := fun Y ↦ ∃ (X : C) (p : F.obj X ⟶ Y), V.weq p

/-- The actual full category on that predicate, retaining every target arrow. -/
abbrev Obj := (objects V F).FullSubcategory

/-- Every original image object has its identity weak comparison. -/
theorem obj_mem (X : C) : objects V F (F.obj X) := ⟨X, 𝟙 _, V.weq.id_mem _⟩

/-- The predicate is forward invariant under original target weak arrows. -/
theorem mem_of_weak {Y Z : D} (f : Y ⟶ Z) (hf : V.weq f)
    (hY : objects V F Y) : objects V F Z := by
  obtain ⟨X, p, hp⟩ := hY
  exact ⟨X, p ≫ f, V.weq.comp_mem _ _ hp hf⟩

instance objects_isClosedUnderIsomorphisms : (objects V F).IsClosedUnderIsomorphisms where
  of_iso e h := mem_of_weak V F e.hom (V.weq_iso _ inferInstance) h

/-- Honest App1 and map factorization restricted to the witnessed actual weak image. -/
structure HasApproximationOnImage : Prop where
  reflects {X Y : C} (f : X ⟶ Y) : V.weq (F.map f) → W.weq f
  lift {X : C} {Y : D} (f : F.obj X ⟶ Y) (hY : objects V F Y) :
    ∃ (X' : C) (i : X ⟶ X') (p : F.obj X' ⟶ Y),
      W.cof i ∧ V.weq p ∧ F.map i ≫ p = f

/-- A geometric arrow factorization into the witnessed image need not already
be a cofibration: the genuine source cylinder supplies the cofibration leg. -/
theorem HasApproximationOnImage.of_factorization (T : FunctorialFactorization W)
    (hweak : ∀ {X Y : C} (f : X ⟶ Y), W.weq f → V.weq (F.map f))
    (hreflect : ∀ {X Y : C} (f : X ⟶ Y), V.weq (F.map f) → W.weq f)
    (hlift : ∀ {X : C} {Y : D} (f : F.obj X ⟶ Y), objects V F Y →
      ∃ (X' : C) (a : X ⟶ X') (p : F.obj X' ⟶ Y), V.weq p ∧ F.map a ≫ p = f) :
    HasApproximationOnImage W V F where
  reflects := hreflect
  lift f hY := by
    obtain ⟨X', a, p, hp, fac⟩ := hlift f hY
    let t := Arrow.mk a
    refine ⟨T.middle.obj t, T.inclusion.app t, F.map (T.projection.app t) ≫ p,
      T.cofibration t, V.weq.comp_mem _ _ (hweak _ (T.weak t)) hp, ?_⟩
    rw [← Category.assoc, ← F.map_comp, T.factorization]
    exact fac

variable {W V F} (h : HasApproximationOnImage W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

include hF in
/-- The original chosen target zero is in the actual weak image. -/
theorem zero_mem : objects V F V.zero :=
  ⟨W.zero, (hF.zero W.isZero).to_ V.zero,
    V.weq_iso _ ((hF.zero W.isZero).isIso V.isZero _)⟩

include h hF in
/-- Restricted App2 proves actual target pushout closure. A common source
representative is kept at the overlap, so all comparison squares commute strictly. -/
theorem pushout_mem {A B E Q : D} {i : A ⟶ B} {f : A ⟶ E} {g : B ⟶ Q} {j : E ⟶ Q}
    (hi : V.cof i) (hQ : IsPushout i f g j)
    (hA : objects V F A) (hB : objects V F B) (hE : objects V F E) : objects V F Q := by
  obtain ⟨X, p, hp⟩ := hA
  obtain ⟨XB, a, pB, ha, hpB, fa⟩ := h.lift (p ≫ i) hB
  obtain ⟨XE, b, pE, hb, hpE, fb⟩ := h.lift (p ≫ f) hE
  obtain ⟨T, c, d, hT⟩ := W.pushout_exists a b ha
  let hFT := hF.pushout ha hT
  have comm : F.map a ≫ (pB ≫ g) = F.map b ≫ (pE ≫ j) := by
    calc
      F.map a ≫ (pB ≫ g) = p ≫ (i ≫ g) := by rw [← Category.assoc, fa, Category.assoc]
      _ = p ≫ (f ≫ j) := congrArg (fun k ↦ p ≫ k) hQ.w
      _ = F.map b ≫ (pE ≫ j) := by
        simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ j) fb.symm
  let q : F.obj T ⟶ Q := hFT.desc (pB ≫ g) (pE ≫ j) comm
  have hq : V.weq q := V.gluing p pB pE q (hF.cofibration a ha) hi hFT hQ
    fa fb (hFT.inl_desc _ _ comm) (hFT.inr_desc _ _ comm) hp hpB hpE
  exact ⟨T, q, hq⟩

include h hF in
/-- Both required inherited-structure closures are proved, not supplied as image assumptions. -/
theorem closed : CofibrationClosedSubcategory.Closed V (objects V F) where
  zero_mem := zero_mem hF
  pushout_mem := pushout_mem h hF

/-- The actual weak-image category has its genuine inherited Waldhausen structure. -/
def waldhausenStructure : Structure (Obj V F) :=
  CofibrationClosedSubcategory.waldhausenStructure V (objects V F) (closed h hF)

/-- The literal target inclusion is exact for that actual structure. -/
theorem inclusion_exact : IsExact (waldhausenStructure h hF).cof (waldhausenStructure h hF).weq
    V.cof V.weq (objects V F).ι :=
  CofibrationClosedSubcategory.inclusion_exact V (objects V F) (closed h hF)

/-- Original target saturation passes to every original weak-image arrow. -/
instance twoOutOfThree [V.weq.HasTwoOutOfThreeProperty] :
    (waldhausenStructure h hF).weq.HasTwoOutOfThreeProperty :=
  CofibrationClosedSubcategory.twoOutOfThree V (objects V F) (closed h hF)

/-- Corestrict the original functor without changing any object or morphism. -/
def corestrict (V : Structure D) (F : C ⥤ D) : C ⥤ Obj V F := (objects V F).lift F (obj_mem V F)

/-- Forgetting weak-image membership recovers the entire original functor exactly. -/
@[simp] theorem corestrict_comp_inclusion : corestrict V F ⋙ (objects V F).ι = F := rfl

/-- Actual original exactness lifts to the witnessed weak-image category. -/
theorem corestrict_exact : IsExact W.cof W.weq
    (waldhausenStructure h hF).cof (waldhausenStructure h hF).weq (corestrict V F) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (objects V F).ι _ (hF.zero hz)
  cofibration f hf := hF.cofibration f hf
  weak f hf := hF.weak f hf
  pushout hi hp := IsPushout.of_map_of_faithful (objects V F).ι (hF.pushout hi hp)

/-- Restricted App2 becomes genuine App2 on this actually constructed target category. -/
theorem corestrict_approximation : HasApproximationProperty W (waldhausenStructure h hF)
    (corestrict V F) where
  reflects f hf := h.reflects f hf
  lift {X} {Y} f := by
    obtain ⟨X', i, p, hi, hp, he⟩ := h.lift f.hom Y.property
    exact ⟨X', i, (objects V F).homMk p, hi, hp,
      ObjectProperty.hom_ext _ he⟩

end CategoryTheory.Waldhausen.ApproximationImage
