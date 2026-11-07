/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Recognizing filtered colimits of nerves by finite categorical lifting -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.FilteredNerveColimit
variable {J : Type u} [SmallCategory J]
  (F : J ⥤ Cat.{u, u}) (c : Cocone F)

/-- The functor from a diagram stage to the vertex of the categorical cocone. -/
abbrev leg (j : J) : F.obj j ⥤ c.pt := (c.ι.app j).toFunctor
/-- The transition functor between two stages of the filtered categorical diagram. -/
abbrev step {j k : J} (f : j ⟶ k) : F.obj j ⥤ F.obj k := (F.map f).toFunctor

lemma leg_step {j k : J} (f : j ⟶ k) : step F f ⋙ leg F c k = leg F c j :=
  congrArg Cat.Hom.toFunctor (c.w f)

lemma leg_step_obj {j k : J} (f : j ⟶ k) (x : F.obj j) :
    (leg F c k).obj ((step F f).obj x) = (leg F c j).obj x :=
  Functor.congr_obj (leg_step F c f) x

lemma leg_step_map {j k : J} (f : j ⟶ k) {x y : F.obj j} (g : x ⟶ y) :
    (leg F c k).map ((step F f).map g) =
      eqToHom (leg_step_obj F c f x) ≫ (leg F c j).map g ≫
        eqToHom (leg_step_obj F c f y).symm :=
  Functor.congr_hom (leg_step F c f) g

lemma step_comp_obj {j k l : J} (f : j ⟶ k) (g : k ⟶ l) (x : F.obj j) :
    (step F (f ≫ g)).obj x = (step F g).obj ((step F f).obj x) :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (F.map_comp f g)) x

/-- Every arrow of the target lifts together with both endpoints at one stage. -/
def ArrowSurjective : Prop := ∀ {X Y : c.pt} (f : X ⟶ Y),
  ∃ (j : J) (x y : F.obj j) (g : x ⟶ y)
    (hx : (leg F c j).obj x = X) (hy : (leg F c j).obj y = Y),
    (leg F c j).map g ≫ eqToHom hy = eqToHom hx ≫ f

/-- Equal images of two objects at one stage become literally equal later. -/
def EventuallyEqualObjects : Prop := ∀ (j : J) (x y : F.obj j),
  (leg F c j).obj x = (leg F c j).obj y →
    ∃ (k : J) (f : j ⟶ k), (step F f).obj x = (step F f).obj y

variable [IsFiltered J]

/-- Joint lifting and eventual object equality let us lift an arrow into an
already specified stage object while retaining that target after transition. -/
theorem lift_arrow_to_stage (ha : ArrowSurjective F c) (he : EventuallyEqualObjects F c)
    (j : J) (y : F.obj j) {X : c.pt} (f : X ⟶ (leg F c j).obj y) :
    ∃ (k : J) (u : j ⟶ k) (x : F.obj k) (g : x ⟶ (step F u).obj y)
      (hx : (leg F c k).obj x = X),
      (leg F c k).map g ≫ eqToHom (leg_step_obj F c u y) = eqToHom hx ≫ f := by
  obtain ⟨k, a, b, g, ha', hb, hg⟩ := ha f
  let l := IsFiltered.max j k
  let u : j ⟶ l := IsFiltered.leftToMax j k
  let v : k ⟶ l := IsFiltered.rightToMax j k
  have hb' : (leg F c l).obj ((step F v).obj b) =
      (leg F c l).obj ((step F u).obj y) :=
    (leg_step_obj F c v b).trans (hb.trans (leg_step_obj F c u y).symm)
  obtain ⟨m, w, hw⟩ := he l ((step F v).obj b) ((step F u).obj y) hb'
  have hbm : (step F (v ≫ w)).obj b = (step F (u ≫ w)).obj y :=
    (step_comp_obj F v w b).trans (hw.trans (step_comp_obj F u w y).symm)
  let gm := (step F (v ≫ w)).map g ≫ eqToHom hbm
  refine ⟨m, u ≫ w, (step F (v ≫ w)).obj a, gm,
    (leg_step_obj F c (v ≫ w) a).trans ha', ?_⟩
  dsimp only [gm]
  rw [Functor.map_comp, leg_step_map, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans]
  have hh := congrArg (eqToHom (leg_step_obj F c (v ≫ w) a) ≫ ·) hg
  simpa only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc] using hh

/-- Every finite chain in the target lifts into one stage of the diagram. -/
theorem chain_surjective
    (ho : ∀ X : c.pt, ∃ (j : J) (x : F.obj j), (leg F c j).obj x = X)
    (ha : ArrowSurjective F c) (he : EventuallyEqualObjects F c)
    (n : ℕ) (s : ComposableArrows c.pt n) :
    ∃ (j : J) (t : ComposableArrows (F.obj j) n), t ⋙ leg F c j = s := by
  induction n with
  | zero =>
    obtain ⟨j, x, hx⟩ := ho (s.obj 0)
    exact ⟨j, ComposableArrows.mk₀ x, ComposableArrows.ext₀ hx⟩
  | succ n ih =>
    obtain ⟨s, X, f, rfl⟩ := ComposableArrows.precomp_surjective s
    obtain ⟨j, t, rfl⟩ := ih s
    obtain ⟨k, u, a, g, ha', hg⟩ := lift_arrow_to_stage F c ha he j t.left f
    refine ⟨k, ComposableArrows.precomp (t ⋙ step F u) g, ?_⟩
    have ht : ComposableArrows.δ₀ ((ComposableArrows.precomp (t ⋙ step F u) g) ⋙ leg F c k) =
        (ComposableArrows.precomp (t ⋙ leg F c j) f).δ₀ := by
      change t ⋙ (step F u ⋙ leg F c k) = t ⋙ leg F c j
      rw [leg_step]
    apply ComposableArrows.ext_succ ha' ht
    change (leg F c k).map g = eqToHom ha' ≫ f ≫ eqToHom _
    apply (cancel_mono (eqToHom (leg_step_obj F c u t.left))).1
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hg

/-- Equality of finite chains is witnessed after one common transition:
only their finitely many vertices require refinement, since every leg is faithful. -/
theorem chain_eventually_equal (he : EventuallyEqualObjects F c)
    [∀ j, (leg F c j).Faithful] (j : J) (n : ℕ)
    (s t : ComposableArrows (F.obj j) n) (h : s ⋙ leg F c j = t ⋙ leg F c j) :
    ∃ (k : J) (u : j ⟶ k), s ⋙ step F u = t ⋙ step F u := by
  choose k f hf using fun v : Fin (n + 1) =>
    he j (s.obj v) (t.obj v) (Functor.congr_obj h v)
  obtain ⟨l, u, g, hg⟩ := IsFiltered.wideSpan f
  have hv (v : Fin (n + 1)) : (step F u).obj (s.obj v) = (step F u).obj (t.obj v) := by
    rw [← hg v, step_comp_obj, step_comp_obj, hf v]
  refine ⟨l, u, ?_⟩
  refine CategoryTheory.Functor.ext hv ?_
  intro v w e
  apply (leg F c l).map_injective
  simp only [Functor.comp_map, Functor.map_comp, eqToHom_map, leg_step_map]
  have hh := Functor.congr_hom h e
  change (leg F c j).map (s.map e) = eqToHom _ ≫ (leg F c j).map (t.map e) ≫ eqToHom _ at hh
  rw [hh]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- The mapped nerve cocone is a genuine simplicial colimit under finite
categorical lifting and eventual object equality. -/
def nerveCoconeIsColimit
    (ho : ∀ X : c.pt, ∃ (j : J) (x : F.obj j), (leg F c j).obj x = X)
    (ha : ArrowSurjective F c) (he : EventuallyEqualObjects F c)
    [∀ j, (leg F c j).Faithful] : IsColimit (nerveFunctor.mapCocone c) := by
  apply evaluationJointlyReflectsColimits
  intro n
  apply Types.FilteredColimit.isColimitOf'
  · intro s
    obtain ⟨j, t, ht⟩ := chain_surjective F c ho ha he n.unop.len s
    exact ⟨j, t, ht.symm⟩
  · intro j s t h
    exact chain_eventually_equal F c he j n.unop.len s t h

end CategoryTheory.FilteredNerveColimit

attribute [colib_tag "COL-0238",
  colib_ref "WeibelKBook" "V, proof of Theorem 3.1, page 20" "background"
    "Filtered nerves and sequential resolution unions"]
  CategoryTheory.FilteredNerveColimit.nerveCoconeIsColimit
