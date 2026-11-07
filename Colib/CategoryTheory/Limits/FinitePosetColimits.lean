/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Order.UpperLower.Basic

/-!
# Ordinary colimit gluing over lower ideals in posets

Principal lower ideals retain their actual terminal-object cocones. Two lower
ideals covering the poset glue along the displayed pushout and overlap cocone,
with original colimit universal properties. The mapped gluing theorem assumes
only the displayed preserved colimits and actual mapped pushout.

Implementation provenance: `Quillen/Aglib/CategoryTheory/Limits/FinitePosetColimits.lean` at
Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe w w' z u v u' v'

namespace CategoryTheory.Limits.FinitePosetLatching
variable {J : Type w} [Category J] {K : Type w'} [Category K]
  {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) {G H : J ⥤ C}

/-- A literal colimit cocone whose image under the original functor is also a
colimit. This only packages actual universal properties, not a filling axiom. -/
def HasPreservedColimit (G : J ⥤ C) : Prop :=
  ∃ c : Cocone G, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c))

/-- Transport the actual cocone along a specified original-diagram isomorphism. -/
theorem HasPreservedColimit.ofIso (e : G ≅ H) (h : HasPreservedColimit F H) :
    HasPreservedColimit F G := by
  obtain ⟨c, ⟨hc⟩, ⟨hFc⟩⟩ := h
  refine ⟨(Cocone.precompose e.hom).obj c,
    ⟨(IsColimit.precomposeHomEquiv e c).symm hc⟩, ?_⟩
  exact ⟨((IsColimit.precomposeHomEquiv (Functor.isoWhiskerRight e F)
    (F.mapCocone c)).symm hFc).ofIsoColimit F.mapCoconePrecompose.symm⟩

/-- Equivalent index categories reindex both universal properties of the same
source cocone. -/
theorem HasPreservedColimit.whisker (e : K ≌ J) (h : HasPreservedColimit F G) :
    HasPreservedColimit F (e.functor ⋙ G) := by
  obtain ⟨c, ⟨hc⟩, ⟨hFc⟩⟩ := h
  exact ⟨c.whisker e.functor, ⟨hc.whiskerEquivalence e⟩, ⟨hFc.whiskerEquivalence e⟩⟩

end CategoryTheory.Limits.FinitePosetLatching

namespace CategoryTheory.Limits.FinitePosetLatching
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  (G : J ⥤ C)

/-- The literal inclusion of a subposet, retaining the original order arrows. -/
def inclusion (A : Set J) : A ⥤ J :=
  (show Monotone (fun x : A ↦ x.val) from fun _ _ h ↦ h).functor

/-- The restriction of the original diagram to a subposet. -/
abbrev restriction (A : Set J) : A ⥤ C := inclusion A ⋙ G

/-- Restrict the original cocone along a literal subposet inclusion. -/
abbrev restrictCocone (A : Set J) (c : Cocone G) : Cocone (restriction G A) :=
  c.whisker (inclusion A)

/-- A principal lower ideal carries its literal terminal-object cocone. -/
def principalCocone (m : J) : Cocone (restriction G (Set.Iic m)) where
  pt := G.obj m
  ι := {
    app x := G.map (homOfLE x.property)
    naturality x y f := by
      change G.map ((inclusion (Set.Iic m)).map f) ≫ G.map (homOfLE y.property) =
        G.map (homOfLE x.property) ≫ 𝟙 (G.obj m)
      rw [Category.comp_id, ← G.map_comp]
      congr 1 }

/-- No colimit-existence assumption is needed for a principal lower ideal. -/
def principalCoconeIsColimit (m : J) : IsColimit (principalCocone G m) where
  desc s := s.ι.app ⟨m, le_rfl⟩
  fac s x := s.w (homOfLE (show x ≤ (⟨m, le_rfl⟩ : Set.Iic m) from x.property))
  uniq s f hf := by
    have h := hf ⟨m, le_rfl⟩
    change G.map (𝟙 m) ≫ f = s.ι.app ⟨m, le_rfl⟩ at h
    simpa only [G.map_id, Category.id_comp] using h

/-- Every functor preserves the principal-ideal colimit, by its actual
terminal-object universal property. -/
def mappedPrincipalCoconeIsColimit {D : Type*} [Category* D] (F : C ⥤ D) (m : J) :
    IsColimit (F.mapCocone (principalCocone G m)) :=
  principalCoconeIsColimit (G ⋙ F) m

/-- The original intersection inclusion into the first lower ideal. -/
def intersectionLeft (A B : Set J) : (A ∩ B : Set J) ⥤ A :=
  (show Monotone (fun x : (A ∩ B : Set J) ↦ (⟨x.val, x.property.1⟩ : A)) from
    fun _ _ h ↦ h).functor

/-- The original intersection inclusion into the second lower ideal. -/
def intersectionRight (A B : Set J) : (A ∩ B : Set J) ⥤ B :=
  (show Monotone (fun x : (A ∩ B : Set J) ↦ (⟨x.val, x.property.2⟩ : B)) from
    fun _ _ h ↦ h).functor

variable {G} {A B : Set J}
  (cA : Cocone (restriction G A)) (cB : Cocone (restriction G B))
  (cI : Cocone (restriction G (A ∩ B)))
  (i : cI.pt ⟶ cA.pt) (j : cI.pt ⟶ cB.pt)
  (hi : ∀ x : (A ∩ B : Set J), cI.ι.app x ≫ i = cA.ι.app ⟨x.val, x.property.1⟩)
  (hj : ∀ x : (A ∩ B : Set J), cI.ι.app x ≫ j = cB.ι.app ⟨x.val, x.property.2⟩)
  {P : C} (a : cA.pt ⟶ P) (b : cB.pt ⟶ P) (sq : IsPushout i j a b)

include hi hj sq in
/-- On the overlap, the two actual colimit legs agree after the pushout. -/
theorem overlap_leg (x : (A ∩ B : Set J)) :
    cA.ι.app ⟨x.val, x.property.1⟩ ≫ a =
      cB.ι.app ⟨x.val, x.property.2⟩ ≫ b := by
  rw [← hi x, ← hj x, Category.assoc, Category.assoc, sq.w]

variable (hcover : ∀ x : J, x ∈ A ∨ x ∈ B)

/-- Glue the two actual cocone legs; agreement on the intersection is proved,
not selected independently at different occurrences of a vertex. -/
def gluedLeg (x : J) : G.obj x ⟶ P := by
  classical
  exact if hx : x ∈ A then cA.ι.app ⟨x, hx⟩ ≫ a
    else cB.ι.app ⟨x, (hcover x).resolve_left hx⟩ ≫ b

@[simp] theorem gluedLeg_in_left {x : J} (hx : x ∈ A) :
    gluedLeg cA cB a b hcover x = cA.ι.app ⟨x, hx⟩ ≫ a := by
  simp [gluedLeg, hx]

include hi hj sq in
theorem gluedLeg_in_right {x : J} (hx : x ∈ B) :
    gluedLeg cA cB a b hcover x = cB.ι.app ⟨x, hx⟩ ≫ b := by
  classical
  by_cases ha : x ∈ A
  · rw [gluedLeg_in_left _ _ _ _ _ ha]
    exact overlap_leg cA cB cI i j hi hj a b sq ⟨x, ha, hx⟩
  · simp [gluedLeg, ha]

variable (hA : IsLowerSet A) (hB : IsLowerSet B)

include hi hj sq hA hB in
/-- The glued legs are strictly natural on every original order arrow. -/
theorem gluedLeg_naturality {x y : J} (f : x ⟶ y) :
    G.map f ≫ gluedLeg cA cB a b hcover y = gluedLeg cA cB a b hcover x := by
  rcases hcover y with hy | hy
  · have hx := hA (leOfHom f) hy
    rw [gluedLeg_in_left _ _ _ _ _ hy, gluedLeg_in_left _ _ _ _ _ hx,
      ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ a)
      ((cA.ι.naturality (homOfLE (show (⟨x, hx⟩ : A) ≤ ⟨y, hy⟩ from leOfHom f))).trans
        (Category.comp_id _))
  · have hx := hB (leOfHom f) hy
    rw [gluedLeg_in_right cA cB cI i j hi hj a b sq hcover hy,
      gluedLeg_in_right cA cB cI i j hi hj a b sq hcover hx, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ b)
      ((cB.ι.naturality (homOfLE (show (⟨x, hx⟩ : B) ≤ ⟨y, hy⟩ from leOfHom f))).trans
        (Category.comp_id _))

/-- The actual pushout carries the original full diagram's glued cocone. -/
def gluedCocone : Cocone G where
  pt := P
  ι := {
    app := gluedLeg cA cB a b hcover
    naturality x y f := by
      change G.map f ≫ gluedLeg cA cB a b hcover y =
        gluedLeg cA cB a b hcover x ≫ 𝟙 P
      rw [Category.comp_id]
      exact gluedLeg_naturality cA cB cI i j hi hj a b sq hcover hA hB f }

include hi hj in
/-- The actual intersection colimit makes the two local universal maps agree. -/
theorem desc_compatible (hcA : IsColimit cA) (hcB : IsColimit cB) (hcI : IsColimit cI)
    (s : Cocone G) :
    i ≫ hcA.desc (restrictCocone G A s) = j ≫ hcB.desc (restrictCocone G B s) := by
  apply hcI.hom_ext
  intro x
  rw [← Category.assoc, hi x, hcA.fac, ← Category.assoc, hj x, hcB.fac]
  rfl

/-- Colimits on a lower-ideal cover assemble by the actual intersection
pushout. This proves the full universal property of the original diagram. -/
def gluedCoconeIsColimit
    (hcA : IsColimit cA) (hcB : IsColimit cB) (hcI : IsColimit cI) :
    IsColimit (gluedCocone cA cB cI i j hi hj a b sq hcover hA hB) := by
  let d (s : Cocone G) : P ⟶ s.pt := sq.desc
    (hcA.desc (restrictCocone G A s)) (hcB.desc (restrictCocone G B s))
    (desc_compatible cA cB cI i j hi hj hcA hcB hcI s)
  have hd (s : Cocone G) (x : J) :
      gluedLeg cA cB a b hcover x ≫ d s = s.ι.app x := by
    rcases hcover x with hx | hx
    · rw [gluedLeg_in_left _ _ _ _ _ hx, Category.assoc]
      change cA.ι.app ⟨x, hx⟩ ≫ (a ≫ sq.desc _ _ _) = _
      rw [sq.inl_desc]
      exact hcA.fac (restrictCocone G A s) ⟨x, hx⟩
    · rw [gluedLeg_in_right cA cB cI i j hi hj a b sq hcover hx, Category.assoc]
      change cB.ι.app ⟨x, hx⟩ ≫ (b ≫ sq.desc _ _ _) = _
      rw [sq.inr_desc]
      exact hcB.fac (restrictCocone G B s) ⟨x, hx⟩
  refine ⟨d, hd, ?_⟩
  intro s m hm
  apply sq.hom_ext
  · apply hcA.hom_ext
    intro x
    rw [← Category.assoc, ← Category.assoc,
      ← gluedLeg_in_left cA cB a b hcover x.property]
    exact (hm x.val).trans (hd s x.val).symm
  · apply hcB.hom_ext
    intro x
    rw [← Category.assoc, ← Category.assoc,
      ← gluedLeg_in_right cA cB cI i j hi hj a b sq hcover x.property]
    exact (hm x.val).trans (hd s x.val).symm

section Mapping
variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

/-- Preservation of the three lower-ideal colimits and their actual gluing
pushout proves preservation of the full glued colimit. -/
def mappedGluedCoconeIsColimit
    (hcA : IsColimit (F.mapCocone cA)) (hcB : IsColimit (F.mapCocone cB))
    (hcI : IsColimit (F.mapCocone cI))
    (hsq : IsPushout (F.map i) (F.map j) (F.map a) (F.map b)) :
    IsColimit (F.mapCocone (gluedCocone cA cB cI i j hi hj a b sq hcover hA hB)) := by
  have hiF (x : (A ∩ B : Set J)) :
      (F.mapCocone cI).ι.app x ≫ F.map i =
        (F.mapCocone cA).ι.app ⟨x.val, x.property.1⟩ := by
    exact (F.map_comp _ _).symm.trans (congrArg F.map (hi x))
  have hjF (x : (A ∩ B : Set J)) :
      (F.mapCocone cI).ι.app x ≫ F.map j =
        (F.mapCocone cB).ι.app ⟨x.val, x.property.2⟩ := by
    exact (F.map_comp _ _).symm.trans (congrArg F.map (hj x))
  let h := gluedCoconeIsColimit (G := G ⋙ F) (A := A) (B := B) (F.mapCocone cA) (F.mapCocone cB)
    (F.mapCocone cI) (F.map i) (F.map j) hiF hjF (F.map a) (F.map b)
    hsq hcover hA hB hcA hcB hcI
  apply h.ofIsoColimit
  refine Cocone.ext (Iso.refl _) ?_
  intro x
  change gluedLeg (G := G ⋙ F) (A := A) (B := B) (F.mapCocone cA) (F.mapCocone cB) (F.map a)
    (F.map b) hcover x ≫
    𝟙 (F.obj P) = F.map (gluedLeg cA cB a b hcover x)
  rw [Category.comp_id]
  rcases hcover x with hx | hx
  · rw [gluedLeg_in_left _ _ _ _ _ hx, gluedLeg_in_left _ _ _ _ _ hx, F.map_comp]
    rfl
  · rw [gluedLeg_in_right (G := G ⋙ F) (A := A) (B := B) (F.mapCocone cA) (F.mapCocone cB)
        (F.mapCocone cI) (F.map i) (F.map j) hiF hjF (F.map a) (F.map b) hsq hcover hx,
      gluedLeg_in_right cA cB cI i j hi hj a b sq hcover hx, F.map_comp]
    rfl

end Mapping

/-- Removing a maximal vertex leaves a lower ideal, the first part of the
actual finite-poset latching decomposition. -/
theorem complement_singleton_isLowerSet (m : J) (hm : IsMax m) :
    IsLowerSet ({m}ᶜ : Set J) := by
  intro y x hxy hy
  change y ≠ m at hy
  change x ≠ m
  intro hx
  subst x
  exact hy (hm.eq_of_le hxy).symm

/-- The remaining lower ideal and the principal lower ideal cover all objects. -/
theorem maximal_lower_cover (m : J) (x : J) :
    x ∈ ({m}ᶜ : Set J) ∨ x ∈ Set.Iic m := by
  by_cases hx : x = m
  · subst x; exact Or.inr le_rfl
  · exact Or.inl hx

/-- The overlap in a maximal-vertex attachment is exactly its strict boundary. -/
theorem maximal_lower_intersection (m : J) :
    ({m}ᶜ : Set J) ∩ Set.Iic m = Set.Iio m := by
  ext x
  exact ⟨fun h ↦ lt_of_le_of_ne h.2 h.1,
    fun h ↦ ⟨ne_of_lt h, h.le⟩⟩

section Existence
variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
  (hcA : IsColimit cA) (hcB : IsColimit cB) (hcI : IsColimit cI)

/-- The intersection comparison is the universal map into the first actual
restricted colimit. -/
def intersectionToLeft : cI.pt ⟶ cA.pt :=
  hcI.desc (cA.whisker (intersectionLeft A B))

/-- The intersection comparison is the universal map into the second actual
restricted colimit. -/
def intersectionToRight : cI.pt ⟶ cB.pt :=
  hcI.desc (cB.whisker (intersectionRight A B))

end Existence

end CategoryTheory.Limits.FinitePosetLatching

end
