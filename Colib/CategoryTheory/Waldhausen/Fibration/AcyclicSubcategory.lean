/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.WeakEquivalenceCofiber
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-! # The actual acyclic subcategory for nested weak equivalences

The fine and coarse Waldhausen structures share their cofibration and chosen
zero data explicitly. Objects are genuinely coarse-acyclic; the inherited
weak equivalences remain the fine ones. Pushouts and quotient closure are
proved by coarse gluing. Only the separate assertion that every map between
acyclic objects is coarse-weak uses saturation.


Implementation provenance:
`Quillen/Waldhausen/Fibration/AcyclicSubcategory.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C]

/-- Two genuine weak-equivalence structures with the same underlying
cofibration category and an explicit inclusion of the fine weak class. -/
structure NestedWeakEquivalences (V : Structure C) where
  /-- The Waldhausen structure with the same cofibrations and chosen zero as `V` and a
  weak-equivalence class containing `V.weq`. -/
  coarse : Structure C
  cof_eq : coarse.cof = V.cof
  zero_eq : coarse.zero = V.zero
  le_weq : V.weq ≤ coarse.weq

section Closure
variable (W : Structure C)

/-- Coarse acyclicity is preserved by actual isomorphisms. -/
theorem acyclic_of_iso {X Y : C} (hX : Acyclic W X) (e : X ≅ Y) : Acyclic W Y := by
  have h : W.isZero.to_ Y = W.isZero.to_ X ≫ e.hom := W.isZero.eq_of_src _ _
  unfold Acyclic
  rw [h]
  exact W.weq.comp_mem _ _ hX (W.weq_iso _ inferInstance)

/-- Actual pushouts of three acyclic objects along a cofibration are acyclic. -/
theorem acyclic_of_isPushout {A B D P : C}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P}
    (hi : W.cof i) (h : IsPushout i f g j)
    (hA : Acyclic W A) (hB : Acyclic W B) (hD : Acyclic W D) : Acyclic W P :=
  W.gluing (W.isZero.to_ A) (W.isZero.to_ B) (W.isZero.to_ D) (W.isZero.to_ P)
    (W.cof.id_mem W.zero) hi (IsPushout.id_horiz (𝟙 W.zero)) h
    (W.isZero.eq_of_src _ _) (W.isZero.eq_of_src _ _)
    (W.isZero.eq_of_src _ _) (W.isZero.eq_of_src _ _) hA hB hD

/-- Quotient closure is separately derived by gluing, and permits any actual
zero object in the displayed cofiber square. No saturation is needed. -/
theorem acyclic_quotient_of_isPushout {A B Q Z : C} (hZ : IsZero Z)
    {i : A ⟶ B} {q : B ⟶ Q} (hi : W.cof i)
    (h : IsPushout i (hZ.from_ A) q (hZ.to_ Q))
    (hA : Acyclic W A) (hB : Acyclic W B) : Acyclic W Q :=
  acyclic_of_isPushout W hi h hA hB (acyclic_of_isZero W hZ)

/-- Saturation makes every actual morphism between acyclic objects coarse-weak. -/
theorem weak_of_acyclic [W.weq.HasTwoOutOfThreeProperty] {X Y : C}
    (f : X ⟶ Y) (hX : Acyclic W X) (hY : Acyclic W Y) : W.weq f := by
  apply W.weq.of_precomp (W.isZero.to_ X) f hX
  have h : W.isZero.to_ X ≫ f = W.isZero.to_ Y := W.isZero.eq_of_src _ _
  rw [h]
  exact hY
end Closure

variable {V : Structure C} (N : NestedWeakEquivalences V)

/-- The actual coarse-acyclic object predicate. -/
def acyclicObjects : ObjectProperty C := Acyclic N.coarse
/-- The full subcategory of `C` consisting of objects acyclic for the coarse Waldhausen
structure `N.coarse`. -/
abbrev AcyclicCategory := (acyclicObjects N).FullSubcategory

instance acyclicObjects_isClosedUnderIsomorphisms : (acyclicObjects N).IsClosedUnderIsomorphisms
    where
  of_iso e h := acyclic_of_iso N.coarse h e

/-- The original underlying inclusion, unchanged on all morphisms. -/
def acyclicInclusion : AcyclicCategory N ⥤ C := (acyclicObjects N).ι

/-- The inherited chosen zero is literally the original fine zero object. -/
def acyclicZero : AcyclicCategory N := ⟨V.zero, by
  change Acyclic N.coarse V.zero
  rw [← N.zero_eq]
  exact acyclic_zero N.coarse⟩

theorem acyclicIsZero : IsZero (acyclicZero N) where
  unique_to X := by
    refine ⟨{ default := (acyclicObjects N).homMk (V.isZero.to_ X.obj), uniq := ?_ }⟩
    intro f
    exact ObjectProperty.hom_ext _ (V.isZero.eq_of_src _ _)
  unique_from X := by
    refine ⟨{ default := (acyclicObjects N).homMk (V.isZero.from_ X.obj), uniq := ?_ }⟩
    intro f
    exact ObjectProperty.hom_ext _ (V.isZero.eq_of_tgt _ _)

/-- Existence of a genuine inherited pushout, with its actual ambient square. -/
theorem acyclic_pushout_exists {A B D : AcyclicCategory N}
    (i : A ⟶ B) (f : A ⟶ D) (hi : V.cof i.hom) :
    ∃ (P : AcyclicCategory N) (g : B ⟶ P) (j : D ⟶ P),
      IsPushout i f g j ∧ IsPushout i.hom f.hom g.hom j.hom := by
  obtain ⟨P, g, j, h⟩ := V.pushout_exists i.hom f.hom hi
  have hP : Acyclic N.coarse P := acyclic_of_isPushout N.coarse
    (by rwa [N.cof_eq]) h A.property B.property D.property
  let P' : AcyclicCategory N := ⟨P, hP⟩
  let g' : B ⟶ P' := (acyclicObjects N).homMk g
  let j' : D ⟶ P' := (acyclicObjects N).homMk j
  exact ⟨P', g', j', IsPushout.of_map_of_faithful (acyclicObjects N).ι h, h⟩

/-- Every displayed inherited pushout along a cofibration remains the genuine
ambient pushout, by comparison with the constructed one. -/
theorem acyclicInclusion_map_pushout {A B D P : AcyclicCategory N}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P}
    (hi : V.cof i.hom) (h : IsPushout i f g j) :
    IsPushout i.hom f.hom g.hom j.hom := by
  obtain ⟨P₀, g₀, j₀, h₀, hamb⟩ := acyclic_pushout_exists N i f hi
  let e : P₀ ≅ P := h₀.isoIsPushout _ _ h
  apply hamb.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ((acyclicObjects N).ι.mapIso e)
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.id_comp]
    exact congrArg (fun k ↦ k.hom) (h₀.inl_isoIsPushout_hom _ _ h)
  · simp only [Iso.refl_hom, Category.id_comp]
    exact congrArg (fun k ↦ k.hom) (h₀.inr_isoIsPushout_hom _ _ h)

/-- Coarse-acyclic objects carry the genuinely inherited fine Waldhausen structure. -/
def acyclicStructure : Structure (AcyclicCategory N) where
  zero := acyclicZero N
  isZero := acyclicIsZero N
  cof := V.cof.inverseImage (acyclicObjects N).ι
  weq := V.weq.inverseImage (acyclicObjects N).ι
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := by
    intro X Y f hf
    let : IsIso f := hf
    exact V.cof_iso f.hom inferInstance
  weq_iso := by
    intro X Y f hf
    let : IsIso f := hf
    exact V.weq_iso f.hom inferInstance
  cof_zero X := by
    have h : ((acyclicIsZero N).to_ X).hom = V.isZero.to_ X.obj := V.isZero.eq_of_src _ _
    change V.cof ((acyclicIsZero N).to_ X).hom
    rw [h]
    exact V.cof_zero X.obj
  pushout_exists i f hi := by
    obtain ⟨P, g, j, h, _⟩ := acyclic_pushout_exists N i f hi
    exact ⟨P, g, j, h⟩
  cof_pushout hi h := V.cof_pushout hi (acyclicInclusion_map_pushout N hi h)
  gluing := by
    intro A B D P A' B' D' P' i f g j i' f' g' j' a b d p hi hi' h h' ei ef eg ej ha hb hd
    exact V.gluing a.hom b.hom d.hom p.hom hi hi'
      (acyclicInclusion_map_pushout N hi h) (acyclicInclusion_map_pushout N hi' h')
      (congrArg (fun k ↦ k.hom) ei) (congrArg (fun k ↦ k.hom) ef)
      (congrArg (fun k ↦ k.hom) eg) (congrArg (fun k ↦ k.hom) ej) ha hb hd

/-- The original inclusion is genuinely exact for the fine weak equivalences. -/
theorem acyclicInclusion_exact : IsExact (acyclicStructure N).cof (acyclicStructure N).weq
    V.cof V.weq (acyclicInclusion N) where
  zero h := V.isZero.of_iso ((acyclicObjects N).ι.mapIso (h.iso (acyclicIsZero N)))
  cofibration _ h := h
  weak _ h := h
  pushout hi h := acyclicInclusion_map_pushout N hi h

/-- Changing only the fine weak class to the coarse class is an actual exact functor. -/
theorem changeWeak_exact : IsExact V.cof V.weq N.coarse.cof N.coarse.weq (𝟭 C) where
  zero h := h
  cofibration f h := by change N.coarse.cof f; rwa [N.cof_eq]
  weak f h := N.le_weq f h
  pushout _ h := h

/-- The same actual acyclic inclusion into the coarse structure is exact. -/
theorem acyclicInclusion_coarse_exact : IsExact (acyclicStructure N).cof (acyclicStructure N).weq
    N.coarse.cof N.coarse.weq (acyclicInclusion N) :=
  (acyclicInclusion_exact N).comp (changeWeak_exact N)

/-- The inherited zero is sent to the original chosen fine zero exactly. -/
@[simp] theorem acyclicInclusion_zero :
    (acyclicInclusion N).obj (acyclicStructure N).zero = V.zero := rfl

/-- The coarse structure has the original chosen fine zero. -/
@[simp] theorem NestedWeakEquivalences.coarse_zero : N.coarse.zero = V.zero := N.zero_eq


/-- Actual quotient closure in the original fine structure, separately from
construction of the inherited Waldhausen structure. -/
theorem fine_cofiber_acyclic (X : ExtensionCategory.Obj V)
    (hA : Acyclic N.coarse X.obj.left) (hB : Acyclic N.coarse X.obj.right) :
    Acyclic N.coarse ((ExtensionCategory.cofiber V).obj X) :=
  acyclic_quotient_of_isPushout N.coarse V.isZero (by rw [N.cof_eq]; exact X.property)
    (ExtensionCategory.cofiber_isPushout V X) hA hB

/-- All morphisms of the acyclic category become coarse-weak under saturation;
this does not change its inherited fine weak-equivalence class. -/
theorem acyclicInclusion_map_coarse_weak [N.coarse.weq.HasTwoOutOfThreeProperty]
    {X Y : AcyclicCategory N} (f : X ⟶ Y) : N.coarse.weq ((acyclicInclusion N).map f) :=
  weak_of_acyclic N.coarse f.hom X.property Y.property

end CategoryTheory.Waldhausen.Fibration


namespace CategoryTheory.Waldhausen.Fibration

attribute [colib_tag "COL-0251",
  colib_ref "Waldhausen1985" "Section 1.6, Theorem 1.6.4, the category C^w"
    "adaptation"
    "Original fine weak equivalences on the full subcategory of coarse acyclic objects"]
  acyclicStructure
  acyclicInclusion_exact

end CategoryTheory.Waldhausen.Fibration
