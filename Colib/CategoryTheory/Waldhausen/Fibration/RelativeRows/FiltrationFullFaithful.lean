/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.FiltrationWeakMaps
public import Colib.CategoryTheory.Waldhausen.Additivity.ZeroFactorization

/-! # Full faithfulness of the original relative initial filtration

An arbitrary transformation between the original initial chains is augmented
by the unique map of actual zero vertices and descended through every actual
quotient pushout. Its naturality and uniqueness follow from those displayed
universal properties. No quotient completion or equivalence is an input.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/FiltrationFullFaithful.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- Include also the actual zero vertex in the unchanged initial intervals. -/
def augmentedInitialIndex (n : SimplexCategory) :
    Fin ((addInitial.obj n).len + 1) ⥤ Interval (addInitial.obj n) :=
  (show Monotone (fun i ↦ interval 0 i (Fin.zero_le i)) from fun _ _ h ↦ ⟨le_rfl,h⟩).functor

/-- The original quotient map from the initial interval to its displayed quotient. -/
def originalQuotient {n : SimplexCategory} (F : Obj N n) (p : Interval (addInitial.obj n)) :
    F.obj.obj.obj (interval 0 p.val.2 (Fin.zero_le _)) ⟶ F.obj.obj.obj p :=
  F.obj.obj.map (homOfLE ⟨Fin.zero_le _, le_rfl⟩)

/-- The original quotient maps respect every original interval map. -/
theorem originalQuotient_naturality {n : SimplexCategory} (F : Obj N n)
    {p q : Interval (addInitial.obj n)} (f : p ⟶ q) :
    originalQuotient N F p ≫ F.obj.obj.map f =
      (augmentedInitialIndex n ⋙ F.obj.obj).map (homOfLE (leOfHom f).2) ≫
        originalQuotient N F q := by
  simp only [originalQuotient, Functor.comp_map, ← Functor.map_comp]
  congr 1

/-- Adjoin the unique actual zero-vertex map to an arbitrary original chain transformation. -/
def augmentFiltrationMap {n : SimplexCategory} {F G : Obj N n}
    (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G) :
    augmentedInitialIndex n ⋙ F.obj.obj ⟶ augmentedInitialIndex n ⋙ G.obj.obj where
  app i := by
    change Fin (n.len + 1 + 1) at i
    cases i using Fin.cases with
    | zero => exact (F.obj.property.zero 0).to_ _
    | succ i => exact a.app i
  naturality i j f := by
    change Fin (n.len + 1 + 1) at i j
    cases i using Fin.cases with
    | zero => exact (F.obj.property.zero 0).eq_of_src _ _
    | succ i =>
      cases j using Fin.cases with
      | zero => have h : i.val+1 ≤ 0 := leOfHom f; omega
      | succ j => exact a.naturality (homOfLE (Nat.le_of_succ_le_succ (leOfHom f)))

@[simp] theorem augmentFiltrationMap_app_succ {n : SimplexCategory} {F G : Obj N n}
    (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G)
    (i : Fin (n.len + 1)) : (augmentFiltrationMap N a).app i.succ = a.app i := rfl

/-- The actual augmented map satisfies the original quotient descent relation. -/
theorem filtrationDescent_condition {n : SimplexCategory} {F G : Obj N n}
    (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G)
    (p : Interval (addInitial.obj n)) :
    F.obj.obj.map (homOfLE (show interval 0 p.val.1 (Fin.zero_le _) ≤
      interval 0 p.val.2 (Fin.zero_le _) from ⟨le_rfl,p.property⟩)) ≫
        ((augmentFiltrationMap N a).app p.val.2 ≫ originalQuotient N G p) =
      F.obj.obj.map (homOfLE (show interval 0 p.val.1 (Fin.zero_le _) ≤
        interval p.val.1 p.val.1 le_rfl from ⟨Fin.zero_le _,le_rfl⟩)) ≫
          (F.obj.property.zero p.val.1).to_ (G.obj.obj.obj p) := by
  erw [← Category.assoc, (augmentFiltrationMap N a).naturality (homOfLE p.property),
    Category.assoc]
  change (augmentFiltrationMap N a).app p.val.1 ≫
    G.obj.obj.map _ ≫ G.obj.obj.map _ = _
  erw [(G.obj.property.quotient 0 p.val.1 p.val.2 (Fin.zero_le _) p.property).w]
  rw [← Category.assoc, Additivity.comp_through_isZero V (G.obj.property.zero p.val.1)]
  exact (Additivity.comp_through_isZero V (F.obj.property.zero p.val.1) _ _).symm

/-- Descend the unchanged initial transformation through one original displayed quotient. -/
def extendFiltrationAt {n : SimplexCategory} {F G : Obj N n}
    (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G)
    (p : Interval (addInitial.obj n)) : F.obj.obj.obj p ⟶ G.obj.obj.obj p :=
  (F.obj.property.quotient 0 p.val.1 p.val.2 (Fin.zero_le _) p.property).desc
    ((augmentFiltrationMap N a).app p.val.2 ≫ originalQuotient N G p)
    ((F.obj.property.zero p.val.1).to_ (G.obj.obj.obj p))
    (filtrationDescent_condition N a p)

@[reassoc (attr := simp)] theorem originalQuotient_extendFiltrationAt
    {n : SimplexCategory} {F G : Obj N n}
    (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G)
    (p : Interval (addInitial.obj n)) :
    originalQuotient N F p ≫ extendFiltrationAt N a p =
      (augmentFiltrationMap N a).app p.val.2 ≫ originalQuotient N G p :=
  (F.obj.property.quotient 0 p.val.1 p.val.2 (Fin.zero_le _) p.property).inl_desc _ _ _

/-- The actual quotient descendants commute with every original interval map. -/
theorem extendFiltrationAt_naturality {n : SimplexCategory} {F G : Obj N n}
    (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G)
    {p q : Interval (addInitial.obj n)} (f : p ⟶ q) :
    F.obj.obj.map f ≫ extendFiltrationAt N a q = extendFiltrationAt N a p ≫ G.obj.obj.map f := by
  apply (F.obj.property.quotient 0 p.val.1 p.val.2 (Fin.zero_le _) p.property).hom_ext
  · change originalQuotient N F p ≫ F.obj.obj.map f ≫ extendFiltrationAt N a q =
      originalQuotient N F p ≫ extendFiltrationAt N a p ≫ G.obj.obj.map f
    rw [← Category.assoc, originalQuotient_naturality, Category.assoc,
      originalQuotient_extendFiltrationAt]
    rw [← Category.assoc, (augmentFiltrationMap N a).naturality (homOfLE (leOfHom f).2),
      Category.assoc, ← originalQuotient_naturality]
    rw [originalQuotient_extendFiltrationAt_assoc]
  · exact (F.obj.property.zero p.val.1).eq_of_src _ _

/-- The actual extension is a morphism of the original relative rows. -/
def extendFiltrationMap {n : SimplexCategory} {F G : Obj N n}
    (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G) : F ⟶ G :=
  (objects N n).homMk ((QuotientRows.objects V (addInitial.obj n)).homMk {
    app := extendFiltrationAt N a
    naturality _ _ f := extendFiltrationAt_naturality N a f })

/-- On every original initial object the descended map is exactly the given component. -/
@[simp] theorem extendFiltrationAt_initial {n : SimplexCategory} {F G : Obj N n}
    (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G)
    (i : Fin (n.len + 1)) :
    extendFiltrationAt N a (interval 0 i.succ (Fin.zero_le _)) = a.app i := by
  have h := originalQuotient_extendFiltrationAt N a (interval 0 i.succ (Fin.zero_le _))
  change F.obj.obj.map (𝟙 _) ≫ _ = a.app i ≫ G.obj.obj.map (𝟙 _) at h
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id] at h
  exact h

@[simp] theorem initialFiltrationFunctor_map_extend {n : SimplexCategory} {F G : Obj N n}
    (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G) :
    (initialFiltrationFunctor N n).map (extendFiltrationMap N a) = a := by
  ext i
  exact extendFiltrationAt_initial N a i

/-- Equality on the original initial filtration also retains the unique actual zero component. -/
theorem initialComponent_eq_of_map_eq {n : SimplexCategory} {F G : Obj N n}
    {f g : F ⟶ G} (h : (initialFiltrationFunctor N n).map f = (initialFiltrationFunctor N n).map g)
    (i : Fin ((addInitial.obj n).len + 1)) :
    f.hom.hom.app (interval 0 i (Fin.zero_le _)) = g.hom.hom.app (interval 0 i (Fin.zero_le _))
      := by
  change Fin (n.len + 1 + 1) at i
  cases i using Fin.cases with
  | zero => exact (F.obj.property.zero 0).eq_of_src _ _
  | succ i => exact congrArg (fun a ↦ a.app i) h

/-- The original filtration functor is faithful by each actual quotient universal property. -/
instance initialFiltrationFunctor_faithful (n : SimplexCategory) : (initialFiltrationFunctor N
    n).Faithful where
  map_injective {F G} f g h := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    ext p
    apply (F.obj.property.quotient 0 p.val.1 p.val.2 (Fin.zero_le _) p.property).hom_ext
    · erw [f.hom.hom.naturality, g.hom.hom.naturality,
        initialComponent_eq_of_map_eq N h p.val.2]
    · exact (F.obj.property.zero p.val.1).eq_of_src _ _

/-- Fullness uses the actual descended original transformation, with no choice of quotient
replacement. -/
instance initialFiltrationFunctor_full (n : SimplexCategory) : (initialFiltrationFunctor N
    n).Full where
  map_surjective a := ⟨extendFiltrationMap N a, initialFiltrationFunctor_map_extend N a⟩

/-- The genuine full-faithfulness datum for the unchanged original functor. -/
def initialFiltrationFullyFaithful (n : SimplexCategory) : (initialFiltrationFunctor N
    n).FullyFaithful where
  preimage := extendFiltrationMap N
  map_preimage := initialFiltrationFunctor_map_extend N
  preimage_map f := (initialFiltrationFunctor N n).map_injective
    (initialFiltrationFunctor_map_extend N ((initialFiltrationFunctor N n).map f))

/-- The full-faithfulness inverse is exactly the displayed quotient descendant. -/
@[simp] theorem initialFiltrationFullyFaithful_preimage {n : SimplexCategory} {F G : Obj N n}
    (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G) :
    (initialFiltrationFullyFaithful N n).preimage a = extendFiltrationMap N a := rfl

/-- Pointwise fine weakness of the original chain gives a fine-weak actual quotient extension. -/
theorem extendFiltrationMap_weak {n : SimplexCategory} {F G : Obj N n}
    (a : (initialFiltrationFunctor N n).obj F ⟶ (initialFiltrationFunctor N n).obj G)
    (ha : ∀ i, V.weq (a.app i)) : (waldhausenStructure N n).weq (extendFiltrationMap N a) := by
  apply (weq_iff_initialFiltrationFunctor N (extendFiltrationMap N a)).2
  simpa only [initialFiltrationFunctor_map_extend] using ha

end CategoryTheory.Waldhausen.Fibration.RelativeRows
