/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.InitialIntervals
public import Colib.CategoryTheory.Waldhausen.Rows.Completion
public import Colib.CategoryTheory.Waldhausen.Rows.Functoriality
public import Colib.CategoryTheory.Waldhausen.Rows.PostcomposeExact
public import Colib.CategoryTheory.Waldhausen.Additivity.ZeroFactorization

/-! # The unchanged initial flag of a genuine quotient row

Restriction to intervals starting at zero is fully faithful on all original
row maps. The inverse descends through the actual displayed quotient squares.
Pointwise weakness on this flag detects weakness on the entire row by gluing.

Implementation provenance: `Quillen/Waldhausen/SConstruction/Rows/InitialFlag.lean` at Quillen
commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Restrict every original row and natural transformation to its entire initial flag. -/
def initialFlagFunctor (n : SimplexCategory) : Obj W n ⥤ (Fin (n.len + 1) ⥤ C) where
  obj A := initialIntervals n ⋙ A.obj
  map f := Functor.whiskerLeft (initialIntervals n) f.hom
  map_id _ := by ext i; rfl
  map_comp _ _ := by ext i; rfl

/-- Every original initial-flag arrow is a genuine cofibration. -/
theorem initialFlag_map_cof {n : SimplexCategory} (A : Obj W n)
    {i j : Fin (n.len + 1)} (f : i ⟶ j) :
    W.cof (((initialFlagFunctor W n).obj A).map f) :=
  A.property.cofibration 0 i j (Fin.zero_le _) (leOfHom f)

/-- Original quotient maps commute with every original interval arrow. -/
theorem initialQuotient_naturality {n : SimplexCategory} (A : Obj W n)
    {p q : Interval n} (f : p ⟶ q) :
    initialQuotient W A p ≫ A.obj.map f =
      ((initialFlagFunctor W n).obj A).map (homOfLE (leOfHom f).2) ≫
        initialQuotient W A q := by
  simp only [initialQuotient, initialFlagFunctor, Functor.comp_map, ← Functor.map_comp]
  congr 1

/-- Any transformation of the initial flags satisfies the actual quotient descent relation. -/
theorem initialFlag_descent_condition {n : SimplexCategory} {A B : Obj W n}
    (a : (initialFlagFunctor W n).obj A ⟶ (initialFlagFunctor W n).obj B)
    (p : Interval n) :
    A.obj.map (homOfLE (show interval 0 p.val.1 (Fin.zero_le _) ≤
      interval 0 p.val.2 (Fin.zero_le _) from ⟨le_rfl,p.property⟩)) ≫
        (a.app p.val.2 ≫ initialQuotient W B p) =
      A.obj.map (homOfLE (show interval 0 p.val.1 (Fin.zero_le _) ≤
        interval p.val.1 p.val.1 le_rfl from ⟨Fin.zero_le _,le_rfl⟩)) ≫
          (A.property.zero p.val.1).to_ (B.obj.obj p) := by
  erw [← Category.assoc, a.naturality (homOfLE p.property), Category.assoc]
  change a.app p.val.1 ≫ B.obj.map _ ≫ B.obj.map _ = _
  erw [(B.property.quotient 0 p.val.1 p.val.2 (Fin.zero_le _) p.property).w]
  rw [← Category.assoc, Additivity.comp_through_isZero W (B.property.zero p.val.1)]
  exact (Additivity.comp_through_isZero W (A.property.zero p.val.1) _ _).symm

/-- Descend the given flag map through one original quotient pushout. -/
def extendInitialFlagAt {n : SimplexCategory} {A B : Obj W n}
    (a : (initialFlagFunctor W n).obj A ⟶ (initialFlagFunctor W n).obj B)
    (p : Interval n) : A.obj.obj p ⟶ B.obj.obj p :=
  (A.property.quotient 0 p.val.1 p.val.2 (Fin.zero_le _) p.property).desc
    (a.app p.val.2 ≫ initialQuotient W B p)
    ((A.property.zero p.val.1).to_ (B.obj.obj p)) (initialFlag_descent_condition W a p)

/-- The descendant retains the entire original quotient comparison equation. -/
@[reassoc (attr := simp)] theorem initialQuotient_extendInitialFlagAt
    {n : SimplexCategory} {A B : Obj W n}
    (a : (initialFlagFunctor W n).obj A ⟶ (initialFlagFunctor W n).obj B) (p : Interval n) :
    initialQuotient W A p ≫ extendInitialFlagAt W a p = a.app p.val.2 ≫ initialQuotient W B p :=
  (A.property.quotient 0 p.val.1 p.val.2 (Fin.zero_le _) p.property).inl_desc _ _ _

/-- The actual quotient descendants form a natural transformation on all intervals. -/
theorem extendInitialFlagAt_naturality {n : SimplexCategory} {A B : Obj W n}
    (a : (initialFlagFunctor W n).obj A ⟶ (initialFlagFunctor W n).obj B)
    {p q : Interval n} (f : p ⟶ q) :
    A.obj.map f ≫ extendInitialFlagAt W a q = extendInitialFlagAt W a p ≫ B.obj.map f := by
  apply (A.property.quotient 0 p.val.1 p.val.2 (Fin.zero_le _) p.property).hom_ext
  · change initialQuotient W A p ≫ A.obj.map f ≫ extendInitialFlagAt W a q =
      initialQuotient W A p ≫ extendInitialFlagAt W a p ≫ B.obj.map f
    rw [← Category.assoc, initialQuotient_naturality, Category.assoc,
      initialQuotient_extendInitialFlagAt]
    rw [← Category.assoc, a.naturality (homOfLE (leOfHom f).2),
      Category.assoc, ← initialQuotient_naturality]
    rw [initialQuotient_extendInitialFlagAt_assoc]
  · exact (A.property.zero p.val.1).eq_of_src _ _

/-- The genuine original row map extending a specified initial-flag transformation. -/
def extendInitialFlagMap {n : SimplexCategory} {A B : Obj W n}
    (a : (initialFlagFunctor W n).obj A ⟶ (initialFlagFunctor W n).obj B) : A ⟶ B :=
  (objects W n).homMk {
    app := extendInitialFlagAt W a
    naturality _ _ f := extendInitialFlagAt_naturality W a f }

/-- Every specified initial component is retained exactly. -/
@[simp] theorem extendInitialFlagAt_initial {n : SimplexCategory} {A B : Obj W n}
    (a : (initialFlagFunctor W n).obj A ⟶ (initialFlagFunctor W n).obj B)
    (i : Fin (n.len + 1)) : extendInitialFlagAt W a (interval 0 i (Fin.zero_le _)) = a.app i := by
  have h := initialQuotient_extendInitialFlagAt W a (interval 0 i (Fin.zero_le _))
  change A.obj.map (𝟙 _) ≫ _ = a.app i ≫ B.obj.map (𝟙 _) at h
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id] at h
  exact h

/-- Restriction of the actual descendant is exactly the given initial-flag map. -/
@[simp] theorem initialFlagFunctor_map_extend {n : SimplexCategory} {A B : Obj W n}
    (a : (initialFlagFunctor W n).obj A ⟶ (initialFlagFunctor W n).obj B) :
    (initialFlagFunctor W n).map (extendInitialFlagMap W a) = a := by
  ext i
  exact extendInitialFlagAt_initial W a i

/-- Original quotient universal properties detect equality of whole-row maps. -/
instance initialFlagFunctor_faithful (n : SimplexCategory) : (initialFlagFunctor W n).Faithful where
  map_injective {A B} f g h := by
    apply ObjectProperty.hom_ext
    ext p
    apply (A.property.quotient 0 p.val.1 p.val.2 (Fin.zero_le _) p.property).hom_ext
    · erw [f.hom.naturality, g.hom.naturality]
      rw [show f.hom.app (interval 0 p.val.2 (Fin.zero_le _)) =
        g.hom.app (interval 0 p.val.2 (Fin.zero_le _)) from congrArg (fun a ↦ a.app p.val.2) h]
    · exact (A.property.zero p.val.1).eq_of_src _ _

/-- Every initial-flag map extends by the displayed original quotient pushouts. -/
instance initialFlagFunctor_full (n : SimplexCategory) : (initialFlagFunctor W n).Full where
  map_surjective a := ⟨extendInitialFlagMap W a, initialFlagFunctor_map_extend W a⟩

/-- The explicit fully faithful structure on the unchanged initial restriction. -/
def initialFlagFullyFaithful (n : SimplexCategory) : (initialFlagFunctor W n).FullyFaithful where
  preimage := extendInitialFlagMap W
  map_preimage := initialFlagFunctor_map_extend W
  preimage_map f := (initialFlagFunctor W n).map_injective
    (initialFlagFunctor_map_extend W ((initialFlagFunctor W n).map f))

/-- Genuine Waldhausen gluing detects weakness of the entire row on its initial flag. -/
theorem weq_iff_initialFlag {n : SimplexCategory} {A B : Obj W n} (f : A ⟶ B) :
    weq W n f ↔ ∀ i, W.weq (((initialFlagFunctor W n).map f).app i) := by
  refine ⟨fun hf i ↦ hf _, ?_⟩
  intro hf p
  rcases p with ⟨⟨i,j⟩, hij⟩
  exact W.gluing
    (f.hom.app (interval 0 i (Fin.zero_le _))) (f.hom.app (interval 0 j (Fin.zero_le _)))
    (f.hom.app (interval i i le_rfl)) (f.hom.app (interval i j hij))
    (A.property.cofibration 0 i j (Fin.zero_le _) hij)
    (B.property.cofibration 0 i j (Fin.zero_le _) hij)
    (A.property.quotient 0 i j (Fin.zero_le _) hij)
    (B.property.quotient 0 i j (Fin.zero_le _) hij)
    (f.hom.naturality _) (f.hom.naturality _) (f.hom.naturality _) (f.hom.naturality _)
    (hf i) (hf j) (W.weq_iso _ ((A.property.zero i).isIso (B.property.zero i) _))

/-- Actual quotient descent preserves pointwise weak initial transformations. -/
theorem extendInitialFlagMap_weak {n : SimplexCategory} {A B : Obj W n}
    (a : (initialFlagFunctor W n).obj A ⟶ (initialFlagFunctor W n).obj B)
    (ha : ∀ i, W.weq (a.app i)) : weq W n (extendInitialFlagMap W a) := by
  apply (weq_iff_initialFlag W _).2
  simpa only [initialFlagFunctor_map_extend] using ha

end CategoryTheory.Waldhausen.QuotientRows
