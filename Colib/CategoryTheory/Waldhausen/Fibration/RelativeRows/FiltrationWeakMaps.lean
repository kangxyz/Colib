/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.WeakChains
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-! # Original initial filtrations and genuine fine-weak detection

The target is the actual `ComposableArrows C n.len` category consumed by the
finite replacement construction. The functor retains every original natural
transformation. Fine weakness of its original components detects fine
weakness on the entire quotient row by actual Waldhausen gluing.
No quotient-presentation equivalence is assumed or concluded.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/FiltrationWeakMaps.lean`
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

/-- The unchanged initial chain, including all original component maps. -/
def initialFiltrationFunctor (n : SimplexCategory) : Obj N n ⥤ ComposableArrows C n.len where
  obj F := initialFiltration F.obj
  map f := Functor.whiskerLeft (initialFiltrationIndex n) f.hom.hom
  map_id _ := by ext i; rfl
  map_comp _ _ := by ext i; rfl

@[simp] theorem initialFiltrationFunctor_obj (n : SimplexCategory) (F : Obj N n) :
    (initialFiltrationFunctor N n).obj F = initialFiltration F.obj := rfl

@[simp] theorem initialFiltrationFunctor_map_app {n : SimplexCategory}
    {F G : Obj N n} (f : F ⟶ G) (i : Fin (n.len + 1)) :
    ((initialFiltrationFunctor N n).map f).app i =
      f.hom.hom.app (interval 0 i.succ (Fin.zero_le _)) := rfl

/-- The initial vertex is the original first-object evaluation. -/
@[simp] theorem first_obj (n : SimplexCategory) (F : Obj N n) :
    (first N n).obj F = F.obj.obj.obj (interval 0 1 (Fin.zero_le _)) := rfl


/-- Fine-weak original row maps remain pointwise fine-weak on the original chain. -/
theorem initialFiltrationFunctor_map_weak {n : SimplexCategory} {F G : Obj N n}
    (f : F ⟶ G) (hf : (waldhausenStructure N n).weq f) (i : Fin (n.len + 1)) :
    V.weq (((initialFiltrationFunctor N n).map f).app i) :=
  hf (interval 0 i.succ (Fin.zero_le _))

/-- The omitted zero vertex has an actual isomorphism, so it needs no extra weak hypothesis. -/
theorem initialComponent_weak {n : SimplexCategory} {F G : Obj N n} (f : F ⟶ G)
    (hf : ∀ i, V.weq (((initialFiltrationFunctor N n).map f).app i))
    (i : Fin ((addInitial.obj n).len + 1)) :
    V.weq (f.hom.hom.app (interval 0 i (Fin.zero_le _))) := by
  change Fin (n.len + 1 + 1) at i
  cases i using Fin.cases with
  | zero => exact V.weq_iso _ ((F.obj.property.zero 0).isIso (G.obj.property.zero 0) _)
  | succ i => exact hf i

/-- Actual quotient gluing detects fine weakness of the original whole-row map. -/
theorem weq_iff_initialFiltrationFunctor {n : SimplexCategory} {F G : Obj N n} (f : F ⟶ G) :
    (waldhausenStructure N n).weq f ↔
      ∀ i, V.weq (((initialFiltrationFunctor N n).map f).app i) := by
  refine ⟨fun hf i ↦ initialFiltrationFunctor_map_weak N f hf i, ?_⟩
  intro hf p
  rcases p with ⟨⟨i,j⟩, hij⟩
  exact V.gluing
    (f.hom.hom.app (interval 0 i (Fin.zero_le _)))
    (f.hom.hom.app (interval 0 j (Fin.zero_le _)))
    (f.hom.hom.app (interval i i le_rfl))
    (f.hom.hom.app (interval i j hij))
    (F.obj.property.cofibration 0 i j (Fin.zero_le _) hij)
    (G.obj.property.cofibration 0 i j (Fin.zero_le _) hij)
    (F.obj.property.quotient 0 i j (Fin.zero_le _) hij)
    (G.obj.property.quotient 0 i j (Fin.zero_le _) hij)
    (f.hom.hom.naturality _) (f.hom.hom.naturality _)
    (f.hom.hom.naturality _) (f.hom.hom.naturality _)
    (initialComponent_weak N f hf i) (initialComponent_weak N f hf j)
    (V.weq_iso _ ((F.obj.property.zero i).isIso (G.obj.property.zero i) _))

/-- The original functor commutes strictly with every original ordinal restriction. -/
theorem initialFiltrationFunctor_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    reindex N α ⋙ initialFiltrationFunctor N m =
      initialFiltrationFunctor N n ⋙
        (Functor.whiskeringLeft (Fin (m.len + 1)) (Fin (n.len + 1)) C).obj
          (SimplexCategory.toCat.map α).toFunctor := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
