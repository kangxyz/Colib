/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# The category of all semisimplices and its original last-vertex functor

Objects are all finite chains, including degenerate ones. Morphisms are actual
injective index maps with strict face equality. The last-vertex functor retains
the source equality transport and the original terminal segment of the chain.

Implementation provenance:
`Quillen/CategoryTheory/SemisimplexResolution/Basic.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
universe u
namespace CategoryTheory.SemisimplexResolution
variable (C : Type u) [SmallCategory C]

/-- A finite nonempty chain in `C`, retaining its arrows and allowing repeated vertices. -/
structure Obj : Type u where
  /-- The number of arrows in the chain; its vertices are indexed by `Fin (dim + 1)`. -/
  dim : ℕ
  /-- The functor describing the objects and arrows of the chain in `C`. -/
  chain : ComposableArrows C dim

/-- The functor between finite ordinal categories induced by an order embedding. -/
abbrev indexFunctor {n m : ℕ} (a : Fin (n + 1) ↪o Fin (m + 1)) :
    Fin (n + 1) ⥤ Fin (m + 1) := a.monotone.functor

/-- A face map from `A` to `B`, specified by an order embedding for which restricting the target
chain gives the source chain exactly. -/
structure Hom (A B : Obj C) : Type u where
  /-- The order embedding selecting the source vertices among the target vertices. -/
  index : Fin (A.dim + 1) ↪o Fin (B.dim+1)
  face : indexFunctor index ⋙ B.chain = A.chain

@[ext] theorem Hom.ext {A B : Obj C} {f g : Hom C A B} (h : f.index = g.index) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : SmallCategory (Obj C) where
  Hom := Hom C
  id A := ⟨(OrderIso.refl _).toOrderEmbedding, rfl⟩
  comp f g := ⟨f.index.trans g.index, by
    change indexFunctor f.index ⋙ (indexFunctor g.index ⋙ _) = _
    rw [g.face, f.face]⟩
  id_comp _ := Hom.ext C rfl
  comp_id _ := Hom.ext C rfl
  assoc _ _ _ := Hom.ext C rfl

/-- The terminal vertex of the chain `A`. -/
abbrev lastObj (A : Obj C) : C := A.chain.obj (Fin.last A.dim)

/-- The map between last vertices induced by a face `f`, using its chain equality and the terminal
segment of the target chain. -/
def lastMap {A B : Obj C} (f : A ⟶ B) : lastObj C A ⟶ lastObj C B :=
  eqToHom (congrArg (fun T : ComposableArrows C A.dim => T.obj (Fin.last A.dim)) f.face).symm ≫
    B.chain.map (homOfLE (Fin.le_last (f.index (Fin.last A.dim))))

lemma lastMap_id (A : Obj C) : lastMap C (𝟙 A) = 𝟙 (lastObj C A) := by
  simp [lastMap]

lemma face_map {A B : Obj C} (f : A ⟶ B) {i j : Fin (A.dim + 1)} (a : i ⟶ j) :
    B.chain.map ((indexFunctor f.index).map a) ≫
      eqToHom (congrArg (fun T : ComposableArrows C A.dim => T.obj j) f.face) =
    eqToHom (congrArg (fun T : ComposableArrows C A.dim => T.obj i) f.face) ≫
      A.chain.map a := by
  simpa only [eqToIso.hom, eqToHom_app, Functor.comp_map] using
    (eqToIso f.face).hom.naturality a

lemma lastMap_comp {A B D : Obj C} (f : A ⟶ B) (g : B ⟶ D) :
    lastMap C (f ≫ g) = lastMap C f ≫ lastMap C g := by
  dsimp [lastMap]
  rw [Category.assoc]
  rw [← Category.assoc (B.chain.map _)]
  have h := face_map C g (homOfLE (Fin.le_last (f.index (Fin.last A.dim))))
  have h' := congrArg (fun k =>
    eqToHom (congrArg (fun T : ComposableArrows C B.dim =>
      T.obj (f.index (Fin.last A.dim))) g.face).symm ≫ k ≫
    eqToHom (congrArg (fun T : ComposableArrows C B.dim =>
      T.obj (Fin.last B.dim)) g.face).symm) h
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    eqToHom_trans_assoc, Category.id_comp] at h'
  rw [← h']
  simp only [Category.assoc]
  rw [eqToHom_trans_assoc]
  rw [← D.chain.map_comp]
  rfl

/-- The functor from finite chains and face maps to `C` that selects the last vertex and maps a
face through the remaining terminal segment. -/
def lastVertex : Obj C ⥤ C where
  obj := lastObj C
  map := lastMap C
  map_id := lastMap_id C
  map_comp := lastMap_comp C

end CategoryTheory.SemisimplexResolution
