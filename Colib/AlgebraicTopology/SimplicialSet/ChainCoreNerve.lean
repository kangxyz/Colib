/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicTopology.SimplicialSet.Diagonal
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Core

/-! # The diagonal nerve of cores of composable chains

The objects are the native `Core (ComposableArrows D n)` and their ordinary nerves.
Diagonal evaluation uses the actual vertical isomorphism followed by the target
row's horizontal arrow. No rectangular-grid model is introduced.

Adapted from `Quillen/Waldhausen/QuillenComparison/ChainClassification.lean` and
`Quillen/Topology/Realization/Classification.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial
universe u v

namespace CategoryTheory

variable (D : Type u) [Category.{v} D]

/-- Reindex native composable chains and their invertible natural transformations. -/
def chainCoreReindex {m n : SimplexCategory} (α : m ⟶ n) :
    Core (ComposableArrows D n.len) ⥤ Core (ComposableArrows D m.len) where
  obj F := ⟨(SimplexCategory.toCat.map α).toFunctor ⋙ F.of⟩
  map e := ⟨Functor.isoWhiskerLeft (SimplexCategory.toCat.map α).toFunctor e.iso⟩
  map_id _ := by apply Core.hom_ext; rfl
  map_comp _ _ := by apply Core.hom_ext; rfl

/-- The cores of native composable-chain categories form a simplicial category. -/
def chainCoreSimplicial : SimplexCategoryᵒᵖ ⥤ Cat.{v, max u v} where
  obj n := Cat.of (Core (ComposableArrows D n.unop.len))
  map α := Cat.Hom.ofFunctor (chainCoreReindex D α.unop)
  map_id _ := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp _ _ := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The genuine bisimplicial nerve of the cores of composable chains. -/
def chainCoreNerve : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  chainCoreSimplicial D ⋙ nerveFunctor

end CategoryTheory

namespace SSet.ChainCore

variable {D : Type u} [Category.{v} D] {n : ℕ}

/-- Evaluate the two chain directions diagonally, using vertical then horizontal maps. -/
def evaluationSimplex (G : ComposableArrows (Core (ComposableArrows D n)) n) :
    ComposableArrows D n where
  obj i := (G.obj i).of.obj i
  map {i j} f := (G.map f).iso.hom.app i ≫ (G.obj j).of.map f
  map_id i := by
    rw [G.map_id, (G.obj i).of.map_id]
    exact Category.id_comp _
  map_comp {i j k} f g := by
    rw [G.map_comp, (G.obj k).of.map_comp]
    change (_ ≫ _) ≫ (_ ≫ _) = (_ ≫ _) ≫ (_ ≫ _)
    simp only [Category.assoc]
    congr 1
    rw [← (G.map g).iso.hom.naturality_assoc]

/-- The exact diagonal evaluation from the native chain-core nerve to the ordinary nerve. -/
def evaluation (D : Type u) [Category.{v} D] :
    diagonalSSet (chainCoreNerve D) ⟶ nerve D where
  app _ := ↾fun G ↦ evaluationSimplex G
  naturality _ _ _ := by ext G; rfl

/-- A chain gives a vertically constant simplex in the native chain-core diagonal. -/
def constant (D : Type u) [Category.{v} D] :
    nerve D ⟶ diagonalSSet (chainCoreNerve D) where
  app n := ↾fun F ↦ (Functor.const (Fin (n.unop.len + 1))).obj (Core.mk F)
  naturality _ _ _ := by ext F; rfl

/-- Diagonal evaluation recovers an actual vertically constant chain. -/
@[simp] theorem evaluationSimplex_constant (F : ComposableArrows D n) :
    evaluationSimplex ((Functor.const (Fin (n + 1))).obj (Core.mk F)) = F := by
  refine CategoryTheory.Functor.ext
    (F := evaluationSimplex ((Functor.const _).obj (Core.mk F))) (G := F)
    (fun _ ↦ rfl) ?_
  intro i j f
  change 𝟙 _ ≫ F.map f = _
  simp

/-- Evaluation is a strict retraction of the vertically constant section. -/
@[simp] theorem constant_evaluation (D : Type u) [Category.{v} D] :
    constant D ≫ evaluation D = 𝟙 (nerve D) := by
  ext n F
  exact evaluationSimplex_constant F

/-- Coherent natural isomorphisms between any two actual chain rows. -/
def rowTransport {m : ℕ} (G : ComposableArrows (Core (ComposableArrows D m)) n)
    (s t : Fin (n + 1)) : (G.obj s).of ≅ (G.obj t).of :=
  (G.map (homOfLE (Fin.zero_le s))).iso.symm ≪≫
    (G.map (homOfLE (Fin.zero_le t))).iso

@[simp] theorem rowTransport_self {m : ℕ}
    (G : ComposableArrows (Core (ComposableArrows D m)) n) (s : Fin (n + 1)) :
    rowTransport G s s = Iso.refl _ := by simp [rowTransport]

@[simp] theorem rowTransport_trans {m : ℕ}
    (G : ComposableArrows (Core (ComposableArrows D m)) n) (s t r : Fin (n + 1)) :
    rowTransport G s t ≪≫ rowTransport G t r = rowTransport G s r := by
  simp [rowTransport]

/-- On ordered rows, coherent transport is the original component isomorphism. -/
theorem rowTransport_of_le {m : ℕ}
    (G : ComposableArrows (Core (ComposableArrows D m)) n)
    (s t : Fin (n + 1)) (h : s ≤ t) :
    rowTransport G s t = (G.map (homOfLE h)).iso := by
  have hh : G.map (homOfLE (Fin.zero_le t)) =
      G.map (homOfLE (Fin.zero_le s)) ≫ G.map (homOfLE h) := G.map_comp _ _
  simp [rowTransport, hh]

/-- Row transport commutes with every ordinal restriction, even when zero is not preserved. -/
theorem rowTransport_precomp {m : ℕ} {p q : SimplexCategory}
    (G : ComposableArrows (Core (ComposableArrows D m)) q.len) (α : p ⟶ q)
    (s t : Fin (p.len + 1)) :
    rowTransport ((SimplexCategory.toCat.map α).toFunctor ⋙ G) s t =
      rowTransport G (α.toOrderHom s) (α.toOrderHom t) := by
  rcases le_total s t with h | h
  · rw [rowTransport_of_le _ _ _ h,
      rowTransport_of_le _ _ _ (α.toOrderHom.monotone h)]
    rfl
  · have hh := rowTransport_of_le
      ((SimplexCategory.toCat.map α).toFunctor ⋙ G) t s h
    have hh' := rowTransport_of_le G (α.toOrderHom t) (α.toOrderHom s)
      (α.toOrderHom.monotone h)
    have hi : rowTransport ((SimplexCategory.toCat.map α).toFunctor ⋙ G) t s =
        rowTransport G (α.toOrderHom t) (α.toOrderHom s) := hh.trans hh'.symm
    have hinv := congrArg Iso.symm hi
    simpa [rowTransport] using hinv

/-- Horizontal restriction of chain rows preserves their coherent isomorphisms. -/
theorem rowTransport_reindex {p q : SimplexCategory}
    (G : ComposableArrows (Core (ComposableArrows D q.len)) n) (α : p ⟶ q)
    (s t : Fin (n + 1)) :
    rowTransport (G ⋙ chainCoreReindex D α) s t =
      Functor.isoWhiskerLeft (SimplexCategory.toCat.map α).toFunctor
        (rowTransport G s t) := rfl

/-- Each actual chain row is naturally isomorphic to its diagonal evaluation. -/
def rowToDiagonal (G : ComposableArrows (Core (ComposableArrows D n)) n)
    (t : Fin (n + 1)) : (G.obj t).of ≅ evaluationSimplex G :=
  NatIso.ofComponents (fun i ↦ (rowTransport G t i).app i) (by
    intro i j f
    have ht : rowTransport G t i ≪≫ (G.map f).iso = rowTransport G t j := by
      have hf : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
      have h := rowTransport_trans G t i j
      rw [rowTransport_of_le G i j (leOfHom f), hf] at h
      exact h
    have h := congrArg (fun e ↦ e.hom.app i) ht
    change (rowTransport G t i).hom.app i ≫ (G.map f).iso.hom.app i = _ at h
    change (G.obj t).of.map f ≫ (rowTransport G t j).hom.app j =
      (rowTransport G t i).hom.app i ≫ ((G.map f).iso.hom.app i ≫ (G.obj j).of.map f)
    rw [← Category.assoc, h]
    exact (rowTransport G t j).hom.naturality f)

/-- The row-to-diagonal isomorphisms form a natural transformation in the outer direction. -/
theorem rowToDiagonal_transition (G : ComposableArrows (Core (ComposableArrows D n)) n)
    {s t : Fin (n + 1)} (f : s ⟶ t) :
    (G.map f).iso ≪≫ rowToDiagonal G t = rowToDiagonal G s := by
  apply Iso.ext
  ext i
  change (G.map f).iso.hom.app i ≫ (rowTransport G t i).hom.app i =
    (rowTransport G s i).hom.app i
  have ht := congrArg (fun e ↦ e.hom.app i) (rowTransport_trans G s t i)
  rw [rowTransport_of_le G s t (leOfHom f)] at ht
  exact ht

/-- All face and degeneracy restrictions preserve the actual diagonal-row isomorphism. -/
theorem rowToDiagonal_reindex {p q : SimplexCategory}
    (G : ComposableArrows (Core (ComposableArrows D q.len)) q.len) (α : p ⟶ q)
    (t : Fin (p.len + 1)) :
    rowToDiagonal ((SimplexCategory.toCat.map α).toFunctor ⋙ G ⋙ chainCoreReindex D α) t =
      Functor.isoWhiskerLeft (SimplexCategory.toCat.map α).toFunctor
        (rowToDiagonal G (α.toOrderHom t)) := by
  apply Iso.ext
  ext i
  change (rowTransport ((SimplexCategory.toCat.map α).toFunctor ⋙ G ⋙
    chainCoreReindex D α) t i).hom.app i = _
  change (rowTransport (((SimplexCategory.toCat.map α).toFunctor ⋙ G) ⋙
    chainCoreReindex D α) t i).hom.app i =
      (rowTransport G (α.toOrderHom t) (α.toOrderHom i)).hom.app (α.toOrderHom i)
  have h := rowTransport_precomp G α t i
  exact congrArg (fun e ↦ e.hom.app (α.toOrderHom i)) h

/-- Coherent transport in a vertically constant chain is the identity. -/
@[simp] theorem rowTransport_constant (F : ComposableArrows D n)
    (s t : Fin (n + 1)) :
    rowTransport ((Functor.const (Fin (n + 1))).obj (Core.mk F)) s t = Iso.refl F := by
  simp [rowTransport]

/-- The row-to-diagonal isomorphism of a constant chain is the strict evaluation equality. -/
theorem rowToDiagonal_constant (F : ComposableArrows D n) (t : Fin (n + 1)) :
    rowToDiagonal ((Functor.const (Fin (n + 1))).obj (Core.mk F)) t =
      eqToIso (evaluationSimplex_constant F).symm := by
  apply Iso.ext
  ext i
  simp [rowToDiagonal]

end SSet.ChainCore
