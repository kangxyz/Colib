/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicTopology.SimplicialSet.ChainCoreNerve
public import Colib.Topology.Realization.HomotopyBridge
public import Mathlib.Topology.Homotopy.Equiv

/-! # Deformation of the native chain-core diagonal onto the ordinary nerve

Each actual chain row is moved to its diagonal evaluation through its coherent
natural isomorphism. This constructs the contraction directly on the diagonal
of the native chain-core nerve, with no additional rectangular model.

Adapted from `Quillen/Topology/Realization/ClassificationHomotopy.lean` at
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the evaluation
map and deformation endpoints on the native objects.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u v

namespace SSet.ChainCore

variable {D : Type u} [Category.{v} D] {n : ℕ}

/-- An interval parameter selects the original chain row or its evaluated diagonal. -/
def selectedRow (G : ComposableArrows (Core (ComposableArrows D n)) n)
    (ψ : Fin (n + 1) → Fin 2) (t : Fin (n + 1)) : Core (ComposableArrows D n) :=
  if ψ t = 0 then G.obj t else Core.mk (evaluationSimplex G)

/-- The selected row is connected to the original by the actual row-to-diagonal isomorphism. -/
def selectedRowIso (G : ComposableArrows (Core (ComposableArrows D n)) n)
    (ψ : Fin (n + 1) → Fin 2) (t : Fin (n + 1)) : G.obj t ≅ selectedRow G ψ t :=
  if h : ψ t = 0 then eqToIso (by simp [selectedRow, h])
  else Core.isoMk (y := Core.mk (evaluationSimplex G)) (rowToDiagonal G t) ≪≫
    eqToIso (by simp [selectedRow, h])

/-- Conjugate the original outer chain by the selected actual row isomorphisms. -/
def cylinderSimplex (G : ComposableArrows (Core (ComposableArrows D n)) n)
    (ψ : Fin (n + 1) → Fin 2) : ComposableArrows (Core (ComposableArrows D n)) n where
  obj := selectedRow G ψ
  map {s t} f := (selectedRowIso G ψ s).inv ≫ G.map f ≫ (selectedRowIso G ψ t).hom
  map_id _ := by simp
  map_comp f g := by simp [Category.assoc]

/-- At interval zero the original chain is unchanged. -/
@[simp] theorem cylinderSimplex_zero
    (G : ComposableArrows (Core (ComposableArrows D n)) n) :
    cylinderSimplex G (fun _ ↦ 0) = G := by
  refine CategoryTheory.Functor.ext (F := cylinderSimplex G (fun _ ↦ 0)) (G := G)
    (fun _ ↦ rfl) ?_
  intro s t f
  simp [cylinderSimplex, selectedRowIso, selectedRow]

/-- At interval one every row is the diagonal chain and every outer arrow is the identity. -/
@[simp] theorem cylinderSimplex_one
    (G : ComposableArrows (Core (ComposableArrows D n)) n) :
    cylinderSimplex G (fun _ ↦ 1) =
      (Functor.const (Fin (n + 1))).obj (Core.mk (evaluationSimplex G)) := by
  refine CategoryTheory.Functor.ext (F := cylinderSimplex G (fun _ ↦ 1))
    (G := (Functor.const (Fin (n + 1))).obj (Core.mk (evaluationSimplex G)))
    (fun _ ↦ rfl) ?_
  intro s t f
  apply Core.hom_ext
  simp only [cylinderSimplex, selectedRowIso, show (1 : Fin 2) ≠ 0 by decide,
    selectedRow, eqToIso_refl, Iso.trans_refl, eqToHom_refl, Category.id_comp,
    Category.comp_id, Functor.const_obj_map, coreCategory_comp_iso, Iso.trans_hom]
  change (rowToDiagonal G s).inv ≫ (G.map f).iso.hom ≫ (rowToDiagonal G t).hom = 𝟙 _
  have h := congrArg Iso.hom (rowToDiagonal_transition G f)
  change (G.map f).iso.hom ≫ (rowToDiagonal G t).hom = _ at h
  rw [h]
  simp

private theorem selectedRow_reindex {p q : SimplexCategory}
    (G : ComposableArrows (Core (ComposableArrows D q.len)) q.len) (α : p ⟶ q)
    (ψ : Fin (q.len + 1) → Fin 2) (t : Fin (p.len + 1)) :
    selectedRow ((SimplexCategory.toCat.map α).toFunctor ⋙ G ⋙ chainCoreReindex D α)
        (ψ ∘ α.toOrderHom) t =
      (chainCoreReindex D α).obj (selectedRow G ψ (α.toOrderHom t)) := by
  change (if ψ (α.toOrderHom t) = 0 then _ else _) =
    (chainCoreReindex D α).obj (if ψ (α.toOrderHom t) = 0 then _ else _)
  split_ifs <;> rfl

private theorem eqToIso_heq_refl {C : Type*} [Category C] {X Y : C} (h : X = Y) :
    HEq (eqToIso h) (Iso.refl X) := by subst Y; rfl

private theorem iso_trans_eqToIso_heq {C : Type*} [Category C] {X Y Z : C}
    (e : X ≅ Y) (h : Y = Z) : HEq (e ≪≫ eqToIso h) e := by subst Z; simp

private theorem mapIso_eqToIso_heq {C E : Type*} [Category C] [Category E]
    (F : C ⥤ E) {X Y : C} (h : X = Y) :
    HEq (F.mapIso (eqToIso h)) (Iso.refl (F.obj X)) := by subst Y; simp

private theorem mapIso_trans_eqToIso_heq {C E : Type*} [Category C] [Category E]
    (F : C ⥤ E) {X Y Z : C} (e : X ≅ Y) (h : Y = Z) :
    HEq (F.mapIso (e ≪≫ eqToIso h)) (F.mapIso e) := by subst Z; simp

private theorem selectedRowIso_reindex {p q : SimplexCategory}
    (G : ComposableArrows (Core (ComposableArrows D q.len)) q.len) (α : p ⟶ q)
    (ψ : Fin (q.len + 1) → Fin 2) (t : Fin (p.len + 1)) :
    HEq (selectedRowIso ((SimplexCategory.toCat.map α).toFunctor ⋙ G ⋙
      chainCoreReindex D α) (ψ ∘ α.toOrderHom) t)
      ((chainCoreReindex D α).mapIso (selectedRowIso G ψ (α.toOrderHom t))) := by
  by_cases h : ψ (α.toOrderHom t) = 0
  · simp only [selectedRowIso, Function.comp_apply, h, dite_true]
    exact (eqToIso_heq_refl _).trans (mapIso_eqToIso_heq (chainCoreReindex D α) _).symm
  · simp only [selectedRowIso, Function.comp_apply, h, dite_false]
    refine (iso_trans_eqToIso_heq _ _).trans (HEq.trans ?_
      (mapIso_trans_eqToIso_heq _ _ _).symm)
    apply heq_of_eq
    apply Iso.ext
    apply Core.hom_ext
    ext i
    exact congrArg (fun e ↦ e.hom.app i) (rowToDiagonal_reindex G α t)

private theorem conjugate_heq {C : Type*} [Category C]
    {X Y X₁ Y₁ X₂ Y₂ : C} (e₁ : X ≅ X₁) (f₁ : Y ≅ Y₁)
    (e₂ : X ≅ X₂) (f₂ : Y ≅ Y₂) (g : X ⟶ Y)
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (he : HEq e₁ e₂) (hf : HEq f₁ f₂) :
    HEq (e₁.inv ≫ g ≫ f₁.hom) (e₂.inv ≫ g ≫ f₂.hom) := by
  subst X₂
  subst Y₂
  cases eq_of_heq he
  cases eq_of_heq hf
  rfl

/-- The contraction is compatible with simultaneous restriction in both simplicial directions. -/
theorem cylinderSimplex_reindex {p q : SimplexCategory}
    (G : ComposableArrows (Core (ComposableArrows D q.len)) q.len) (α : p ⟶ q)
    (ψ : Fin (q.len + 1) → Fin 2) :
    cylinderSimplex ((SimplexCategory.toCat.map α).toFunctor ⋙ G ⋙ chainCoreReindex D α)
        (ψ ∘ α.toOrderHom) =
      (SimplexCategory.toCat.map α).toFunctor ⋙ cylinderSimplex G ψ ⋙ chainCoreReindex D α := by
  apply CategoryTheory.Functor.hext
  · exact selectedRow_reindex G α ψ
  · intro s t f
    change HEq (_ ≫ _ ≫ _) ((chainCoreReindex D α).map (_ ≫ _ ≫ _))
    rw [Functor.map_comp, Functor.map_comp]
    exact conjugate_heq _ _ _ _ _ (selectedRow_reindex G α ψ s)
      (selectedRow_reindex G α ψ t) (selectedRowIso_reindex G α ψ s)
      (selectedRowIso_reindex G α ψ t)

/-- The genuine simplicial cylinder on the native chain-core diagonal. -/
def cylinder (D : Type u) [Category.{v} D] :
    diagonalSSet (chainCoreNerve D) ⊗ Δ[1] ⟶ diagonalSSet (chainCoreNerve D) where
  app _ := ↾fun z ↦ cylinderSimplex z.1 z.2.down.toOrderHom
  naturality n m α := by
    ext z
    exact cylinderSimplex_reindex z.1 α.unop z.2.down.toOrderHom

@[simp] theorem cylinder_zero (D : Type u) [Category.{v} D] :
    SSet.ι₀ ≫ cylinder D = 𝟙 (diagonalSSet (chainCoreNerve D)) := by
  ext n G
  exact cylinderSimplex_zero G

@[simp] theorem cylinder_one (D : Type u) [Category.{v} D] :
    SSet.ι₁ ≫ cylinder D = evaluation D ≫ constant D := by
  ext n G
  exact cylinderSimplex_one G

/-- A simplicial deformation onto the ordinary nerve, retaining exact diagonal evaluation. -/
def homotopy (D : Type u) [Category.{v} D] :
    SSet.Homotopy (𝟙 (diagonalSSet (chainCoreNerve D))) (evaluation D ≫ constant D) where
  h := cylinder D
  h₀ := cylinder_zero D
  h₁ := cylinder_one D
  rel := by ext n z; exact z.1.property.elim

/-- Diagonal evaluation is an actual realization homotopy equivalence. -/
def realizationHomotopyEquiv (D : Type u) [Category.{v} D] :
    ContinuousMap.HomotopyEquiv |diagonalSSet (chainCoreNerve D)| |nerve D| where
  toFun := (SSet.toTop.map (evaluation D)).hom
  invFun := (SSet.toTop.map (constant D)).hom
  left_inv := by
    have h := (realizationSimplicialHomotopy (homotopy D)).symm
    exact ⟨by simpa only [SSet.toTop.map_id, SSet.toTop.map_comp,
      TopCat.hom_id, TopCat.hom_comp] using h⟩
  right_inv := by
    have h := congrArg (fun f ↦ (SSet.toTop.map f).hom) (constant_evaluation D)
    have he : (SSet.toTop.map (evaluation D)).hom.comp
        (SSet.toTop.map (constant D)).hom = ContinuousMap.id _ := by
      simpa only [SSet.toTop.map_comp, SSet.toTop.map_id, TopCat.hom_comp, TopCat.hom_id] using h
    rw [he]

@[simp] theorem realizationHomotopyEquiv_toFun (D : Type u) [Category.{v} D] :
    (realizationHomotopyEquiv D).toFun = (SSet.toTop.map (evaluation D)).hom := rfl

private theorem coreIsoMk_eqToIso_heq {C : Type*} [Category C] {X Y : C} (h : X = Y) :
    HEq (Core.isoMk (x := Core.mk X) (y := Core.mk Y) (eqToIso h))
      (Iso.refl (Core.mk X)) := by subst Y; rfl

private theorem selectedRow_constant (F : ComposableArrows D n)
    (ψ : Fin (n + 1) → Fin 2) (t : Fin (n + 1)) :
    selectedRow ((Functor.const (Fin (n + 1))).obj (Core.mk F)) ψ t = Core.mk F := by
  simp [selectedRow]

private theorem selectedRowIso_constant (F : ComposableArrows D n)
    (ψ : Fin (n + 1) → Fin 2) (t : Fin (n + 1)) :
    HEq (selectedRowIso ((Functor.const (Fin (n + 1))).obj (Core.mk F)) ψ t)
      (Iso.refl (Core.mk F)) := by
  by_cases h : ψ t = 0
  · simp only [selectedRowIso, h, dite_true]
    exact eqToIso_heq_refl _
  · simp only [selectedRowIso, h, dite_false]
    refine (iso_trans_eqToIso_heq _ _).trans ?_
    rw [rowToDiagonal_constant]
    exact coreIsoMk_eqToIso_heq _

/-- The cylinder fixes every native chain already constant in the outer direction. -/
@[simp] theorem cylinderSimplex_constant (F : ComposableArrows D n)
    (ψ : Fin (n + 1) → Fin 2) :
    cylinderSimplex ((Functor.const (Fin (n + 1))).obj (Core.mk F)) ψ =
      (Functor.const (Fin (n + 1))).obj (Core.mk F) := by
  apply CategoryTheory.Functor.hext
  · exact selectedRow_constant F ψ
  · intro s t f
    have h := conjugate_heq _ _ (Iso.refl (Core.mk F)) (Iso.refl (Core.mk F))
      (𝟙 (Core.mk F)) (selectedRow_constant F ψ s) (selectedRow_constant F ψ t)
      (selectedRowIso_constant F ψ s) (selectedRowIso_constant F ψ t)
    simpa [cylinderSimplex] using h

/-- The simplicial deformation fixes the entire vertically constant nerve image. -/
@[simp] theorem constant_cylinder (D : Type u) [Category.{v} D] :
    (constant D ▷ Δ[1]) ≫ cylinder D = fst (nerve D) Δ[1] ≫ constant D := by
  ext n z
  exact cylinderSimplex_constant z.1 _

/-- The realized homotopy fixes each chosen vertex in the constant-nerve image. -/
theorem realizationHomotopy_fixed_vertex (D : Type u) [Category.{v} D]
    (x : (nerve D) _⦋0⦌) (t : unitInterval) :
    realizationSimplicialHomotopy (homotopy D)
      (t, realizationPoint ((constant D).app _ x)) =
        realizationPoint ((constant D).app _ x) := by
  apply realizationSimplicialHomotopy_fixed_vertex (homotopy D)
    ((constant D).app _ x) ((constant D).app _ x) _ t
  change SSet.yonedaEquiv.symm ((constant D).app _ x) ▷ Δ[1] ≫ cylinder D = _
  rw [← SSet.yonedaEquiv_symm_comp]
  rw [comp_whiskerRight, Category.assoc, constant_cylinder,
    ← Category.assoc, whiskerRight_fst, Category.assoc]

end SSet.ChainCore
