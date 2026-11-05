/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.AlgebraicTopology.SimplicialSet.Diagonal

/-! # The two independent degrees of the genuine Waldhausen S-construction

The first degree is the S/interval direction and the second is the
weak-equivalence/nerve direction. Their diagonal is the existing actual
Waldhausen simplicial set, with the identical underlying grid functors.
No exact-category or preadditive hypotheses are used.
The zero condition is `IsZero` at diagonal entries, not equality to a chosen zero.

Implementation provenance: adapted from `Quillen/Waldhausen/SConstruction/Bisimplicial.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The zero-simplex comparison is separated into `BisimplicialZero` so that this
module does not depend on realization or K-groups.
Isolated strict compilation is recorded in the accompanying release report.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe v u v' u'

namespace CategoryTheory.Waldhausen

/-- Independent S degree `n` and weak-equivalence degree `m`. -/
def Grid₂ (n m : SimplexCategory) := Fin (m.len + 1) × Interval n

instance (n m : SimplexCategory) : PartialOrder (Grid₂ n m) :=
  inferInstanceAs (PartialOrder (Fin (m.len + 1) × Interval n))

/-- A nerve coordinate and an interval, with independent ordinal bounds. -/
def grid₂ {n m : SimplexCategory} (t : Fin (m.len + 1))
    (i j : Fin (n.len + 1)) (h : i ≤ j) : Grid₂ n m := (t, interval i j h)

/-- Reindex both directions independently. -/
def gridMap₂ {n' n m' m : SimplexCategory} (α : n' ⟶ n) (β : m' ⟶ m) :
    Grid₂ n' m' ⥤ Grid₂ n m :=
  (show Monotone (fun p : Grid₂ n' m' ↦
      (β.toOrderHom p.1,
        interval (α.toOrderHom p.2.1.1) (α.toOrderHom p.2.1.2)
          (α.toOrderHom.monotone p.2.2))) from
    fun _ _ h ↦ ⟨β.toOrderHom.monotone h.1,
      α.toOrderHom.monotone h.2.1, α.toOrderHom.monotone h.2.2⟩).functor

@[simp] theorem gridMap₂_obj_grid₂ {n' n m' m : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m) (t : Fin (m'.len + 1))
    (i j : Fin (n'.len + 1)) (h : i ≤ j) :
    (gridMap₂ α β).obj (grid₂ t i j h) =
      grid₂ (β.toOrderHom t) (α.toOrderHom i) (α.toOrderHom j)
        (α.toOrderHom.monotone h) := rfl

@[simp] theorem gridMap₂_id (n m : SimplexCategory) :
    gridMap₂ (𝟙 n) (𝟙 m) = 𝟭 (Grid₂ n m) := rfl

@[simp] theorem gridMap₂_comp {n₀ n₁ n₂ m₀ m₁ m₂ : SimplexCategory}
    (α : n₀ ⟶ n₁) (α' : n₁ ⟶ n₂) (β : m₀ ⟶ m₁) (β' : m₁ ⟶ m₂) :
    gridMap₂ (α ≫ α') (β ≫ β') = gridMap₂ α β ⋙ gridMap₂ α' β' := rfl

/-- Independent interval and nerve restrictions commute strictly. -/
theorem gridMap₂_interchange {n' n m' m : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m) :
    gridMap₂ α (𝟙 m') ⋙ gridMap₂ (𝟙 n) β =
      gridMap₂ (𝟙 n') β ⋙ gridMap₂ α (𝟙 m) := rfl

/-- On the diagonal the indexing map is literally the original grid map. -/
theorem gridMap₂_diagonal {n' n : SimplexCategory} (α : n' ⟶ n) :
    gridMap₂ α α = gridMap α := rfl

variable {C : Type u} [Category.{v} C]

/-- Genuine quotient diagrams in degree n, with weak maps in independent degree m. -/
structure IsSimplex₂ (cof weq : MorphismProperty C) {n m : SimplexCategory}
    (F : Grid₂ n m ⥤ C) : Prop where
  zero (t i) : IsZero (F.obj (grid₂ t i i le_rfl))
  cofibration (t i j k) (hij : i ≤ j) (hjk : j ≤ k) :
    cof (F.map (homOfLE (show grid₂ t i j hij ≤ grid₂ t i k (hij.trans hjk) from
      ⟨le_rfl, le_rfl, hjk⟩)))
  quotient (t i j k) (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout
      (F.map (homOfLE (show grid₂ t i j hij ≤ grid₂ t i k (hij.trans hjk) from
        ⟨le_rfl, le_rfl, hjk⟩)))
      (F.map (homOfLE (show grid₂ t i j hij ≤ grid₂ t j j le_rfl from
        ⟨le_rfl, hij, le_rfl⟩)))
      (F.map (homOfLE (show grid₂ t i k (hij.trans hjk) ≤ grid₂ t j k hjk from
        ⟨le_rfl, hij, le_rfl⟩)))
      (F.map (homOfLE (show grid₂ t j j le_rfl ≤ grid₂ t j k hjk from
        ⟨le_rfl, le_rfl, hjk⟩)))
  weak (s t i j) (hst : s ≤ t) (hij : i ≤ j) :
    weq (F.map (homOfLE (show grid₂ s i j hij ≤ grid₂ t i j hij from
      ⟨hst, le_rfl, le_rfl⟩)))

variable (cof weq : MorphismProperty C)

/-- Both independently reindexed directions retain all actual simplex conditions. -/
theorem IsSimplex₂.precomp {n' n m' m : SimplexCategory} {F : Grid₂ n m ⥤ C}
    (hF : IsSimplex₂ cof weq F) (α : n' ⟶ n) (β : m' ⟶ m) :
    IsSimplex₂ cof weq (gridMap₂ α β ⋙ F) where
  zero t i := hF.zero (β.toOrderHom t) (α.toOrderHom i)
  cofibration t i j k hij hjk := hF.cofibration (β.toOrderHom t) (α.toOrderHom i)
    (α.toOrderHom j) (α.toOrderHom k)
    (α.toOrderHom.monotone hij) (α.toOrderHom.monotone hjk)
  quotient t i j k hij hjk := hF.quotient (β.toOrderHom t) (α.toOrderHom i)
    (α.toOrderHom j) (α.toOrderHom k)
    (α.toOrderHom.monotone hij) (α.toOrderHom.monotone hjk)
  weak s t i j hst hij := hF.weak (β.toOrderHom s) (β.toOrderHom t)
    (α.toOrderHom i) (α.toOrderHom j)
    (β.toOrderHom.monotone hst) (α.toOrderHom.monotone hij)

/-- The diagonal conditions are exactly the original genuine simplex conditions. -/
theorem isSimplex₂_diagonal_iff {n : SimplexCategory} (F : Grid n ⥤ C) :
    IsSimplex₂ cof weq F ↔ IsSimplex cof weq F :=
  ⟨fun h ↦ ⟨h.zero, h.cofibration, h.quotient, h.weak⟩,
    fun h ↦ ⟨h.zero, h.cofibration, h.quotient, h.weak⟩⟩

/-- The actual bisimplicial set: outer S degree, inner weak-equivalence degree. -/
def bisimplicialSSetOfProperties : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} where
  obj n := {
    obj m := { F : Grid₂ n.unop m.unop ⥤ C // IsSimplex₂ cof weq F }
    map β := ↾fun F ↦ ⟨gridMap₂ (𝟙 n.unop) β.unop ⋙ F.1,
      F.2.precomp cof weq (𝟙 n.unop) β.unop⟩
    map_id _ := by ext F; rfl
    map_comp _ _ := by ext F; rfl }
  map α := {
    app m := ↾fun F ↦ ⟨gridMap₂ α.unop (𝟙 m.unop) ⋙ F.1,
      F.2.precomp cof weq α.unop (𝟙 m.unop)⟩
    naturality _ _ _ := by ext F; rfl }
  map_id _ := by ext m F; rfl
  map_comp _ _ := by ext m F; rfl

@[simp] theorem bisimplicialSSetOfProperties_intervalMap_val
    {n' n : SimplexCategoryᵒᵖ} (α : n ⟶ n') (m : SimplexCategoryᵒᵖ)
    (F : ((bisimplicialSSetOfProperties cof weq).obj n).obj m) :
    (((bisimplicialSSetOfProperties cof weq).map α).app m F).1 =
      gridMap₂ α.unop (𝟙 m.unop) ⋙ F.1 := rfl

@[simp] theorem bisimplicialSSetOfProperties_nerveMap_val
    (n : SimplexCategoryᵒᵖ) {m' m : SimplexCategoryᵒᵖ} (β : m ⟶ m')
    (F : ((bisimplicialSSetOfProperties cof weq).obj n).obj m) :
    (((bisimplicialSSetOfProperties cof weq).obj n).map β F).1 =
      gridMap₂ (𝟙 n.unop) β.unop ⋙ F.1 := rfl

/-- The actual constant zero diagram, in both independent degrees. -/
def zeroSimplex₂ [cof.ContainsIdentities] [weq.ContainsIdentities]
    (Z : C) (hZ : IsZero Z) (n m : SimplexCategoryᵒᵖ) :
    ((bisimplicialSSetOfProperties cof weq).obj n).obj m :=
  ⟨(Functor.const (Grid₂ n.unop m.unop)).obj Z, {
    zero := fun _ _ ↦ hZ
    cofibration := fun _ _ _ _ _ _ ↦ cof.id_mem Z
    quotient := fun _ _ _ _ _ _ ↦ IsPushout.id_horiz (𝟙 Z)
    weak := fun _ _ _ _ _ _ ↦ weq.id_mem Z }⟩

/-- Its diagonal uses precisely the original grid functor, not a replacement model. -/
def bisimplicialDiagonalIsoOfProperties :
    SSet.diagonalSSet (bisimplicialSSetOfProperties cof weq) ≅ sSet cof weq :=
  NatIso.ofComponents (fun n ↦ {
    hom := ↾fun F ↦ ⟨F.1, (isSimplex₂_diagonal_iff cof weq F.1).1 F.2⟩
    inv := ↾fun F ↦ ⟨F.1, (isSimplex₂_diagonal_iff cof weq F.1).2 F.2⟩
    hom_inv_id := by ext F; rfl
    inv_hom_id := by ext F; rfl }) (by intro n m α; ext F; rfl)

@[simp] theorem bisimplicialDiagonalIsoOfProperties_hom_val
    (n : SimplexCategoryᵒᵖ)
    (F : (SSet.diagonalSSet (bisimplicialSSetOfProperties cof weq)).obj n) :
    ((bisimplicialDiagonalIsoOfProperties cof weq).hom.app n F).1 = F.1 := rfl

@[simp] theorem bisimplicialDiagonalIsoOfProperties_inv_val
    (n : SimplexCategoryᵒᵖ) (F : (sSet cof weq).obj n) :
    ((bisimplicialDiagonalIsoOfProperties cof weq).inv.app n F).1 = F.1 := rfl

/-- The bisimplicial S-construction of an arbitrary Waldhausen category. -/
abbrev bisimplicialSSet (V : Structure C) : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  bisimplicialSSetOfProperties V.cof V.weq

/-- Its diagonal is the unchanged actual Waldhausen simplicial set. -/
abbrev bisimplicialDiagonalIso (V : Structure C) :
    SSet.diagonalSSet (bisimplicialSSet V) ≅ sSet V.cof V.weq :=
  bisimplicialDiagonalIsoOfProperties V.cof V.weq

section Postcomposition
variable {D : Type u'} [Category.{v'} D] {cof' weq' : MorphismProperty D}
  {G : C ⥤ D} (hG : IsExact cof weq cof' weq' G)

include hG in
/-- A genuine exact functor acts by actual postcomposition in both degrees. -/
theorem IsSimplex₂.postcomp {n m : SimplexCategory} {F : Grid₂ n m ⥤ C}
    (hF : IsSimplex₂ cof weq F) : IsSimplex₂ cof' weq' (F ⋙ G) where
  zero t i := hG.zero (hF.zero t i)
  cofibration t i j k hij hjk := hG.cofibration _ (hF.cofibration t i j k hij hjk)
  quotient t i j k hij hjk := hG.pushout (hF.cofibration t i j k hij hjk)
    (hF.quotient t i j k hij hjk)
  weak s t i j hst hij := hG.weak _ (hF.weak s t i j hst hij)
end Postcomposition

section SameUniverses
variable {D : Type u} [Category.{v} D] {cof' weq' : MorphismProperty D}
  {G : C ⥤ D} (hG : IsExact cof weq cof' weq' G)

/-- The bisimplicial map of genuine exact functors, literally postcomposition. -/
def bisimplicialSSetMap :
    bisimplicialSSetOfProperties cof weq ⟶ bisimplicialSSetOfProperties cof' weq' where
  app n := {
    app m := ↾fun F ↦ ⟨F.1 ⋙ G, F.2.postcomp cof weq hG⟩
    naturality _ _ _ := by ext F; rfl }
  naturality _ _ _ := by ext m F; rfl

@[simp] theorem bisimplicialSSetMap_app_val (n m : SimplexCategoryᵒᵖ)
    (F : ((bisimplicialSSetOfProperties cof weq).obj n).obj m) :
    (((bisimplicialSSetMap cof weq hG).app n).app m F).1 = F.1 ⋙ G := rfl

/-- The exact diagonal identification retains the already-defined S-map. -/
theorem bisimplicialDiagonalIso_naturality :
    SSet.diagonalMap (bisimplicialSSetMap cof weq hG) ≫
        (bisimplicialDiagonalIsoOfProperties cof' weq').hom =
      (bisimplicialDiagonalIsoOfProperties cof weq).hom ≫ sSetMap hG := by
  ext n F
  rfl
end SameUniverses

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0154",
  colib_ref "Waldhausen1985" "Section 1.3, pp. 328-330" "background"
    "Background for the stated unnormalized IsZero model; not a strict-model identification"]
  CategoryTheory.Waldhausen.bisimplicialDiagonalIsoOfProperties
