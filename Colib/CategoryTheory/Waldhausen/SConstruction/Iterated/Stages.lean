/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Category

/-!
# All finite iterated S-cylinders and their original zero tracks

Each stage has the actual row-insertion simplicial cylinder. Induction proves both faces
are the chosen next-stage vertex and proves that the whole chosen-zero track is constant.
The original cylinder and its exact naturality are retained at every finite stage.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/Stages.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, assumptions,
chosen zero objects and universe parameters are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite MonoidalCategory SSet
open scoped Simplicial
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory

/-- Every genuine simplicial invariant has the canonical row-insertion cylinder. -/
def prolongCylinder (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    (W : WideSubcategory preservesZero.{u}) :
    H.obj W ⊗ Δ[1] ⟶ (prolong H).obj W where
  app n := ↾fun z ↦ (H.map ((insertion z.2.down).app W)).app n z.1
  naturality n m α := by
    ext z : 3
    change (H.map ((insertion (α.unop ≫ z.2.down)).app W)).app m ((H.obj W).map α z.1) =
      ((H.obj ((rows m.unop).obj W)).map α)
        ((H.map ((rowsReindex α.unop).app W)).app n
          ((H.map ((insertion z.2.down).app W)).app n z.1))
    rw [insertion_reindex, H.map_comp]
    exact ConcreteCategory.congr_hom
      ((H.map ((insertion z.2.down).app W) ≫ H.map ((rowsReindex α.unop).app W)).naturality α) z.1

/-- The concrete structure cylinder exists between every finite iterated S-stage. -/
def stageCylinder (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    (stages r).obj W ⊗ Δ[1] ⟶ (stages (r + 1)).obj W :=
  prolongCylinder (stages r) W

lemma prolongCylinder_naturality (H : WideSubcategory preservesZero.{u} ⥤ SSet.{u})
    {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    (H.map F ▷ Δ[1]) ≫ prolongCylinder H W =
      prolongCylinder H V ≫ (prolong H).map F := by
  ext n z : 4
  change (H.map ((insertion z.2.down).app W)).app n ((H.map F).app n z.1) =
    (H.map ((rows n.unop).map F)).app n ((H.map ((insertion z.2.down).app V)).app n z.1)
  have e := congrArg H.map ((insertion z.2.down).naturality F)
  rw [H.map_comp, H.map_comp] at e
  exact ConcreteCategory.congr_hom (congrArg (fun η : H.obj V ⟶ H.obj ((rows n.unop).obj W) ↦
    η.app n) e) z.1

/-- All stages and all their original cylinder maps are functorial. -/
lemma stageCylinder_naturality (r : ℕ) {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    ((stages r).map F ▷ Δ[1]) ≫ stageCylinder r W =
      stageCylinder r V ≫ (stages (r + 1)).map F :=
  prolongCylinder_naturality (stages r) F

/-- The initial stage is literally the previously defined original S-space. -/
lemma stages_zero (W : WideSubcategory preservesZero.{u}) :
    (stages 0).obj W = sSet W.obj.waldhausen.cof W.obj.waldhausen.weq := rfl

/-- The second stage is the previously constructed genuine double-S model. -/
def stagesOneIso (W : WideSubcategory preservesZero.{u}) :
    (stages 1).obj W ≅ doubleDiagonal W.obj.waldhausen :=
  Iso.refl _

lemma stageCylinder_zero (W : WideSubcategory preservesZero.{u}) :
    stageCylinder 0 W ≫ (stagesOneIso W).hom = suspensionCylinder W.obj.waldhausen := by
  ext n z : 4
  rfl

end CategoryTheory.Waldhausen.IteratedS

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite MonoidalCategory SSet
open scoped Simplicial
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory

/-- The actual constant-zero exact functor, retaining its original zero image. -/
def zeroHom (V W : WideSubcategory preservesZero.{u}) : V ⟶ W where
  hom := {
    toFunctor := (Functor.const V.obj.Obj).obj W.obj.waldhausen.zero
    isExact := {
      zero _ := W.obj.waldhausen.isZero
      cofibration _ _ := W.obj.waldhausen.cof.id_mem _
      weak _ _ := W.obj.waldhausen.weq.id_mem _
      pushout _ _ := IsPushout.id_horiz (𝟙 W.obj.waldhausen.zero) } }
  property := rfl

lemma rows_map_zeroHom (V W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) :
    (rows n).map (zeroHom V W) = zeroHom ((rows n).obj V) ((rows n).obj W) := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ ObjectProperty.FullSubcategory.ext rfl) ?_
  intro A B f
  apply ObjectProperty.hom_ext
  ext p
  exact W.obj.waldhausen.isZero.eq_of_src _ _

lemma insertion_const (W : WideSubcategory preservesZero.{u}) (n : SimplexCategory) (c : Fin 2) :
    (insertion (SimplexCategory.const n ⦋1⦌ c)).app W = zeroHom W ((rows n).obj W) := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  exact suspensionRow_const W.obj.waldhausen n c

/-- The canonical vertex at every actual finite iterated S-stage. -/
def stageVertex (r : ℕ) :
    (W : WideSubcategory preservesZero.{u}) → ((stages r).obj W).obj (op ⦋0⦌) :=
  Nat.rec (fun W ↦ zeroSimplex W.obj.waldhausen.cof W.obj.waldhausen.weq
      W.obj.waldhausen.zero W.obj.waldhausen.isZero (op ⦋0⦌))
    (fun _ previous W ↦ previous ((rows ⦋0⦌).obj W)) r

lemma stageVertex_naturality (r : ℕ) {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) :
    ((stages r).map F).app (op ⦋0⦌) (stageVertex r V) = stageVertex r W := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun _ ↦ F.property) ?_
    intro p q f
    exact (F.hom.isExact.zero V.obj.waldhausen.isZero).eq_of_src _ _
  | succ r ih => exact ih ((rows ⦋0⦌).map F)

/-- Each constructed stage sends an original zero functor to its literal constant vertex map. -/
lemma stages_map_zeroHom (r : ℕ) (V W : WideSubcategory preservesZero.{u}) :
    (stages r).map (zeroHom V W) = SSet.const (stageVertex r W) := by
  induction r generalizing V W with
  | zero =>
    ext n A : 4
    apply Subtype.ext
    rfl
  | succ r ih =>
    ext n A : 4
    change ((stages r).map ((rows n.unop).map (zeroHom V W))).app n A =
      ((stages r).obj ((rows n.unop).obj W)).map (n.unop.const ⦋0⦌ 0).op
        (((stages r).map ((rowsReindex (n.unop.const ⦋0⦌ 0)).app W)).app (op ⦋0⦌)
          (stageVertex r ((rows ⦋0⦌).obj W)))
    rw [rows_map_zeroHom, ih, stageVertex_naturality]
    rfl

/-- Both faces of every actual stage cylinder are the chosen constant map. -/
lemma stageCylinder_endpoint (r : ℕ) (W : WideSubcategory preservesZero.{u}) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj W).obj n) (c : Fin 2) :
    (stageCylinder r W).app n (A, ⟨SimplexCategory.const n.unop ⦋1⦌ c⟩) =
      (SSet.const (X := (stages r).obj W) (stageVertex (r+1) W)).app n A := by
  change ((stages r).map ((insertion (n.unop.const ⦋1⦌ c)).app W)).app n A =
    ((stages r).obj ((rows n.unop).obj W)).map (n.unop.const ⦋0⦌ 0).op
      (((stages r).map ((rowsReindex (n.unop.const ⦋0⦌ 0)).app W)).app (op ⦋0⦌)
        (stageVertex r ((rows ⦋0⦌).obj W)))
  rw [insertion_const]
  erw [stages_map_zeroHom]
  rw [stageVertex_naturality]
  rfl

lemma stageCylinder_fixed_vertex (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    SSet.yonedaEquiv.symm (stageVertex r W) ▷ Δ[1] ≫ stageCylinder r W =
      CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (stageVertex (r+1) W) := by
  ext n z : 4
  change ((stages r).map ((insertion z.2.down).app W)).app n
      (((stages r).obj W).map z.1.down.op (stageVertex r W)) =
    ((stages r).obj ((rows n.unop).obj W)).map z.1.down.op
      (((stages r).map ((rowsReindex z.1.down).app W)).app (op ⦋0⦌)
        (stageVertex r ((rows ⦋0⦌).obj W)))
  have h := ConcreteCategory.congr_hom
    (((stages r).map ((insertion z.2.down).app W)).naturality z.1.down.op) (stageVertex r W)
  change ((stages r).map ((insertion z.2.down).app W)).app n
      (((stages r).obj W).map z.1.down.op (stageVertex r W)) =
    ((stages r).obj ((rows n.unop).obj W)).map z.1.down.op
      (((stages r).map ((insertion z.2.down).app W)).app (op ⦋0⦌) (stageVertex r W)) at h
  exact h.trans (congrArg (((stages r).obj ((rows n.unop).obj W)).map z.1.down.op)
    ((stageVertex_naturality r ((insertion z.2.down).app W)).trans
      (stageVertex_naturality r ((rowsReindex z.1.down).app W)).symm))

end CategoryTheory.Waldhausen.IteratedS
