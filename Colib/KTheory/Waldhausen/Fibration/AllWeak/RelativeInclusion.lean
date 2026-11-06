/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.AllWeak.AcyclicInclusion
public import Colib.KTheory.Waldhausen.Fibration.AllWeak.OrdinaryRows
public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.CoarseEvaluation

/-! # The original acyclic-to-relative diagram

Apply the original acyclic inclusion to every component of an all-weak
relative row in the actual acyclic category. Its categorical exactness and
original tail/fiber squares require no saturation. Only the coarse
realization square uses the genuinely proved all-weak-source coarse
exactness and its two-out-of-three hypothesis.


Implementation provenance:
`Quillen/Waldhausen/Fibration/AllWeak/RelativeInclusion.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.AllWeak
section Categorical
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The unchanged acyclic inclusion acts on every original one-longer row. -/
def relativeInclusion (n : SimplexCategory) :
    RelativeRows.Obj (nested (acyclicStructure N)) n ⥤ RelativeRows.Obj N n where
  obj X := ⟨(QuotientRows.postcompose (acyclicStructure N) V
    (Fibration.acyclicInclusion_exact N) (RelativeRows.addInitial.obj n)).obj X.obj,
      fun p ↦ (X.obj.obj.obj ((QuotientRows.indexMap (RelativeRows.tail.app n)).obj p)).property⟩
  map f := (RelativeRows.objects N n).homMk
    ((QuotientRows.postcompose (acyclicStructure N) V
      (Fibration.acyclicInclusion_exact N) (RelativeRows.addInitial.obj n)).map f.hom)
  map_id _ := by apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; ext p; rfl
  map_comp _ _ := by apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; ext p; rfl

/-- Forgetting the relative predicate retains exactly original row postcomposition. -/
@[simp] theorem relativeInclusion_forget (n : SimplexCategory) :
    relativeInclusion N n ⋙ RelativeRows.forget N n =
      RelativeRows.forget (nested (acyclicStructure N)) n ⋙
        QuotientRows.postcompose (acyclicStructure N) V
          (Fibration.acyclicInclusion_exact N) (RelativeRows.addInitial.obj n) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual relative functor is exact for the original inherited fine weak classes. -/
theorem relativeInclusion_exact (n : SimplexCategory) :
    IsExact (RelativeRows.waldhausenStructure (nested (acyclicStructure N)) n).cof
      (RelativeRows.waldhausenStructure (nested (acyclicStructure N)) n).weq
      (RelativeRows.waldhausenStructure N n).cof (RelativeRows.waldhausenStructure N n).weq
      (relativeInclusion N n) where
  zero h := IsZero.of_full_of_faithful_of_isZero (RelativeRows.forget N n) _
    (((RelativeRows.forget_exact (nested (acyclicStructure N)) n).comp
      (QuotientRows.postcompose_exact (acyclicStructure N) V
        (Fibration.acyclicInclusion_exact N) (RelativeRows.addInitial.obj n))).zero h)
  cofibration _f hf := QuotientRows.postcompose_cof (acyclicStructure N) V
    (Fibration.acyclicInclusion_exact N) hf
  weak _f hf := hf
  pushout hf h := IsPushout.of_map_of_faithful (RelativeRows.forget N n)
    ((QuotientRows.postcompose_exact (acyclicStructure N) V
      (Fibration.acyclicInclusion_exact N) (RelativeRows.addInitial.obj n)).pushout hf
        (RelativeRows.forget_map_pushout (nested (acyclicStructure N)) hf h))

@[simp] theorem relativeInclusion_component (n : SimplexCategory)
    (X : RelativeRows.Obj (nested (acyclicStructure N)) n)
    (p : Interval (RelativeRows.addInitial.obj n)) :
    (((relativeInclusion N n).obj X).obj.obj.obj p) = (X.obj.obj.obj p).obj := rfl

@[simp] theorem relativeInclusion_map_component {n : SimplexCategory}
    {X Y : RelativeRows.Obj (nested (acyclicStructure N)) n} (f : X ⟶ Y)
    (p : Interval (RelativeRows.addInitial.obj n)) :
    (((relativeInclusion N n).map f).hom.hom.app p) = (f.hom.hom.app p).hom := rfl

/-- Every original ordinal restriction commutes strictly with the same inclusion. -/
@[simp] theorem relativeInclusion_reindex {m n : SimplexCategory} (α : m ⟶ n) :
    relativeInclusion N n ⋙ RelativeRows.reindex N α =
      RelativeRows.reindex (nested (acyclicStructure N)) α ⋙ relativeInclusion N m := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual inherited zero row is retained literally. -/
@[simp] theorem relativeInclusion_zero (n : SimplexCategory) :
    (relativeInclusion N n).obj (RelativeRows.zero (nested (acyclicStructure N)) n) =
      RelativeRows.zero N n := by
  apply ObjectProperty.FullSubcategory.ext
  apply ObjectProperty.FullSubcategory.ext
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The original tail square, before taking either S-construction. -/
@[simp] theorem relativeInclusion_tail (n : SimplexCategory) :
    relativeInclusion N n ⋙ RelativeRows.tailFunctor N n =
      RelativeRows.tailFunctor (nested (acyclicStructure N)) n ⋙
        QuotientRows.postcompose (acyclicStructure (nested (acyclicStructure N)))
          (acyclicStructure N) (Fibration.acyclicInclusion_exact (nested (acyclicStructure N)))
            n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual three-term zero/object/zero diagram commutes with the original inclusion. -/
theorem oneChain_acyclicInclusion (X : AcyclicCategory N) :
    (QuotientRows.oneChain (acyclicStructure N)).flip.obj X ⋙ Fibration.acyclicInclusion N =
      (QuotientRows.oneChain V).flip.obj X.obj := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · fin_cases i <;> rfl
  · intro i j f
    have hij := leOfHom f
    change i.val ≤ j.val at hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact V.isZero.eq_of_src _ _
      | exact V.isZero.eq_of_tgt _ _
      | omega
      | have hf : f = 𝟙 _ := Subsingleton.elim _ _
        subst f
        simp

/-- The one-row functors retain the original inclusion strictly. -/
theorem oneEmbedding_acyclicInclusion :
    QuotientRows.oneEmbedding (acyclicStructure N) ⋙
      QuotientRows.postcompose (acyclicStructure N) V (Fibration.acyclicInclusion_exact N) ⦋1⦌ =
        Fibration.acyclicInclusion N ⋙ QuotientRows.oneEmbedding V := by
  refine CategoryTheory.Functor.ext (fun X ↦ ?_) ?_
  · apply ObjectProperty.FullSubcategory.ext
    exact congrArg (fun F ↦ QuotientRows.oneIndex ⋙ F) (oneChain_acyclicInclusion N X)
  · intro X Y f
    apply ObjectProperty.hom_ext
    ext p
    have eqToHom_hom {A B : QuotientRows.Obj V ⦋1⦌} (h : A = B) :
        (eqToHom h).hom = eqToHom (congrArg (fun Z ↦ Z.obj) h) := by subst B; rfl
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      eqToHom_hom, eqToHom_app]
    rcases p with ⟨⟨i,j⟩, hij⟩
    fin_cases i <;> fin_cases j <;>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] <;> rfl

/-- The original split-fiber square retains the original acyclic inclusion. -/
@[simp] theorem fiber_relativeInclusion (n : SimplexCategory) :
    RelativeRows.fiber (nested (acyclicStructure N)) n ⋙ relativeInclusion N n =
      Fibration.acyclicInclusion N ⋙ RelativeRows.fiber N n := by
  apply RelativeRows.functor_eq_of_comp_forget N
  change QuotientRows.oneEmbedding (acyclicStructure N) ⋙
    (QuotientRows.reindex (acyclicStructure N) (RelativeRows.fiberOrdinal n) ⋙
      QuotientRows.postcompose (acyclicStructure N) V (Fibration.acyclicInclusion_exact N)
        (RelativeRows.addInitial.obj n)) =
      (Fibration.acyclicInclusion N ⋙ QuotientRows.oneEmbedding V) ⋙
        QuotientRows.reindex V (RelativeRows.fiberOrdinal n)
  rw [← QuotientRows.postcompose_reindex, ← CategoryTheory.Functor.assoc,
    oneEmbedding_acyclicInclusion]

end Categorical
section Simplicial
variable {C : Type u} [SmallCategory C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The original relative inclusion in both original S directions. -/
def relativeInclusionSRows :
    RelativeRows.relativeSRows (nested (acyclicStructure N)) ⟶ RelativeRows.relativeSRows N where
  app n := sSetMap (relativeInclusion_exact N n.unop)
  naturality n m α := by
    ext k F : 4
    rfl

/-- The actual tail square uses the actual double-S base identification. -/
@[simp] theorem relativeInclusionSRows_tail :
    relativeInclusionSRows N ≫ RelativeRows.tailSRows N =
      RelativeRows.tailSRows (nested (acyclicStructure N)) ≫ ordinaryRowsInclusion
        (acyclicStructure N) := by
  ext n k F : 5
  rfl

/-- Its literal original diagonal map. -/
def relativeInclusionTotal :
    SSet.diagonalSSet (RelativeRows.relativeSRows (nested (acyclicStructure N))) ⟶
      SSet.diagonalSSet (RelativeRows.relativeSRows N) :=
  SSet.diagonalMap (relativeInclusionSRows N)

/-- The actual all-zero simplex is retained in every diagonal degree. -/
@[simp] theorem relativeInclusionTotal_zeroSimplex (n : SimplexCategory) :
    (relativeInclusionTotal N).app (op n)
      (zeroSimplex (RelativeRows.waldhausenStructure (nested (acyclicStructure N)) n).cof
        (RelativeRows.waldhausenStructure (nested (acyclicStructure N)) n).weq
        (RelativeRows.zero (nested (acyclicStructure N)) n)
        (RelativeRows.isZero (nested (acyclicStructure N)) n) (op n)) =
      zeroSimplex (RelativeRows.waldhausenStructure N n).cof
        (RelativeRows.waldhausenStructure N n).weq (RelativeRows.zero N n)
        (RelativeRows.isZero N n) (op n) := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ relativeInclusion_zero N n) ?_
  intro i j f
  exact ((relativeInclusion_exact N n).zero
    (RelativeRows.isZero (nested (acyclicStructure N)) n)).eq_of_src _ _

/-- Realization preserves the original chosen total basepoint exactly. -/
@[simp] theorem relativeInclusionTotal_basepoint :
    SSet.toTop.map (relativeInclusionTotal N)
      (RelativeRows.totalBasepoint (nested (acyclicStructure N))) = RelativeRows.totalBasepoint
        N := by
  have h := SSet.yonedaEquiv_symm_comp
    (RelativeRows.totalZeroVertex (nested (acyclicStructure N))) (relativeInclusionTotal N)
  have h' := congrArg (fun f : (Δ[0] : SSet.{u}) ⟶
      SSet.diagonalSSet (RelativeRows.relativeSRows N) ↦ SSet.toTop.map f default) h
  simpa only [Functor.map_comp, TopCat.comp_app, RelativeRows.totalZeroVertex,
    relativeInclusionTotal_zeroSimplex, RelativeRows.totalBasepoint] using h'

/-- The original total split-fiber square is a strict equality. -/
@[simp] theorem totalFiberInclusion_relativeInclusion :
    RelativeRows.totalFiberInclusion (nested (acyclicStructure N)) ≫ relativeInclusionTotal N =
      sSetMap (Fibration.acyclicInclusion_exact N) ≫ RelativeRows.totalFiberInclusion N := by
  apply NatTrans.ext
  funext n
  have hs : sSetMap (RelativeRows.fiber_exact (nested (acyclicStructure N)) n.unop) ≫
      sSetMap (relativeInclusion_exact N n.unop) =
        sSetMap (Fibration.acyclicInclusion_exact N) ≫ sSetMap (RelativeRows.fiber_exact N
          n.unop) := by
    rw [sSetMap_comp_sSetMap, sSetMap_comp_sSetMap]
    exact RelativeRows.sSetMap_eq_of_functor_eq _ _ (fiber_relativeInclusion N n.unop)
  exact congrArg (fun f ↦ f.app n) hs

/-- The original coarse-evaluation square, using only the established
structural extension and two-out-of-three inputs. -/
theorem relativeInclusionTotal_coarseEvaluation (he : ExtensionAxiom N.coarse)
    [N.coarse.weq.HasTwoOutOfThreeProperty] :
    relativeInclusionTotal N ≫ RelativeRows.coarseEvaluation N he =
      RelativeRows.coarseEvaluation (nested (acyclicStructure N)) (extensionAxiom
        (acyclicStructure N)) ≫
        sSetMap (AllWeak.acyclicInclusion_exact N) := by
  ext n F : 4
  rfl

end Simplicial
end CategoryTheory.Waldhausen.Fibration.AllWeak
