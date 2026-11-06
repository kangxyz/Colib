/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.FiltrationRealization
public import Colib.KTheory.Waldhausen.Fibration.MixedNerves.TotalEvaluation
public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.FiberFiltration
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap

/-! # The original relative total S-construction and the coarse S-construction

The actual initial-filtration map is followed by the actual mixed diagonal
evaluation. Its equivalence is proved from the genuine cylinder comparison;
no realization or homotopy-fiber conclusion is assumed as data.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/CoarseEvaluation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse)

/-- The actual original relative grid is evaluated along its initial diagonal intervals. -/
def coarseEvaluation : SSet.diagonalSSet (relativeSRows N) ⟶
    sSet N.coarse.cof N.coarse.weq :=
  relativeFiltrationTotalMap N he ≫ MixedNerves.totalCofEvaluation N

/-- Every object is the original initial interval at the same nerve index. -/
@[simp] theorem coarseEvaluation_obj (n : SimplexCategory)
    (F : (SSet.diagonalSSet (relativeSRows N)).obj (op n))
    (i : Fin (n.len + 1)) (p : Interval n) :
    (((coarseEvaluation N he).app (op n) F).val.obj (i,p)) =
      (F.val.obj (i,p)).obj.obj.obj (interval 0 i.succ (Fin.zero_le _)) := rfl

/-- The original split-fiber inclusion on the actual total diagonal. -/
def totalFiberInclusion : sSet V.cof V.weq ⟶ SSet.diagonalSSet (relativeSRows N) :=
  (CategoryTheory.TheoremA.diagonalConstantIso _).inv ≫ SSet.diagonalMap (fiberSRows N)

/-- The actual relative-to-coarse map is a homotopy equivalence under the proved cylinder
hypotheses. -/
def coarseEvaluationHomotopyEquiv (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D)
    [N.coarse.weq.HasTwoOutOfThreeProperty] :
    ContinuousMap.HomotopyEquiv |SSet.diagonalSSet (relativeSRows N)|
      |sSet N.coarse.cof N.coarse.weq| :=
  (relativeFiltrationTotalHomotopyEquiv N he).trans
    (MixedNerves.totalCofEvaluationHomotopyEquiv N D hs)

/-- The equivalence has the literal original evaluation map as its forward map. -/
@[simp] theorem coarseEvaluationHomotopyEquiv_toFun (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D)
    [N.coarse.weq.HasTwoOutOfThreeProperty] :
    (coarseEvaluationHomotopyEquiv N he D hs).toFun =
      (SSet.toTop.map (coarseEvaluation N he)).hom := by
  change (MixedNerves.totalCofEvaluationHomotopyEquiv N D hs).toFun.comp
    (relativeFiltrationTotalHomotopyEquiv N he).toFun = _
  rw [MixedNerves.totalCofEvaluationHomotopyEquiv_toFun,
    relativeFiltrationTotalHomotopyEquiv_toFun,
    coarseEvaluation, SSet.toTop.map_comp, TopCat.hom_comp]

/-- The canonical split-fiber triangle is an equality of the original simplicial maps. -/
@[simp] theorem totalFiberInclusion_coarseEvaluation :
    totalFiberInclusion N ≫ coarseEvaluation N he = sSetMap (changeWeak_exact N) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro F
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro a b f
  change F.val.map (homOfLE (show a ≤ (a.1,b.2) from ⟨le_rfl,(leOfHom f).2⟩)) ≫
    (𝟙 _ ≫ F.val.map (homOfLE (show (a.1,b.2) ≤ b from ⟨(leOfHom f).1,le_rfl⟩))) =
    𝟙 _ ≫ F.val.map f ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id, ← F.val.map_comp]
  rfl

/-- The original total relative zero simplex maps to the actual coarse chosen zero. -/
@[simp] theorem coarseEvaluation_zeroSimplex (n : SimplexCategory) :
    (coarseEvaluation N he).app (op n)
      (zeroSimplex (waldhausenStructure N n).cof (waldhausenStructure N n).weq
        (zero N n) (isZero N n) (op n)) =
      zeroSimplex N.coarse.cof N.coarse.weq N.coarse.zero N.coarse.isZero (op n) := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ N.zero_eq.symm) ?_
  intro i j f
  exact V.isZero.eq_of_src _ _

/-- The original total split inclusion retains the actual relative chosen zero. -/
@[simp] theorem totalFiberInclusion_zeroSimplex (n : SimplexCategory) :
    (totalFiberInclusion N).app (op n) (zeroSimplex V.cof V.weq V.zero V.isZero (op n)) =
      zeroSimplex (waldhausenStructure N n).cof (waldhausenStructure N n).weq
        (zero N n) (isZero N n) (op n) := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ fiber_zero N n) ?_
  intro i j f
  exact ((fiber_exact N n).zero V.isZero).eq_of_src _ _

/-- Realization retains the exact canonical change-of-weak-equivalences triangle. -/
theorem totalFiberInclusion_coarseEvaluation_realized :
    (SSet.toTop.map (coarseEvaluation N he)).hom.comp
      (SSet.toTop.map (totalFiberInclusion N)).hom = changeWeakMap N := by
  have h := congrArg (fun f ↦ (SSet.toTop.map f).hom)
    (totalFiberInclusion_coarseEvaluation N he)
  rw [SSet.toTop.map_comp, TopCat.hom_comp] at h
  exact h

/-- The actual all-zero vertex of the original total relative S-construction. -/
def totalZeroVertex : (SSet.diagonalSSet (relativeSRows N)) _⦋0⦌ :=
  zeroSimplex (waldhausenStructure N ⦋0⦌).cof (waldhausenStructure N ⦋0⦌).weq
    (zero N ⦋0⦌) (isZero N ⦋0⦌) (op ⦋0⦌)

/-- The original total relative realization is based at its actual zero vertex. -/
def totalBasepoint : |SSet.diagonalSSet (relativeSRows N)| :=
  SSet.toTop.map (SSet.yonedaEquiv.symm (totalZeroVertex N)) default

/-- The exact forward evaluation preserves the actual chosen basepoint. -/
@[simp] theorem coarseEvaluation_basepoint :
    SSet.toTop.map (coarseEvaluation N he) (totalBasepoint N) = N.coarse.kBasepoint := by
  have h := SSet.yonedaEquiv_symm_comp (totalZeroVertex N) (coarseEvaluation N he)
  have h' := congrArg (fun f : (Δ[0] : SSet.{u}) ⟶ sSet N.coarse.cof N.coarse.weq ↦
    SSet.toTop.map f default) h
  simpa only [Functor.map_comp, TopCat.comp_app, totalZeroVertex,
    coarseEvaluation_zeroSimplex, totalBasepoint, basepoint, delooping] using h'

/-- The exact original split inclusion preserves the actual relative basepoint. -/
@[simp] theorem totalFiberInclusion_basepoint :
    SSet.toTop.map (totalFiberInclusion N) V.kBasepoint = totalBasepoint N := by
  have h := SSet.yonedaEquiv_symm_comp
    (zeroSimplex V.cof V.weq V.zero V.isZero (op ⦋0⦌)) (totalFiberInclusion N)
  have h' := congrArg (fun f : (Δ[0] : SSet.{u}) ⟶
    SSet.diagonalSSet (relativeSRows N) ↦ SSet.toTop.map f default) h
  simpa only [Functor.map_comp, TopCat.comp_app, totalFiberInclusion_zeroSimplex,
    totalBasepoint, totalZeroVertex, basepoint, delooping] using h'

end CategoryTheory.Waldhausen.Fibration.RelativeRows
