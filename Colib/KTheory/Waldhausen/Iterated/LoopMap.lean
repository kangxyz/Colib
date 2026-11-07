/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.Iterated.Double
public import Colib.KTheory.Waldhausen.Basic
public import Colib.Topology.Realization.HomotopyBridge
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift


/-!
# The first genuine iterated-S loop structure map

The actual simplicial cylinder realizes to a continuous map from the original
Waldhausen delooping into the based loop space of the second S-stage. Its
loop endpoints and original K-basepoint equation are proved. The genuine
loop-degree shift gives a degree-raising homomorphism on the existing
K-groups. This file proves neither an Omega-equivalence nor the full tower,
and does not define nonconnective K-theory.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Waldhausen/SConstruction/Iterated/LoopMap.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual quotient-row
construction, maps, chosen zero objects, hypotheses and universes are retained.
Native Colib simplicial, realization and homotopy-group owners are reused.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory SSet Topology
open scoped Simplicial Topology unitInterval
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The zero-object vertex of the double S-construction. -/
def doubleVertex : (doubleDiagonal W).obj (op ⦋0⦌) :=
  zeroSimplex (QuotientRows.waldhausenStructure W ⦋0⦌).cof
    (QuotientRows.waldhausenStructure W ⦋0⦌).weq
    (QuotientRows.zero W ⦋0⦌) (QuotientRows.isZero W ⦋0⦌) (op ⦋0⦌)

lemma doubleZero_eq_const : doubleZero W = SSet.const (doubleVertex W) := by
  ext n A : 4
  rfl

lemma suspensionCylinder_zeroSimplex (n : SimplexCategoryᵒᵖ)
    (τ : n.unop ⟶ ⦋1⦌) :
    (suspensionCylinder W).app n
      (zeroSimplex W.cof W.weq W.zero W.isZero n, ⟨τ⟩) =
      (doubleZero W).app n (zeroSimplex W.cof W.weq W.zero W.isZero n) := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ suspensionRow_zero_obj W τ) ?_
  intro p q f
  exact ((suspensionRow_exact W τ).zero W.isZero).eq_of_src _ _

lemma suspensionCylinder_fixed_vertex :
    SSet.yonedaEquiv.symm (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) ▷ Δ[1] ≫
      suspensionCylinder W =
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (doubleVertex W) := by
  ext n z : 4
  exact suspensionCylinder_zeroSimplex W n z.2.down

/-- The original cylinder is a self-homotopy of the actual zero map. -/
def suspensionHomotopy : SSet.Homotopy (doubleZero W) (doubleZero W) where
  h := suspensionCylinder W
  h₀ := suspensionCylinder_zero W
  h₁ := suspensionCylinder_one W
  rel := by ext n z; exact z.1.property.elim

/-- The genuine realization of the second S-stage. -/
def doubleDelooping : TopCat.{max u v} := SSet.toTop.obj (doubleDiagonal W)

/-- The realization of the zero-object vertex in the double S-construction. -/
def doubleBasepoint : doubleDelooping W := realizationPoint (doubleVertex W)

lemma doubleZero_realization (x : W.Delooping) :
    SSet.toTop.map (doubleZero W) x = doubleBasepoint W := by
  rw [doubleZero_eq_const]
  exact realization_const_apply _ x

/-- The original S-construction has an actual continuous map to loops on its
second iterated S-construction, with both loop endpoints proved. -/
def loopStructureMap : C(W.Delooping, Path (doubleBasepoint W) (doubleBasepoint W)) where
  toFun x :=
    { toFun t := realizationSimplicialHomotopy (suspensionHomotopy W) (t, x)
      continuous_toFun := (realizationSimplicialHomotopy (suspensionHomotopy W)).continuous.comp
        (continuous_id.prodMk continuous_const)
      source' := ((realizationSimplicialHomotopy (suspensionHomotopy W)).apply_zero x).trans
        (doubleZero_realization W x)
      target' := ((realizationSimplicialHomotopy (suspensionHomotopy W)).apply_one x).trans
        (doubleZero_realization W x) }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (realizationSimplicialHomotopy (suspensionHomotopy W)).continuous.comp
      (continuous_snd.prodMk continuous_fst)

/-- The original chosen K-basepoint goes to the literal constant loop. -/
@[simp] lemma loopStructureMap_basepoint :
    loopStructureMap W W.kBasepoint = Path.refl (doubleBasepoint W) := by
  ext t
  exact realizationSimplicialHomotopy_fixed_vertex (suspensionHomotopy W)
    (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) (doubleVertex W)
    (suspensionCylinder_fixed_vertex W) t

/-- The actual structure map gives a degree-raising homomorphism on the
original K-groups. Invertibility has not been assumed or asserted. -/
def degreeRaisingMap (n : ℕ) :
    W.K n →* HomotopyGroup.Pi (n + 2) (doubleDelooping W) (doubleBasepoint W) :=
  (loopShiftMulEquiv n).symm.toMonoidHom.comp
    (HomotopyGroup.piMap n (loopStructureMap W) (loopStructureMap_basepoint W))


end CategoryTheory.Waldhausen.IteratedS
