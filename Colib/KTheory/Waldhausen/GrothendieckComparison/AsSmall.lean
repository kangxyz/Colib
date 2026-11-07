/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckGroup.AsSmall
public import Colib.KTheory.Waldhausen.GrothendieckComparison.Equivalence

/-! # The original classical K₀ comparison in independent universes

The existing genuine common-universe model preserves the actual original
object loop under its original based realization homeomorphism. Composing
its checked K-equivalence with the original up/down algebraic presentation
maps gives the comparison on the unchanged original category and K₀.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/SmallModel.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The existing actual universe-lifting simplicial map preserves the original object simplex. -/
theorem asSmallSSetIso_objectSimplex (A : C) :
    W.asSmallSSetIso.hom.app (op ⦋1⦌) (W.kZeroObjectSimplex A) =
      W.asSmall.kZeroObjectSimplex (AsSmall.up.obj A) := by
  apply Subtype.ext
  change (intervalProjection ⦋1⦌ ⋙ QuotientRows.oneDiagram W A) ⋙ AsSmall.up =
    intervalProjection ⦋1⦌ ⋙ QuotientRows.oneDiagram W.asSmall (AsSmall.up.obj A)
  rw [Functor.assoc, QuotientRows.oneDiagram_postcompose W W.asSmall
    W.asSmall_up_exact rfl]

/-- The existing actual based homeomorphism maps the unchanged original object loop. -/
theorem asSmallDeloopingHomeomorph_objectLoop (A : C) :
    ((W.kZeroObjectLoop A).map W.asSmallDeloopingHomeomorph.continuous).cast
      W.asSmallDeloopingHomeomorph_basepoint.symm
      W.asSmallDeloopingHomeomorph_basepoint.symm =
        W.asSmall.kZeroObjectLoop (AsSmall.up.obj A) := by
  ext t
  change SSet.toTop.map W.asSmallSSetIso.hom
    (realizationEdgePath (W.kZeroObjectEdge A) t) = _
  exact (realizationEdgePath_naturality_apply W.asSmallSSetIso.hom
    (W.kZeroObjectEdge A) t).trans
      (congrArg (fun e : (sSet W.asSmall.cof W.asSmall.weq) _⦋1⦌ ↦
        SSet.toTop.map (SSet.yonedaEquiv.symm e) (realizationInterval t))
          (W.asSmallSSetIso_objectSimplex A))

/-- The original homotopical small-model equivalence retains the original object-loop class. -/
@[simp] theorem asSmallKEquiv_objectClass (A : C) :
    W.asSmallKEquiv 0 (W.kZeroObjectClass A) =
      W.asSmall.kZeroObjectClass (AsSmall.up.obj A) := by
  apply W.asSmall.kZeroFundamentalGroupEquiv.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (HomotopyGroup.map W.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
      W.asSmallDeloopingHomeomorph_basepoint (W.kZeroObjectClass A)) = _
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
  change FundamentalGroup.mapOfEq _ _
    (W.kZeroFundamentalGroupEquiv (W.kZeroObjectClass A)) = _
  rw [W.kZeroFundamentalGroupEquiv_objectClass,
    W.asSmall.kZeroFundamentalGroupEquiv_objectClass, FundamentalGroup.mapOfEq_apply]
  apply End.ext
  exact congrArg Path.Homotopic.Quotient.mk (W.asSmallDeloopingHomeomorph_objectLoop A)

end CategoryTheory.Waldhausen.Structure
namespace CategoryTheory.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The genuine original classical-to-homotopical equivalence, allowing
independent original object and morphism universes. -/
@[colib_tag "COL-0269", colib_ref "ThomasonTrobaugh1990" "Section 1.5.6, p. 261"
  "adaptation" "The actual object-loop map identifies the weak-arrow and cofibration-pushout \
    presentation with unnormalized Waldhausen K-zero in independent universes"]
def grothendieckKZeroEquivOfAsSmall : Multiplicative (Group W) ≃* W.K 0 :=
  (asSmallGrothendieckEquiv W).toMultiplicative.trans
    ((grothendieckKZeroEquiv W.asSmall).trans (W.asSmallKEquiv 0).symm)

/-- Universe transport keeps the original object class and original topological object loop. -/
@[simp] theorem grothendieckKZeroEquivOfAsSmall_objectClass (A : C) :
    grothendieckKZeroEquivOfAsSmall W (Multiplicative.ofAdd (objectClass W A)) =
      W.kZeroObjectClass A := by
  apply (W.asSmallKEquiv 0).injective
  change W.asSmallKEquiv 0
    ((W.asSmallKEquiv 0).symm
      (grothendieckKZeroEquiv W.asSmall
        (Multiplicative.ofAdd (asSmallGrothendieckEquiv W (objectClass W A))))) = _
  rw [MulEquiv.apply_symm_apply, asSmallGrothendieckEquiv_objectClass,
    grothendieckKZeroEquiv_objectClass, W.asSmallKEquiv_objectClass]

/-- The inverse universe-bridge comparison retains every original object generator. -/
@[simp] theorem grothendieckKZeroEquivOfAsSmall_symm_objectClass (A : C) :
    (grothendieckKZeroEquivOfAsSmall W).symm (W.kZeroObjectClass A) =
      Multiplicative.ofAdd (objectClass W A) := by
  rw [← grothendieckKZeroEquivOfAsSmall_objectClass W A, MulEquiv.symm_apply_apply]

/-- The general comparison retains the exact existing small-model comparison square. -/
theorem asSmallKEquiv_grothendieckKZeroEquivOfAsSmall
    (a : Multiplicative (Group W)) :
    W.asSmallKEquiv 0 (grothendieckKZeroEquivOfAsSmall W a) =
      grothendieckKZeroEquiv W.asSmall
        (Multiplicative.ofAdd (asSmallGrothendieckEquiv W a.toAdd)) :=
  (W.asSmallKEquiv 0).apply_symm_apply _

variable {D : Type u} [Category.{v} D] (V : Structure D) (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Every original exact functor commutes with the independent-universe comparison,
using precisely the existing canonical rebased KMap. -/
theorem grothendieckKZeroEquivOfAsSmall_natural
    (a : Multiplicative (Group W)) :
    KMap hF 0 (grothendieckKZeroEquivOfAsSmall W a) =
      grothendieckKZeroEquivOfAsSmall V ((map W F hF).toMultiplicative a) := by
  apply (V.asSmallKEquiv 0).injective
  have hk := DFunLike.congr_fun (asSmallKEquiv_naturality hF 0)
    (grothendieckKZeroEquivOfAsSmall W a)
  change V.asSmallKEquiv 0 (KMap hF 0 (grothendieckKZeroEquivOfAsSmall W a)) =
    KMap hF.asSmall 0 (W.asSmallKEquiv 0 (grothendieckKZeroEquivOfAsSmall W a)) at hk
  rw [hk, asSmallKEquiv_grothendieckKZeroEquivOfAsSmall,
    asSmallKEquiv_grothendieckKZeroEquivOfAsSmall]
  have hs := DFunLike.congr_fun
    (grothendieckKZeroEquiv_natural W.asSmall V.asSmall (asSmallFunctor F) hF.asSmall)
    (Multiplicative.ofAdd (asSmallGrothendieckEquiv W a.toAdd))
  change KMap hF.asSmall 0
    (grothendieckKZeroEquiv W.asSmall
      (Multiplicative.ofAdd (asSmallGrothendieckEquiv W a.toAdd))) =
    grothendieckKZeroEquiv V.asSmall
      (Multiplicative.ofAdd (map W.asSmall (asSmallFunctor F) hF.asSmall
        (asSmallGrothendieckEquiv W a.toAdd))) at hs
  rw [hs, ← asSmallGrothendieckEquiv_natural W V F hF]
  rfl

/-- The actual inverse comparison is natural on every original homotopical K₀ class. -/
theorem grothendieckKZeroEquivOfAsSmall_symm_natural (x : W.K 0) :
    (grothendieckKZeroEquivOfAsSmall V).symm (KMap hF 0 x) =
      (map W F hF).toMultiplicative ((grothendieckKZeroEquivOfAsSmall W).symm x) := by
  apply (grothendieckKZeroEquivOfAsSmall V).injective
  rw [MulEquiv.apply_symm_apply]
  have h := grothendieckKZeroEquivOfAsSmall_natural W V F hF
    ((grothendieckKZeroEquivOfAsSmall W).symm x)
  simpa only [MulEquiv.apply_symm_apply] using h

/-- On matching-universe small categories, the new universe bridge is precisely
the already-proved original canonical comparison, not a second identification. -/
theorem grothendieckKZeroEquivOfAsSmall_eq
    {C₀ : Type u} [SmallCategory C₀] (W₀ : Structure C₀) :
    grothendieckKZeroEquivOfAsSmall W₀ = grothendieckKZeroEquiv W₀ := by
  have h : (grothendieckKZeroEquivOfAsSmall W₀ : Multiplicative (Group W₀) →* W₀.K 0) =
      (grothendieckKZeroEquiv W₀ : Multiplicative (Group W₀) →* W₀.K 0) := by
    apply mulHom_ext W₀
    intro A
    exact (grothendieckKZeroEquivOfAsSmall_objectClass W₀ A).trans
      (grothendieckKZeroEquiv_objectClass W₀ A).symm
  apply MulEquiv.ext
  intro a
  exact congrArg (fun f : Multiplicative (Group W₀) →* W₀.K 0 ↦ f a) h

end CategoryTheory.Waldhausen.AlgebraicGrothendieck
