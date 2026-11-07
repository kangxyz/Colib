/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Automorphism.Class
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportFundamentalGroup
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.KOneNormalization
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.Reversal

/-!
Implementation provenance: `Quillen/KTheory/Automorphism/PositiveNormalization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, tracks,
hypotheses, and signs are retained under native mathematical ownership.

# The original right and positive loop normalizations

Right translation uses its original inverse-pair cancellation cap. Positive
normalization is exactly its inner-loop reversal, including reversal of that
same cap. A genuine homotopy preserves the corrected class because each
loop-space component has abelian fundamental group. This does not assert
that an arbitrary object loop acts trivially on the ambient second homotopy group.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open Topology HomotopyGroup
open CategoryTheory
open scoped Topology
namespace CategoryTheory.ExactCategory.Automorphism
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Every actual loop-space component has commutative fundamental group, via its second
homotopy group. -/
lemma loopComponent_piOne_mul_comm (p : Path x x)
    (a b : HomotopyGroup.Pi 1 (Path x x) p) : a * b = b * a := by
  let e := HomotopyGroup.pi1MulEquivFundamentalGroup.trans (loopKOneNormalization p)
  apply e.injective
  simp only [map_mul]
  exact mul_comm _ _

private lemma fundamentalGroup_transport_symm {p q : Path x x} (γ : Path p q) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath γ.symm =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm := by
  apply MulEquiv.ext
  intro a
  apply End.ext
  change CategoryTheory.Groupoid.inv (CategoryTheory.Groupoid.inv
    (Path.Homotopic.Quotient.mk γ)) ≫ a.asHom ≫
      CategoryTheory.Groupoid.inv (Path.Homotopic.Quotient.mk γ) =
    Path.Homotopic.Quotient.mk γ ≫ a.asHom ≫
      CategoryTheory.Groupoid.inv (Path.Homotopic.Quotient.mk γ)
  simp only [Groupoid.inv_eq_inv, CategoryTheory.IsIso.inv_inv]

variable {Z : Type v} [TopologicalSpace Z] (f : C(Z, Path x x)) (z : Z)

/-- Postcompose the displayed loop-valued map with right translation by its base loop’s inverse. -/
def rightNormalizedLoopMap : C(Z, Path x x) := (rightTranslate (f z)).comp f

/-- The original cancellation cap, in the direction from the translated image to the
constant loop. -/
def rightNormalizationPath : Path (rightNormalizedLoopMap f z z) (Path.refl x) :=
  (cancellationPath (f z)).symm

/-- Right translation and the specified cap induce exactly the original capped-class
homomorphism. -/
theorem rightNormalization_formula (a : HomotopyGroup.Pi 1 Z z) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv (rightNormalizationPath f z) 0
        (piMap 0 (rightNormalizedLoopMap f z) rfl a)) =
      loopComponentToPiTwo (f z)
        (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)) := by
  apply (loopShiftMulEquiv 0).injective
  simp only [loopComponentToPiTwo, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  change pathTransport (rightNormalizationPath f z) 1
    (HomotopyGroup.map (rightNormalizedLoopMap f z) rfl a) =
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath (cancellationPath (f z))).symm
          (FundamentalGroup.map (rightTranslate (f z)) (f z)
            (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a))))
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [piOneEquivFundamentalGroup_pathTransport, MulEquiv.apply_symm_apply]
  erw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
  have hm (b : FundamentalGroup Z z) :
      FundamentalGroup.mapOfEq (rightNormalizedLoopMap f z) rfl b =
        FundamentalGroup.map (rightTranslate (f z)) (f z) (FundamentalGroup.map f z b) := by
    rcases b with ⟨b⟩
    obtain ⟨α, rfl⟩ := Path.Homotopic.Quotient.mk_surjective b
    rw [FundamentalGroup.mapOfEq_apply]
    rfl
  rw [hm]
  exact DFunLike.congr_fun (fundamentalGroup_transport_symm (cancellationPath (f z))) _

/-- Reverse the inner loop after the original right translation, with no other normalization. -/
def positiveNormalizedLoopMap : C(Z, Path x x) :=
  loopReversal.comp (rightNormalizedLoopMap f z)

/-- Reverse the inner loops of the original cancellation track while retaining its outer
direction. -/
def positiveNormalizationPath : Path (positiveNormalizedLoopMap f z z) (Path.refl x) :=
  loopReversalPath (rightNormalizationPath f z)

/-- The displayed right normalization and single reversal represent the inverse original
capped class. -/
theorem positiveNormalization_formula (a : HomotopyGroup.Pi 1 Z z) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv (positiveNormalizationPath f z) 0
        (piMap 0 (positiveNormalizedLoopMap f z) rfl a)) =
      (loopComponentToPiTwo (f z)
        (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)))⁻¹ := by
  have ht : pathTransport (positiveNormalizationPath f z) 1
      (HomotopyGroup.map (positiveNormalizedLoopMap f z) rfl a) =
    HomotopyGroup.map loopReversal loopReversal_refl
      (pathTransport (rightNormalizationPath f z) 1
        (HomotopyGroup.map (rightNormalizedLoopMap f z) rfl a)) := by
    exact (congrArg (pathTransport (positiveNormalizationPath f z) 1)
      (HomotopyGroup.map_comp (rightNormalizedLoopMap f z) rfl loopReversal rfl a)).trans
      (pathTransport_naturality_of_track loopReversal (rightNormalizationPath f z)
        (positiveNormalizationPath f z) rfl loopReversal_refl (fun _ => rfl) 1 _)
  change (loopShiftMulEquiv 0).symm (pathTransport _ 1 (HomotopyGroup.map _ _ a)) = _
  rw [ht]
  exact (loopShiftEquiv_symm_loopReversal 1 _).trans
    (congrArg (fun a => a⁻¹) (rightNormalization_formula f z a))

/-- A genuine map homotopy suffices with the candidate’s actual prescribed correction path. -/
theorem positiveNormalization_of_homotopy {k : C(Z, Path x x)}
    (H : k.Homotopy (positiveNormalizedLoopMap f z))
    (γ : Path (k z) (Path.refl x)) (a : HomotopyGroup.Pi 1 Z z) :
    (loopShiftMulEquiv 0).symm
      (pathTransportMulEquiv γ 0 (piMap 0 k rfl a)) =
      (loopComponentToPiTwo (f z)
        (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)))⁻¹ := by
  have h := DFunLike.congr_fun (piOne_homotopy_corrected H γ
    (positiveNormalizationPath f z) (loopComponent_piOne_mul_comm (Path.refl x))) a
  exact (congrArg (loopShiftMulEquiv 0).symm h).trans (positiveNormalization_formula f z a)

end CategoryTheory.ExactCategory.Automorphism
