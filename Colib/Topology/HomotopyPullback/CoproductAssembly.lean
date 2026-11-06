/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.CoproductPaths

/-! # Varying-target cartesian coproduct and actual cofan assembly -/
/-! Implementation source: `Quillen/Topology/Realization/Cartesian/CoproductAssembly.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual coproduct topologies and canonical
constant-path comparisons are retained. -/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.HomotopyPullback

section Sigma
variable {ι : Type u} {W X A B : ι → Type u}
  [∀ i, TopologicalSpace (W i)] [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
  (p : ∀ i, C(W i, A i)) (q : ∀ i, C(X i, B i))
  (f : ∀ i, C(W i, X i)) (g : ∀ i, C(A i, B i))
  (w : ∀ i, (q i).comp (f i) = (g i).comp (p i))

include w in
theorem sigmaSquare : (sigmaMap q).comp (sigmaMap f) = (sigmaMap g).comp (sigmaMap p) := by
  apply ContinuousMap.ext
  intro z
  exact congrArg (Sigma.mk z.1) (ContinuousMap.congr_fun (w z.1) z.2)

/-- Arbitrary families of actual cartesian squares assemble into their
varying-target coproduct square, with canonical comparison unchanged. -/
theorem cartesianSigma (h : ∀ i, Cartesian (p i) (q i) (f i) (g i) (w i)) :
    Cartesian (sigmaMap p) (sigmaMap q) (sigmaMap f) (sigmaMap g) (sigmaSquare p q f g w) := by
  let es := fun i ↦ (h i).equiv.trans (componentPullbackHomeomorph q i (g i)).toHomotopyEquiv
  refine ⟨(ContinuousMap.sigmaHomotopyEquiv es).trans
    (sigmaPullbackHomeomorph (sigmaMap q)
      (fun i ↦ (ContinuousMap.sigmaMk i).comp (g i))).toHomotopyEquiv, ?_⟩
  apply ContinuousMap.ext
  rintro ⟨i, x⟩
  change sigmaPullbackMap (sigmaMap q) (fun i ↦ (ContinuousMap.sigmaMk i).comp (g i))
    ⟨i, componentPullbackMap q i (g i) ((h i).equiv.toFun x)⟩ = _
  rw [(h i).equiv_toFun]
  rfl
end Sigma

section Cofans
variable {ι : Type u} (W X A B : ι → TopCat.{u})
  (cW : Cofan W) (cX : Cofan X) (cA : Cofan A) (cB : Cofan B)
  (hW : IsColimit cW) (hX : IsColimit cX) (hA : IsColimit cA) (hB : IsColimit cB)
  (p : cW.pt ⟶ cA.pt) (q : cX.pt ⟶ cB.pt)
  (f : cW.pt ⟶ cX.pt) (g : cA.pt ⟶ cB.pt) (w : f ≫ q = p ≫ g)
  (ps : ∀ i, W i ⟶ A i) (qs : ∀ i, X i ⟶ B i)
  (fs : ∀ i, W i ⟶ X i) (gs : ∀ i, A i ⟶ B i)
  (ws : ∀ i, fs i ≫ qs i = ps i ≫ gs i)
  (wp : ∀ i, cW.inj i ≫ p = ps i ≫ cA.inj i)
  (wq : ∀ i, cX.inj i ≫ q = qs i ≫ cB.inj i)
  (wf : ∀ i, cW.inj i ≫ f = fs i ≫ cX.inj i)
  (wg : ∀ i, cA.inj i ≫ g = gs i ≫ cB.inj i)

include hW hX hA hB wp wq wf wg in
/-- The same result for four arbitrary actual coproduct cocones, using
their proved universal properties rather than preferred sigma models. -/
theorem cartesianCofan (h : ∀ i, Cartesian (ps i).hom (qs i).hom (fs i).hom (gs i).hom
    (congrArg TopCat.Hom.hom (ws i))) :
    Cartesian p.hom q.hom f.hom g.hom (congrArg TopCat.Hom.hom w) := by
  apply cartesianOfCoordinates p.hom q.hom f.hom g.hom (congrArg TopCat.Hom.hom w)
    (sigmaMap (fun i ↦ (ps i).hom)) (sigmaMap (fun i ↦ (qs i).hom))
    (sigmaMap (fun i ↦ (fs i).hom)) (sigmaMap (fun i ↦ (gs i).hom))
    (sigmaSquare _ _ _ _ (fun i ↦ congrArg TopCat.Hom.hom (ws i)))
    (cofanHomeomorph W cW hW).symm (cofanHomeomorph X cX hX).symm
    (cofanHomeomorph A cA hA).symm (cofanHomeomorph B cB hB).symm
  · exact cofanMap_coordinates W A cW cA hW hA p ps wp
  · exact cofanMap_coordinates X B cX cB hX hB q qs wq
  · exact cofanMap_coordinates W X cW cX hW hX f fs wf
  · exact cofanMap_coordinates A B cA cB hA hB g gs wg
  · exact cartesianSigma _ _ _ _ (fun i ↦ congrArg TopCat.Hom.hom (ws i)) h
end Cofans

section Components
variable {ι : Type u} (X B : ι → TopCat.{u}) (cX : Cofan X) (cB : Cofan B)
  (hX : IsColimit cX) (hB : IsColimit cB) (q : cX.pt ⟶ cB.pt) (qs : ∀ i, X i ⟶ B i)
  (wq : ∀ i, cX.inj i ≫ q = qs i ≫ cB.inj i)

include hX hB in
/-- Every actual component inclusion is homotopy cartesian against the
coproduct of arbitrary vertical maps, with no fibration assumption. -/
theorem cartesianCofanComponent (i : ι) :
    Cartesian (qs i).hom q.hom (cX.inj i).hom (cB.inj i).hom (congrArg TopCat.Hom.hom (wq i)) := by
  apply cartesianOfCoordinates (W' := X i) (X' := Σ j, X j) (A' := B i) (B' := Σ j, B j)
    (qs i).hom q.hom (cX.inj i).hom (cB.inj i).hom
    (congrArg TopCat.Hom.hom (wq i))
    (qs i).hom (sigmaMap (fun j ↦ (qs j).hom))
    (ContinuousMap.sigmaMk (X := fun j ↦ X j) i) (ContinuousMap.sigmaMk (X := fun j ↦ B j) i) rfl
    (Homeomorph.refl (X i)) (cofanHomeomorph X cX hX).symm
    (Homeomorph.refl (B i)) (cofanHomeomorph B cB hB).symm
  · rfl
  · exact cofanMap_coordinates X B cX cB hX hB q qs wq
  · apply ContinuousMap.ext
    intro x
    apply (cofanHomeomorph X cX hX).injective
    change cofanHomeomorph X cX hX ⟨i, x⟩ =
      cofanHomeomorph X cX hX ((cofanHomeomorph X cX hX).symm (cX.inj i x))
    rw [cofanHomeomorph_apply, Homeomorph.apply_symm_apply]
  · apply ContinuousMap.ext
    intro x
    apply (cofanHomeomorph B cB hB).injective
    change cofanHomeomorph B cB hB ⟨i, x⟩ =
      cofanHomeomorph B cB hB ((cofanHomeomorph B cB hB).symm (cB.inj i x))
    rw [cofanHomeomorph_apply, Homeomorph.apply_symm_apply]
  · exact cartesianComponentInclusion (fun j ↦ (qs j).hom) i
end Components

end Topology.HomotopyPullback
