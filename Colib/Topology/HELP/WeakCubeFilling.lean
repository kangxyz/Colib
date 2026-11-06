/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.CubicalHorn

/-!
# Actual finite cube fillings from singleton based homotopy sets

Normalize an arbitrary boundary map on the genuine contractible horn using
its proved HEP. Its top face is then an original generalized loop. A relative
nullhomotopy fills the product cube; whole-boundary HEP restores the exact
original boundary map. No sphere comparison or global contraction is assumed.


Implementation provenance:
`Quillen/Topology/HELP/WeakCubeFilling.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.CubicalTests
variable {X : Type u} [TopologicalSpace X]

/-- Arbitrary maps from the whole product boundary extend when the actual
based n-dimensional homotopy set at every source point is a singleton. -/
theorem exists_extend_productBoundary (n : ℕ)
    (hs : ∀ x : X,Subsingleton (HomotopyGroup.Pi n X x))
    (a : C(ProductBoundary.{u} n,X)) :
    ∃ c : C(cube.{u} n × unitInterval,X), c.comp (productBoundaryInclusion n).hom = a := by
  let x := a (hornInclusion n (hornZero n))
  let H : (a.comp (hornInclusion n).hom).Homotopy
      (ContinuousMap.const (Horn.{u} n) x) := {
    toFun z := a (hornInclusion n (hornContraction n z))
    continuous_toFun := by fun_prop
    map_zero_left z := congrArg (fun q ↦ a (hornInclusion n q))
      ((hornContraction n).map_zero_left z)
    map_one_left z := congrArg (fun q ↦ a (hornInclusion n q))
      ((hornContraction n).map_one_left z) }
  obtain ⟨V,hV₀,hVhorn⟩ := TopCat.homotopyExtensionProperty_continuous
    (hornInclusion_hep n) (TopCat.of X) a H.toContinuousMap H.map_zero_left
  let a₁ : C(ProductBoundary.{u} n,X) := ⟨fun z ↦ V (1,z),by fun_prop⟩
  have hhorn (z : Horn.{u} n) : a₁ (hornInclusion n z) = x :=
    (hVhorn 1 z).trans (H.map_one_left z)
  let p : GenLoop (Fin n) X x :=
    ⟨⟨fun z ↦ a₁ (topFace n ⟨z⟩),by fun_prop⟩,fun z hz ↦ hhorn (topRim n ⟨⟨z⟩,hz⟩)⟩
  have hp : (Quotient.mk' p : HomotopyGroup.Pi n X x) = Quotient.mk' GenLoop.const :=
    (hs x).elim _ _
  obtain ⟨K⟩ := Quotient.exact hp
  let L : C(cube.{u} n × unitInterval,X) := ⟨fun z ↦ K (unitInterval.symm z.2,z.1.down),by fun_prop⟩
  have htop (z : cube.{u} n) : L ((topFace n z).val) = a₁ (topFace n z) := by
    change K (unitInterval.symm 1,z.down) = p.val z.down
    rw [unitInterval.symm_one]
    exact K.apply_zero z.down
  have hside (z : Horn.{u} n) : L z.val = x := by
    rcases z.property with hz | hz
    · exact (K.prop (unitInterval.symm z.val.2) z.val.1.down hz).trans (p.property _ hz)
    · change K (unitInterval.symm z.val.2,z.val.1.down) = x
      rw [hz,unitInterval.symm_zero]
      exact K.toHomotopy.map_one_left z.val.1.down
  have hL (z : ProductBoundary.{u} n) : L z.val = a₁ z := by
    obtain ⟨z,rfl⟩ := hornTop_surjective n z
    cases z with
    | inl z => exact htop z
    | inr z => exact (hside z).trans (hhorn z).symm
  let R : a₁.Homotopy a := {
    toFun z := V (unitInterval.symm z.1,z.2)
    continuous_toFun := by fun_prop
    map_zero_left z := by simp only [unitInterval.symm_zero]; rfl
    map_one_left z := by simpa only [unitInterval.symm_one] using hV₀ z }
  obtain ⟨W,_,hW⟩ := TopCat.homotopyExtensionProperty_continuous
    (productBoundaryInclusion_hep n) (TopCat.of X) L R.toContinuousMap
      (fun z ↦ (R.map_zero_left z).trans (hL z).symm)
  refine ⟨⟨fun z ↦ W (1,z),by fun_prop⟩,?_⟩
  ext z
  exact (hW 1 z).trans (R.map_one_left z)

/-- Every original finite cube boundary map into a nonempty space with
singleton finite based homotopy sets has a literal continuous extension.
Dimension zero uses nonemptiness, not a vacuous based condition. -/
theorem exists_extend_boundary [Nonempty X]
    (hs : ∀ x : X,∀ n : ℕ,Subsingleton (HomotopyGroup.Pi n X x))
    (n : ℕ) (a : C(boundary.{u} n,X)) :
    ∃ c : C(cube.{u} n,X), c.comp (boundaryInclusion n).hom = a := by
  cases n with
  | zero =>
    refine ⟨ContinuousMap.const _ (Classical.choice (inferInstance : Nonempty X)),?_⟩
    ext z
    obtain ⟨i,_⟩ := z.property
    exact Fin.elim0 i
  | succ n =>
    let e := productBoundaryHomeomorph.{u} n
    let a' := a.comp (e : C(ProductBoundary.{u} n,boundary.{u} (n+1)))
    obtain ⟨c,hc⟩ := exists_extend_productBoundary n (fun x ↦ hs x n) a'
    refine ⟨c.comp ((stepHomeomorph n).symm : C(cube.{u} (n+1),cube.{u} n × unitInterval)),?_⟩
    ext z
    have h := ContinuousMap.congr_fun hc (e.symm z)
    change c ((stepHomeomorph n).symm z.val) = a (e (e.symm z)) at h
    exact h.trans (congrArg a (e.apply_symm_apply z))

end Topology.CubicalTests
