/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.StableOmega
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
Nonnegative stable groups of Omega-spectra are identified naturally with the original positive
homotopy groups at level one.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StableLevelOne.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native prespectrum,
integer degrees, original structure maps, coefficients and signs are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum
variable (E : LoopPrespectrum.{u}) (hE : E.IsOmega)

/-- Positive homotopy of the original level-one space identifies with every
nonnegative stable group through the actual structure map and colimit inclusion. -/
def levelOneStableStageEquiv (n : ℕ) :
    Additive (HomotopyGroup.Pi (n + 1) (E.space 1) (E.point 1)) ≃+
      (stableSystem E (n : ℤ)).obj 0 :=
  (structurePiEquiv E hE 1 n).toAdditive.trans (nonnegativeStableStageEquiv E n)

/-- The level-one equivalence followed by the canonical stable-colimit equivalence. -/
def levelOneStableEquiv (n : ℕ) :
    Additive (HomotopyGroup.Pi (n + 1) (E.space 1) (E.point 1)) ≃+
      stableHomotopyGroup E (n : ℤ) :=
  (levelOneStableStageEquiv E hE n).trans
    (stableHomotopyStageZeroIso E hE (n : ℤ)).symm.addCommGroupIsoToAddEquiv

theorem levelOneStableEquiv_apply (n : ℕ)
    (a : Additive (HomotopyGroup.Pi (n + 1) (E.space 1) (E.point 1))) :
    levelOneStableEquiv E hE n a =
      stableHomotopyι E (n : ℤ) 0 (levelOneStableStageEquiv E hE n a) := by
  change (stableHomotopyStageZeroIso E hE (n : ℤ)).inv _ = _
  rw [stableHomotopyStageZeroIso_inv]
  rfl

variable {E} {F : LoopPrespectrum.{u}} (hF : F.IsOmega) (f : E ⟶ F)

theorem levelOneStableStageEquiv_naturality (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (E.space 1) (E.point 1)) :
    levelOneStableStageEquiv F hF n (Additive.ofMul (HomotopyGroup.piMap n (f.map 1)
      (f.map_point 1) a)) =
      (stableSystemMap f (n : ℤ)).app 0
        (levelOneStableStageEquiv E hE n (Additive.ofMul a)) := by
  change nonnegativeStableStageEquiv F n
    (Additive.ofMul (structurePiMap F 1 n (HomotopyGroup.piMap n (f.map 1) (f.map_point 1) a))) =
      (stableSystemMap f (n : ℤ)).app 0
        (nonnegativeStableStageEquiv E n (Additive.ofMul (structurePiMap E 1 n a)))
  rw [← nonnegativeStableStageEquiv_naturality]
  exact congrArg (fun b ↦ nonnegativeStableStageEquiv F n (Additive.ofMul b))
    (DFunLike.congr_fun (structurePiMap_naturality f 1 n) a)

theorem levelOneStableEquiv_naturality (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (E.space 1) (E.point 1)) :
    levelOneStableEquiv F hF n (Additive.ofMul (HomotopyGroup.piMap n (f.map 1)
      (f.map_point 1) a)) =
      (stableHomotopyFunctor (n : ℤ)).map f
        (levelOneStableEquiv E hE n (Additive.ofMul a)) := by
  rw [levelOneStableEquiv_apply, levelOneStableEquiv_apply,
    levelOneStableStageEquiv_naturality hE hF f]
  exact (ConcreteCategory.congr_hom (stableHomotopyι_naturality f (n : ℤ) 0)
    (levelOneStableStageEquiv E hE n (Additive.ofMul a))).symm

include hE hF in
/-- A bijective original positive homotopy map at level one gives the unchanged
nonnegative stable map as an isomorphism. -/
theorem stableMap_nonneg_isIso_of_levelOne (n : ℕ)
    (hf : Function.Bijective (HomotopyGroup.piMap n (f.map 1) (f.map_point 1))) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map f) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let eE := levelOneStableEquiv E hE n
  let eF := levelOneStableEquiv F hF n
  have he : (fun a ↦ (stableHomotopyFunctor (n : ℤ)).map f (eE a)) =
      (fun a ↦ eF (Additive.ofMul (HomotopyGroup.piMap n (f.map 1) (f.map_point 1) a.toMul))) := by
    funext a
    exact (levelOneStableEquiv_naturality hE hF f n a.toMul).symm
  have hb : Function.Bijective
      (fun a : Additive (HomotopyGroup.Pi (n + 1) (E.space 1) (E.point 1)) ↦
      Additive.ofMul (HomotopyGroup.piMap n (f.map 1) (f.map_point 1) a.toMul)) := hf
  exact (Function.Bijective.of_comp_iff _ eE.bijective).mp
    (by
      rw [show ((stableHomotopyFunctor (n : ℤ)).map f) ∘ eE = _ from he]
      exact eF.bijective.comp hb)

end Topology.LoopPrespectrum
