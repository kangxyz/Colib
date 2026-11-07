/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Omega
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Colimits
public import Colib.Topology.Prespectrum.Homotopy
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence

/-! Actual stable homotopy systems. Degrees are chosen at least two, with the
literal degree minus level equal to the requested integer. Transition maps
are the original structure maps followed by the proved inverse loop shift. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StableHomotopy.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native prespectrum,
integer degrees, original structure maps, coefficients and signs are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u
namespace Topology.LoopPrespectrum

/-- The abelian homotopy group at the stage used to compute the specified stable degree. -/
def stableStage (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) : CommGrpCat.{u} :=
  CommGrpCat.of (HomotopyGroup.Pi (d.toNat+n+2)
    (E.space ((-d).toNat+n+2)) (E.point ((-d).toNat+n+2)))

theorem stableStage_degree (d : ℤ) (n : ℕ) :
    (d.toNat+n+2 : ℤ) - ((-d).toNat+n+2) = d := by omega

/-- The genuine structure-induced transition with its original degree-shift inverse. -/
def stableTransition (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) :
    stableStage E d n ⟶ stableStage E d (n+1) :=
  CommGrpCat.ofHom ((loopShiftMulEquiv (x := E.point (((-d).toNat+n+2)+1))
    (d.toNat+n+1)).symm.toMonoidHom.comp
    (HomotopyGroup.mapHom (E.structureMap ((-d).toNat+n+2)) (E.map_point ((-d).toNat+n+2))))

/-- The original transitions form a genuine sequential abelian-group diagram. -/
def stableSystem (E : LoopPrespectrum.{u}) (d : ℤ) : ℕ ⥤ AddCommGrpCat.{u} :=
  Functor.ofSequence (stableTransition E d) ⋙ CommGrpCat.toAddCommGrp

/-- Stable homotopy groups are actual categorical colimits of the displayed original groups. -/
def stableHomotopyGroup (E : LoopPrespectrum.{u}) (d : ℤ) : AddCommGrpCat.{u} :=
  colimit (stableSystem E d)

/-- The actual stage inclusion into the constructed stable homotopy group. -/
def stableHomotopyι (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) :
    (stableSystem E d).obj n ⟶ stableHomotopyGroup E d := colimit.ι _ n

/-- A proved Omega-spectrum has bijective original transition maps in every integer degree. -/
theorem stableTransition_bijective (E : LoopPrespectrum.{u}) (hE : E.IsOmega) (d : ℤ) (n : ℕ) :
    Function.Bijective (stableTransition E d n) := by
  have hb {y : Path (E.point (((-d).toNat+n+2)+1)) (E.point (((-d).toNat+n+2)+1))}
      (h : E.structureMap ((-d).toNat+n+2) (E.point ((-d).toNat+n+2)) = y) :
      Function.Bijective (HomotopyGroup.map (N := Fin (d.toNat+n+2))
        (E.structureMap ((-d).toNat+n+2)) h) := by
    cases h
    exact (hE ((-d).toNat+n+2)).homotopy_bijective (E.point ((-d).toNat+n+2)) (d.toNat+n+2)
  exact (loopShiftMulEquiv (x := E.point (((-d).toNat+n+2)+1)) (d.toNat+n+1)).symm.bijective.comp
    (hb (E.map_point ((-d).toNat+n+2)))

end Topology.LoopPrespectrum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
namespace Topology.LoopPrespectrum

/-- The original adjoint structure map followed by the actual inverse degree shift. -/
def structurePiMap (E : LoopPrespectrum.{u}) (n k : ℕ) :
    HomotopyGroup.Pi (k+1) (E.space n) (E.point n) →*
      HomotopyGroup.Pi (k+2) (E.space (n+1)) (E.point (n+1)) :=
  (loopShiftMulEquiv (x := E.point (n+1)) k).symm.toMonoidHom.comp (HomotopyGroup.piMap k
    (E.structureMap n)
    (E.map_point n))

/-- Naturality keeps the original structure-induced homomorphism, including its degree-shift
    inverse. -/
theorem structurePiMap_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (n k : ℕ) :
    (structurePiMap F n k).comp (HomotopyGroup.piMap k (f.map n) (f.map_point n)) =
      (HomotopyGroup.piMap (k+1) (f.map (n+1)) (f.map_point (n+1))).comp (structurePiMap
        E n k) := by
  ext a
  apply (loopShiftMulEquiv (x := F.point (n+1)) k).injective
  change loopShiftMulEquiv k ((loopShiftMulEquiv k).symm _) =
    loopShiftMulEquiv k (HomotopyGroup.piMap (k+1) (f.map (n+1)) (f.map_point (n+1))
      ((loopShiftMulEquiv k).symm (HomotopyGroup.piMap k (E.structureMap n) (E.map_point n) a)))
  rw [MulEquiv.apply_symm_apply]
  have hn := congrArg (fun h ↦ h ((loopShiftMulEquiv (x := E.point (n+1)) k).symm
    (HomotopyGroup.piMap k (E.structureMap n) (E.map_point n) a)))
    (loopShiftMulEquiv_natural k (f.map (n+1)) (f.map_point (n+1)))
  change HomotopyGroup.piMap k (basedLoopMap (f.map (n+1)) (f.map_point (n+1))) _
    (loopShiftMulEquiv k ((loopShiftMulEquiv k).symm _)) = _ at hn
  rw [MulEquiv.apply_symm_apply] at hn
  change _ = loopShiftMulEquiv (x := F.point (n+1)) k
    (HomotopyGroup.piMap (k+1) (f.map (n+1)) (f.map_point (n+1))
      ((loopShiftMulEquiv (x := E.point (n+1)) k).symm
        (HomotopyGroup.piMap k (E.structureMap n) (E.map_point n) a))) at hn
  rw [← hn]
  have hc : (F.structureMap n).comp (f.map n) =
      (basedLoopMap (f.map (n+1)) (f.map_point (n+1))).comp (E.structureMap n) := by
    apply ContinuousMap.ext
    intro x
    exact (f.comm n x).symm
  have hm := congrFun (homotopyGroupMap_congr hc
    ((congrArg (F.structureMap n) (f.map_point n)).trans (F.map_point n))
    ((congrArg (basedLoopMap (f.map (n+1)) (f.map_point (n+1))) (E.map_point n)).trans
      (basedLoopMap_refl (f.map (n+1)) (f.map_point (n+1))))) a
  exact (HomotopyGroup.map_comp (f.map n) (f.map_point n) (F.structureMap n) (F.map_point n)
    a).symm.trans
    (hm.trans (HomotopyGroup.map_comp (E.structureMap n) (E.map_point n)
      (basedLoopMap (f.map (n+1)) (f.map_point (n+1)))
      (basedLoopMap_refl (f.map (n+1)) (f.map_point (n+1))) a))

/-- Actual prespectrum maps give original maps at every stable stage. -/
def stableStageMap {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (d : ℤ) (n : ℕ) :
    stableStage E d n ⟶ stableStage F d n :=
  CommGrpCat.ofHom (HomotopyGroup.piMap (d.toNat+n+1) (f.map ((-d).toNat+n+2))
    (f.map_point ((-d).toNat+n+2)))

theorem stableStageMap_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (d : ℤ) (n : ℕ) :
    stableTransition E d n ≫ stableStageMap f d (n+1) = stableStageMap f d n ≫ stableTransition
      F d n := by
  apply CommGrpCat.ext
  intro a
  exact (congrArg (fun h ↦ h a) (structurePiMap_naturality f ((-d).toNat+n+2) (d.toNat+n+1))).symm

end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum

/-- Original stage maps and genuine successor naturality form a natural transformation. -/
def stableSystemMap {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (d : ℤ) : stableSystem E d ⟶
    stableSystem F d :=
  Functor.whiskerRight (NatTrans.ofSequence (fun n ↦ stableStageMap f d n)
    (by intro n; simpa only [Functor.ofSequence_map_homOfLE_succ] using
      stableStageMap_naturality f d n))
    CommGrpCat.toAddCommGrp

@[simp] theorem stableSystemMap_id (E : LoopPrespectrum.{u}) (d : ℤ) : stableSystemMap (𝟙 E) d =
    𝟙 (stableSystem E d) := by
  apply NatTrans.ext
  funext n
  apply AddCommGrpCat.ext
  intro a
  exact HomotopyGroup.map_id a

@[simp] theorem stableSystemMap_comp {E F G : LoopPrespectrum.{u}} (f : E ⟶ F) (g : F ⟶ G) (d : ℤ) :
    stableSystemMap (f ≫ g) d = stableSystemMap f d ≫ stableSystemMap g d := by
  apply NatTrans.ext
  funext n
  apply AddCommGrpCat.ext
  intro a
  exact HomotopyGroup.map_comp (f.map ((-d).toNat+n+2)) (f.map_point ((-d).toNat+n+2))
    (g.map ((-d).toNat+n+2)) (g.map_point ((-d).toNat+n+2)) a

/-- The displayed original sequential systems vary functorially with the prespectrum. -/
def stableSystemFunctor (d : ℤ) : LoopPrespectrum.{u} ⥤ (ℕ ⥤ AddCommGrpCat.{u}) where
  obj E := stableSystem E d
  map f := stableSystemMap f d
  map_id E := stableSystemMap_id E d
  map_comp f g := stableSystemMap_comp f g d

/-- The actual integer-graded stable homotopy group functor. -/
def stableHomotopyFunctor (d : ℤ) : LoopPrespectrum.{u} ⥤ AddCommGrpCat.{u} :=
  stableSystemFunctor d ⋙ colim

/-- The original stable stage inclusion commutes with the actual induced stable map. -/
theorem stableHomotopyι_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (d : ℤ) (n : ℕ) :
    stableHomotopyι E d n ≫ (stableHomotopyFunctor d).map f =
      (stableSystemMap f d).app n ≫ stableHomotopyι F d n :=
  ι_colimMap (stableSystemMap f d) n

/-- The entire coherent prespectrum homotopy induces equal original stable maps. -/
theorem Homotopy.stableHomotopyMap_eq {E F : LoopPrespectrum.{u}} {f g : E ⟶ F} (H : Homotopy f
    g) (d : ℤ) :
    (stableHomotopyFunctor d).map f = (stableHomotopyFunctor d).map g := by
  apply congrArg colimMap
  apply NatTrans.ext
  funext n
  apply AddCommGrpCat.ext
  intro a
  exact congrFun (H.homotopyGroupMap_eq ((-d).toNat+n+2) (d.toNat+n+2)) a

end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum

/-- Equality of levels gives the literal transport on the original homotopy groups. -/
def levelPiAddEquiv (E : LoopPrespectrum.{u}) (n : ℕ) {i j : ℕ} (h : i = j) :
    Additive (HomotopyGroup.Pi (n+2) (E.space i) (E.point i)) ≃+
      Additive (HomotopyGroup.Pi (n+2) (E.space j) (E.point j)) := by
  subst j
  exact AddEquiv.refl _

theorem levelPiAddEquiv_naturality {E G : LoopPrespectrum.{u}}
    (f : E ⟶ G) (n : ℕ) {i j : ℕ} (h : i = j)
    (a : HomotopyGroup.Pi (n + 2) (E.space i) (E.point i)) :
    levelPiAddEquiv G n h (Additive.ofMul (HomotopyGroup.piMap (n+1) (f.map i) (f.map_point i) a)) =
      Additive.ofMul (HomotopyGroup.piMap (n+1) (f.map j) (f.map_point j)
        (Additive.toMul (levelPiAddEquiv E n h (Additive.ofMul a)))) := by
  subst j
  rfl

/-- The nonnegative degree system starts at the literal second spectrum space. -/
def nonnegativeStableStageEquiv (E : LoopPrespectrum.{u}) (n : ℕ) :
    Additive (HomotopyGroup.Pi (n+2) (E.space 2) (E.point 2)) ≃+
      (stableSystem E (n : ℤ)).obj 0 :=
  levelPiAddEquiv E n (by omega)

/-- Normalization is natural for the actual second-level homotopy map. -/
theorem nonnegativeStableStageEquiv_naturality {E G : LoopPrespectrum.{u}}
    (f : E ⟶ G) (n : ℕ) (a : HomotopyGroup.Pi (n + 2) (E.space 2) (E.point 2)) :
    nonnegativeStableStageEquiv G n (Additive.ofMul (HomotopyGroup.piMap (n+1) (f.map 2)
      (f.map_point 2) a)) =
      (stableSystemMap f (n : ℤ)).app 0 (nonnegativeStableStageEquiv E n (Additive.ofMul a)) :=
  levelPiAddEquiv_naturality f n (by omega) a

end Topology.LoopPrespectrum
