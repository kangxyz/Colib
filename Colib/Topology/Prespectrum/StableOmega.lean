/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StableHomotopy
public import Colib.Topology.Homotopy.HomotopyGroup.ZeroDetection
public import Colib.CategoryTheory.Limits.Shapes.SequentialSystem.IsoColimit

/-! # Stable groups of genuine Omega-spectra

The original stage-zero inclusion is invertible because every actual
structure-induced transition is invertible. Connected positive spaces
give vanishing negative stable groups. No telescope or cofiber comparison
is used or asserted.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StableOmega.lean` at
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
include hE

/-- The actual original stable successor is an isomorphism for a proved Omega-spectrum. -/
theorem stableSystem_succ_isIso (d : ℤ) (n : ℕ) :
    IsIso ((stableSystem E d).map (homOfLE (Nat.le_succ n))) := by
  let e : stableStage E d n ≅ stableStage E d (n+1) :=
    (MulEquiv.ofBijective (stableTransition E d n).hom (stableTransition_bijective E hE d
      n)).toCommGrpIso
  have he : e.hom = stableTransition E d n := rfl
  let : IsIso (stableTransition E d n) := by rw [← he]; infer_instance
  change IsIso (CommGrpCat.toAddCommGrp.map ((Functor.ofSequence (stableTransition E d)).map
    (homOfLE (Nat.le_succ n))))
  rw [Functor.ofSequence_map_homOfLE_succ]
  infer_instance

/-- The actual stable colimit of an Omega-spectrum identifies with its original first stage. -/
def stableHomotopyStageZeroIso (d : ℤ) : stableHomotopyGroup E d ≅ (stableSystem E d).obj 0 := by
  letI (n : ℕ) : IsIso ((stableSystem E d).map (homOfLE (Nat.le_succ n))) :=
    stableSystem_succ_isIso E hE d n
  exact SequentialSystem.colimitIsoOfSucc (stableSystem E d)

/-- The displayed isomorphism is the inverse of the original stage-zero inclusion. -/
theorem stableHomotopyι_zero_hom (d : ℤ) :
    stableHomotopyι E d 0 ≫ (stableHomotopyStageZeroIso E hE d).hom = 𝟙 _ := by
  let (n : ℕ) : IsIso ((stableSystem E d).map (homOfLE (Nat.le_succ n))) :=
    stableSystem_succ_isIso E hE d n
  exact SequentialSystem.ι_colimitIsoOfSucc_hom (stableSystem E d) 0

/-- Both original directions are inverses, not only an abstract group equivalence. -/
theorem stableHomotopyStageZeroIso_inv (d : ℤ) :
    (stableHomotopyStageZeroIso E hE d).inv = stableHomotopyι E d 0 := by
  apply (cancel_mono (stableHomotopyStageZeroIso E hE d).hom).mp
  rw [Iso.inv_hom_id, stableHomotopyι_zero_hom E hE d]

end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum
variable (E : LoopPrespectrum.{u}) (hE : E.IsOmega)
include hE

/-- All actual positive-degree structure homomorphisms of an Omega-spectrum are bijective. -/
theorem structurePiMap_bijective (n k : ℕ) : Function.Bijective (structurePiMap E n k) := by
  have hb {y : Path (E.point (n+1)) (E.point (n+1))}
      (h : E.structureMap n (E.point n) = y) :
      Function.Bijective (HomotopyGroup.map (N := Fin (k+1)) (E.structureMap n) h) := by
    cases h
    exact (hE n).homotopy_bijective (E.point n) (k+1)
  exact (loopShiftMulEquiv (x := E.point (n+1)) k).symm.bijective.comp (hb (E.map_point n))

/-- The displayed actual structure homomorphism as a group isomorphism. -/
def structurePiEquiv (n k : ℕ) :
    HomotopyGroup.Pi (k+1) (E.space n) (E.point n) ≃*
      HomotopyGroup.Pi (k+2) (E.space (n+1)) (E.point (n+1)) :=
  MulEquiv.ofBijective (structurePiMap E n k) (structurePiMap_bijective E hE n k)

end Topology.LoopPrespectrum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace Topology.LoopPrespectrum
variable (E : LoopPrespectrum.{u}) (hE : E.IsOmega)
include hE

/-- The actual structure-induced equivalence in every finite homotopy-set degree, including zero. -/
def structureHomotopyEquiv (n k : ℕ) :
    HomotopyGroup.Pi k (E.space n) (E.point n) ≃
      HomotopyGroup.Pi (k+1) (E.space (n+1)) (E.point (n+1)) := by
  have hb {y : Path (E.point (n+1)) (E.point (n+1))}
      (h : E.structureMap n (E.point n) = y) :
      Function.Bijective (HomotopyGroup.map (N := Fin k) (E.structureMap n) h) := by
    cases h
    exact (hE n).homotopy_bijective (E.point n) k
  exact (Equiv.ofBijective (HomotopyGroup.map (E.structureMap n) (E.map_point n))
    (hb (E.map_point n))).trans (loopShiftEquiv k).symm

/-- An Omega-spectrum with connected positive levels has the genuine required level connectivity. -/
theorem homotopyGroup_subsingleton_of_lt
    (hconn : ∀ n, PathConnectedSpace (E.space (n + 1)))
    (k n : ℕ) (hkn : k < n) : Subsingleton (HomotopyGroup.Pi k (E.space n) (E.point n)) := by
  induction k generalizing n with
  | zero =>
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    let := hconn n
    exact subsingleton_homotopyGroup_zero _
  | succ k ih =>
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    let := ih n (by omega)
    exact (structureHomotopyEquiv E hE n k).symm.injective.subsingleton

/-- Negative stable groups vanish by the actual Omega comparison and positive-level connectivity. -/
theorem stableHomotopyGroup_subsingleton_of_neg
    (hconn : ∀ n, PathConnectedSpace (E.space (n + 1))) (d : ℤ) (hd : d < 0) :
    Subsingleton (stableHomotopyGroup E d) := by
  let := homotopyGroup_subsingleton_of_lt E hE hconn (d.toNat+2) ((-d).toNat+2) (by omega)
  let : Subsingleton ((stableSystem E d).obj 0) := inferInstanceAs
    (Subsingleton (Additive (HomotopyGroup.Pi (d.toNat+2) (E.space ((-d).toNat+2)) (E.point
      ((-d).toNat+2)))))
  exact (stableHomotopyStageZeroIso E hE d).addCommGroupIsoToAddEquiv.injective.subsingleton

end Topology.LoopPrespectrum
