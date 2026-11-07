/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.ParameterLooping
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.TransposeSign
public import Colib.CategoryTheory.Limits.Shapes.SequentialSystem.SignCorrection
public import Colib.CategoryTheory.Limits.Shapes.SequentialSystem.TailColimit
public import Colib.Topology.Prespectrum.StableHomotopy

/-!
The actual integer-graded stable loop shift includes its proved coordinate sign, alternating
original stage maps, genuine tail reindexing and original-map naturality. No Omega-spectrum premise
is used.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StableShift.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native prespectrum,
integer degrees, original structure maps, coefficients and signs are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

/-- The original loop shift anti-commutes with the actual parameter-correct
prespectrum structure map. -/
theorem parameterLooping_structurePiMap_sign (E : LoopPrespectrum.{u}) (n k : ℕ)
    (a : HomotopyGroup.Pi (k + 1) (Path (E.point n) (E.point n)) (Path.refl (E.point n))) :
    (loopShiftMulEquiv (x := E.point (n+1)) (k+1)).symm
      (structurePiMap (parameterLooping E) n k a) =
    (structurePiMap E n (k+1)
      ((loopShiftMulEquiv (x := E.point n) k).symm a))⁻¹ := by
  exact loopShift_parameter_structure_sign (k+1) (E.structureMap n) (E.map_point n)
    (Path.doubleLoopTranspose (E.point (n+1))) (Path.doubleLoopTranspose_refl _)
    (fun _ _ _ ↦ rfl) a

/-- The actual shifted-degree stages at the original, unchanged spectrum levels. -/
def shiftedStableStage (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) : CommGrpCat.{u} :=
  CommGrpCat.of (HomotopyGroup.Pi (d.toNat+n+3)
    (E.space ((-d).toNat+n+2)) (E.point ((-d).toNat+n+2)))

/-- The shifted diagram retains the original spectrum structure transitions. -/
def shiftedStableTransition (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) :
    shiftedStableStage E d n ⟶ shiftedStableStage E d (n+1) :=
  CommGrpCat.ofHom (structurePiMap E ((-d).toNat+n+2) (d.toNat+n+2))

/-- The sequential system comparing parameter looping with the stable degree shift. -/
def shiftedStableSystem (E : LoopPrespectrum.{u}) (d : ℤ) : ℕ ⥤ AddCommGrpCat.{u} :=
  Functor.ofSequence (shiftedStableTransition E d) ⋙ CommGrpCat.toAddCommGrp

/-- The genuine stagewise loop degree shift, before its alternating sign correction. -/
def parameterStableStageIso (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) :
    (stableSystem (parameterLooping E) d).obj n ≅ (shiftedStableSystem E d).obj n :=
  AddEquiv.toAddCommGrpIso
    (loopShiftMulEquiv (x := E.point ((-d).toNat+n+2)) (d.toNat+n+1)).symm.toAdditive

/-- The original stagewise isomorphisms anti-commute with the two genuine successor maps. -/
theorem parameterStableStageIso_anticomm (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) :
    (stableSystem (parameterLooping E) d).map (homOfLE (Nat.le_succ n)) ≫
        (parameterStableStageIso E d (n+1)).hom =
      -((parameterStableStageIso E d n).hom ≫
        (shiftedStableSystem E d).map (homOfLE (Nat.le_succ n))) := by
  simp only [stableSystem, shiftedStableSystem, Functor.comp_map,
    Functor.ofSequence_map_homOfLE_succ]
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul
    (parameterLooping_structurePiMap_sign E ((-d).toNat+n+2) (d.toNat+n+1) (Additive.toMul a))

/-- Alternating actual stage inversions produce a genuine natural isomorphism
from the parameter-loop stable diagram to the shifted original diagram. -/
def parameterStableSystemIso (E : LoopPrespectrum.{u}) (d : ℤ) :
    stableSystem (parameterLooping E) d ≅ shiftedStableSystem E d :=
  SequentialSystem.signCorrectionIso (parameterStableStageIso E d)
    (parameterStableStageIso_anticomm E d)

/-- The actual colimit comparison before identifying the integer-degree indexing. -/
def parameterStableShiftedColimitIso (E : LoopPrespectrum.{u}) (d : ℤ) :
    stableHomotopyGroup (parameterLooping E) d ≅ colimit (shiftedStableSystem E d) :=
  HasColimit.isoOfNatIso (parameterStableSystemIso E d)

/-- Simultaneous genuine transports of the original positive homotopy degree and level. -/
def degreeLevelPiAddEquiv (E : LoopPrespectrum.{u}) {k l i j : ℕ}
    (hk : k = l) (hi : i = j) :
    Additive (HomotopyGroup.Pi (k+2) (E.space i) (E.point i)) ≃+
      Additive (HomotopyGroup.Pi (l+2) (E.space j) (E.point j)) := by
  subst l
  subst j
  exact AddEquiv.refl _

lemma degreeLevelPiAddEquiv_structure (E : LoopPrespectrum.{u}) {k l i j : ℕ}
    (hk : k = l) (hi : i = j)
    (a : Additive (HomotopyGroup.Pi (k + 2) (E.space i) (E.point i))) :
    (degreeLevelPiAddEquiv E (congrArg (·+1) hk) (congrArg (·+1) hi)).toFun
      (Additive.ofMul (structurePiMap E i (k+1) (Additive.toMul a))) =
    Additive.ofMul (structurePiMap E j (l+1)
      (Additive.toMul ((degreeLevelPiAddEquiv E hk hi).toFun a))) := by
  subst l
  subst j
  rfl

/-- Negative input degrees require the actual one-stage tail in the target system. -/
def parameterStableOffset (d : ℤ) : ℕ := if d < 0 then 1 else 0

lemma parameterStable_degree (d : ℤ) (n : ℕ) :
    d.toNat+n+1 = (d+1).toNat+(parameterStableOffset d+n) := by
  unfold parameterStableOffset
  split_ifs <;> omega

lemma parameterStable_level (d : ℤ) (n : ℕ) :
    (-d).toNat+n+2 = (-(d+1)).toNat+(parameterStableOffset d+n)+2 := by
  unfold parameterStableOffset
  split_ifs <;> omega

/-- The integer reindexing retains the original spectrum level and homotopy degree. -/
def shiftedStableReindexIso (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) :
    (shiftedStableSystem E d).obj n ≅
      (SequentialSystem.shiftFunctor (parameterStableOffset d) ⋙ stableSystem E (d+1)).obj n :=
  (degreeLevelPiAddEquiv E (parameterStable_degree d n) (parameterStable_level d n)).toAddCommGrpIso

lemma shiftedStableReindexIso_naturality (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) :
    (shiftedStableSystem E d).map (homOfLE (Nat.le_succ n)) ≫
        (shiftedStableReindexIso E d (n+1)).hom =
      (shiftedStableReindexIso E d n).hom ≫
        (SequentialSystem.shiftFunctor (parameterStableOffset d) ⋙ stableSystem E (d+1)).map
          (homOfLE (Nat.le_succ n)) := by
  simp only [shiftedStableSystem, stableSystem, Functor.comp_map,
    SequentialSystem.shiftFunctor, Monotone.functor]
  simp only [Functor.ofSequence_map_homOfLE_succ]
  apply AddCommGrpCat.ext
  intro a
  exact degreeLevelPiAddEquiv_structure E (parameterStable_degree d n) (parameterStable_level d n) a

/-- The shifted actual diagram is the original diagram in degree d+1 after its
proved finite tail, without changing any transition map. -/
def shiftedStableSystemIso (E : LoopPrespectrum.{u}) (d : ℤ) :
    shiftedStableSystem E d ≅
      SequentialSystem.shiftFunctor (parameterStableOffset d) ⋙ stableSystem E (d+1) := by
  let η : shiftedStableSystem E d ⟶
      SequentialSystem.shiftFunctor (parameterStableOffset d) ⋙ stableSystem E (d+1) :=
    NatTrans.ofSequence (fun n ↦ (shiftedStableReindexIso E d n).hom)
      (shiftedStableReindexIso_naturality E d)
  exact NatIso.ofComponents (shiftedStableReindexIso E d) (fun {_ _} f ↦ η.naturality f)

/-- Actual integer-graded stable loop shift, with the coordinate sign correction
and genuine final-tail colimit comparison both included. -/
def parameterStableHomotopyIso (E : LoopPrespectrum.{u}) (d : ℤ) :
    stableHomotopyGroup (parameterLooping E) d ≅ stableHomotopyGroup E (d+1) :=
  parameterStableShiftedColimitIso E d ≪≫
    HasColimit.isoOfNatIso (shiftedStableSystemIso E d) ≪≫
    SequentialSystem.tailColimitIso (stableSystem E (d+1)) (parameterStableOffset d)

end Topology.LoopPrespectrum

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

/-- The constructed integer shift keeps the actual colimit stage inclusion,
including its displayed sign and actual reindexing. -/
@[reassoc] theorem parameterStableHomotopyIso_ι_hom (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) :
    stableHomotopyι (parameterLooping E) d n ≫ (parameterStableHomotopyIso E d).hom =
      (SequentialSystem.alternatingIso n (parameterStableStageIso E d n)).hom ≫
        (shiftedStableReindexIso E d n).hom ≫
          stableHomotopyι E (d+1) (parameterStableOffset d+n) := by
  simp [parameterStableHomotopyIso, parameterStableShiftedColimitIso,
    stableHomotopyι, parameterStableSystemIso, shiftedStableSystemIso,
    SequentialSystem.signCorrectionIso]

/-- The reverse comparison retains the same original stage map, rather than an
unspecified stable equivalence. -/
@[reassoc] theorem parameterStableHomotopyIso_ι_inv (E : LoopPrespectrum.{u}) (d : ℤ) (n : ℕ) :
    (SequentialSystem.alternatingIso n (parameterStableStageIso E d n)).hom ≫
      (shiftedStableReindexIso E d n).hom ≫
        stableHomotopyι E (d+1) (parameterStableOffset d+n) ≫
          (parameterStableHomotopyIso E d).inv = stableHomotopyι (parameterLooping E) d n := by
  rw [← parameterStableHomotopyIso_ι_hom_assoc, Iso.hom_inv_id, Category.comp_id]

lemma degreeLevelPiAddEquiv_map {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    {k l i j : ℕ} (hk : k = l) (hi : i = j)
    (a : Additive (HomotopyGroup.Pi (k + 2) (E.space i) (E.point i))) :
    (degreeLevelPiAddEquiv F hk hi).toFun
      (Additive.ofMul (HomotopyGroup.piMap (k+1) (f.map i) (f.map_point i) (Additive.toMul a))) =
    Additive.ofMul (HomotopyGroup.piMap (l+1) (f.map j) (f.map_point j)
      (Additive.toMul ((degreeLevelPiAddEquiv E hk hi).toFun a))) := by
  subst l
  subst j
  rfl

/-- The unchanged original spectrum map on the shifted stages. -/
def shiftedStableStageMap {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (d : ℤ) (n : ℕ) :
    (shiftedStableSystem E d).obj n ⟶ (shiftedStableSystem F d).obj n :=
  AddCommGrpCat.ofHom (HomotopyGroup.piMap (d.toNat+n+2) (f.map ((-d).toNat+n+2))
    (f.map_point ((-d).toNat+n+2))).toAdditive

lemma parameterStableStageIso_map {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (d : ℤ) (n : ℕ) :
    (stableSystemMap (parameterLoopingMap f) d).app n ≫ (parameterStableStageIso F d n).hom =
      (parameterStableStageIso E d n).hom ≫ shiftedStableStageMap f d n := by
  apply AddCommGrpCat.ext
  intro a
  change Additive.ofMul ((loopShiftMulEquiv (x := F.point ((-d).toNat+n+2)) (d.toNat+n+1)).symm
    (HomotopyGroup.piMap (d.toNat+n+1) (basedLoopMap (f.map ((-d).toNat+n+2))
      (f.map_point ((-d).toNat+n+2)))
      (basedLoopMap_refl _ _) (Additive.toMul a))) =
    Additive.ofMul (HomotopyGroup.piMap (d.toNat+n+2) (f.map ((-d).toNat+n+2))
      (f.map_point ((-d).toNat+n+2))
      ((loopShiftMulEquiv (x := E.point ((-d).toNat+n+2)) (d.toNat+n+1)).symm (Additive.toMul a)))
  refine Quotient.inductionOn (Additive.toMul a) (fun p ↦ ?_)
  exact congrArg (fun q ↦ Additive.ofMul (Quotient.mk' q : HomotopyGroup.Pi (d.toNat+n+3)
      (F.space ((-d).toNat+n+2)) (F.point ((-d).toNat+n+2))))
    (loopUncurry_postcomp (f.map ((-d).toNat+n+2)) (f.map_point ((-d).toNat+n+2)) p)

lemma shiftedStableReindexIso_map {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (d : ℤ) (n : ℕ) :
    shiftedStableStageMap f d n ≫ (shiftedStableReindexIso F d n).hom =
      (shiftedStableReindexIso E d n).hom ≫
        (stableSystemMap f (d+1)).app (parameterStableOffset d+n) := by
  apply AddCommGrpCat.ext
  intro a
  exact degreeLevelPiAddEquiv_map f (parameterStable_degree d n) (parameterStable_level d n) a

@[reassoc] lemma parameterStable_correctedStage_map {E F : LoopPrespectrum.{u}}
    (f : E ⟶ F) (d : ℤ) (n : ℕ) :
    (stableSystemMap (parameterLoopingMap f) d).app n ≫
        (SequentialSystem.alternatingIso n (parameterStableStageIso F d n)).hom ≫
          (shiftedStableReindexIso F d n).hom
          =
      (SequentialSystem.alternatingIso n (parameterStableStageIso E d n)).hom ≫
        (shiftedStableReindexIso E d n).hom ≫
        (stableSystemMap f (d+1)).app (parameterStableOffset d+n) := by
  have h : (stableSystemMap (parameterLoopingMap f) d).app n ≫
      (parameterStableStageIso F d n).hom ≫ (shiftedStableReindexIso F d n).hom =
    (parameterStableStageIso E d n).hom ≫ (shiftedStableReindexIso E d n).hom ≫
      (stableSystemMap f (d+1)).app (parameterStableOffset d+n) := by
    rw [← Category.assoc, parameterStableStageIso_map, Category.assoc, shiftedStableReindexIso_map]
  simpa only [SequentialSystem.alternatingIso_hom, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp] using
    congrArg (fun h ↦ (-1 : ℤ)^n • h) h

/-- Naturality is for the unchanged original stable-group maps in all integer degrees. -/
theorem parameterStableHomotopyIso_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (d : ℤ) :
    (stableHomotopyFunctor d).map (parameterLoopingMap f) ≫ (parameterStableHomotopyIso F d).hom =
      (parameterStableHomotopyIso E d).hom ≫ (stableHomotopyFunctor (d+1)).map f := by
  apply colimit.hom_ext
  intro n
  change stableHomotopyι (parameterLooping E) d n ≫
      ((stableHomotopyFunctor d).map (parameterLoopingMap f) ≫ (parameterStableHomotopyIso F d).hom)
        =
    stableHomotopyι (parameterLooping E) d n ≫
      ((parameterStableHomotopyIso E d).hom ≫ (stableHomotopyFunctor (d+1)).map f)
  rw [← Category.assoc, stableHomotopyι_naturality, Category.assoc,
    parameterStableHomotopyIso_ι_hom, parameterStable_correctedStage_map_assoc]
  rw [← stableHomotopyι_naturality, ← parameterStableHomotopyIso_ι_hom_assoc]

/-- The inverse naturality equation keeps the original connecting-map orientation. -/
theorem parameterStableHomotopyIso_inv_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (d : ℤ) :
    (parameterStableHomotopyIso E d).inv ≫ (stableHomotopyFunctor d).map (parameterLoopingMap f) =
      (stableHomotopyFunctor (d+1)).map f ≫ (parameterStableHomotopyIso F d).inv := by
  apply (cancel_mono (parameterStableHomotopyIso F d).hom).mp
  rw [Category.assoc, parameterStableHomotopyIso_naturality,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Topology.LoopPrespectrum
