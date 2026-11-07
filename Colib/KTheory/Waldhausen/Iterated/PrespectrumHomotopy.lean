/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.StructureHomotopy
public import Colib.KTheory.Waldhausen.Iterated.ExactMaps
public import Colib.Topology.Prespectrum.Homotopy

/-! Whole structure-compatible based prespectrum homotopies from weak natural transformations,
in the original independent object and morphism universes. -/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/PrespectrumHomotopy.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete based tracks,
structure-map parameters and universe assumptions are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

/-- The actual zeroth-level loop homotopy, with the whole basepoint track fixed. -/
def transformationLoopHomotopy {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) :
    C(unitInterval × Path (stagePoint 0 V) (stagePoint 0 V), Path (stagePoint 0 W) (stagePoint 0
      W)) where
  toFun z :=
    { toFun t := stageTransformationTopHomotopy 0 η hη (z.1,z.2 t)
      continuous_toFun := by fun_prop
      source' := by
        rw [Path.source]
        exact stageTransformationTopHomotopy_fixed_point 0 η hη z.1
      target' := by
        rw [Path.target]
        exact stageTransformationTopHomotopy_fixed_point 0 η hη z.1 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (stageTransformationTopHomotopy 0 η hη).continuous.comp
      (continuous_fst.fst.prodMk ((Path.continuous_uncurry_iff.mpr continuous_id).comp
        (continuous_fst.snd.prodMk continuous_snd)))

/-- A genuine weak natural transformation gives a coherent homotopy of the entire
original prespectrum, retaining the original structure maps at every time. -/
def prespectrumTransformationHomotopy {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) :
    LoopPrespectrum.Homotopy (prespectrumMap F) (prespectrumMap G) where
  level n := Nat.casesOn n (transformationLoopHomotopy η hη)
    (fun r ↦ (stageTransformationTopHomotopy r η hη).toContinuousMap)
  at_zero n x := by
    cases n with
    | zero =>
      change Path (stagePoint 0 V) (stagePoint 0 V) at x
      apply Path.ext
      funext t
      exact (stageTransformationTopHomotopy 0 η hη).apply_zero (x t)
    | succ r => exact (stageTransformationTopHomotopy r η hη).apply_zero x
  at_one n x := by
    cases n with
    | zero =>
      change Path (stagePoint 0 V) (stagePoint 0 V) at x
      apply Path.ext
      funext t
      exact (stageTransformationTopHomotopy 0 η hη).apply_one (x t)
    | succ r => exact (stageTransformationTopHomotopy r η hη).apply_one x
  at_point n s := by
    cases n with
    | zero =>
      apply Path.ext
      funext t
      exact stageTransformationTopHomotopy_fixed_point 0 η hη s
    | succ r => exact stageTransformationTopHomotopy_fixed_point r η hη s
  comm n s x t := by
    cases n with
    | zero => rfl
    | succ r => exact stageTransformationTopHomotopy_structure r η hη s t x

section OriginalUniverses
universe u₀ v₀
variable {C D : Type u₀} [Category.{v₀} C] [Category.{v₀} D]
  (W : Structure C) (V : Structure D) {F G : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)

/-- Actual original-universe transformations retain the complete coherent homotopy. -/
def originalPrespectrumTransformationHomotopy
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) :
    LoopPrespectrum.Homotopy (originalPrespectrumMap W V hF h0F)
      (originalPrespectrumMap W V hG h0G) :=
  prespectrumTransformationHomotopy
    (F := asSmallCategoryMap W V hF h0F) (G := asSmallCategoryMap W V hG h0G)
    (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (fun A ↦ hη (AsSmall.down.obj A))

/-- No chosen-zero-image hypothesis is required: the canonical conjugation of the
original transformation gives a genuine homotopy of the actual spectrum maps. -/
def exactOriginalPrespectrumHomotopy (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) :
    LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W V hF)
      (exactOriginalPrespectrumMap W V hG) :=
  originalPrespectrumTransformationHomotopy W V hF.rebase hG.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    (normalizedWeakTransformation hF hG η) (normalizedWeakTransformation_weak hF hG η hη)

/-- A natural isomorphism supplies the actual coherent spectrum homotopy. -/
def exactOriginalPrespectrumIsoHomotopy (e : F ≅ G) :
    LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W V hF)
      (exactOriginalPrespectrumMap W V hG) :=
  exactOriginalPrespectrumHomotopy W V hF hG e.hom (fun _A ↦ V.weq_iso _ inferInstance)

end OriginalUniverses
end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0277"]
  CategoryTheory.Waldhausen.IteratedS.prespectrumTransformationHomotopy
  CategoryTheory.Waldhausen.IteratedS.exactOriginalPrespectrumIsoHomotopy

attribute [colib_tag "COL-0277",
  colib_ref "ThomasonTrobaugh1990" "Section 1.5.4, pp. 260-261" "background"
    "Weak-transformation homotopy background; full structure-compatible tracks are explicit"]
  CategoryTheory.Waldhausen.IteratedS.exactOriginalPrespectrumHomotopy
