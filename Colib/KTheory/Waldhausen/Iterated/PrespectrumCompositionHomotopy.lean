/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.TriangleComposition
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopy
public import Colib.Topology.Prespectrum.RelativeHomotopy
public import Colib.Topology.Prespectrum.HomotopyComposition

/-!
# Relative composition coherence of original prespectrum transformation homotopies

The genuine stage triangles lift to an actual whole two-parameter prespectrum comparison. The
zero level is constructed explicitly on the original based loop space. All endpoints, basepoints,
and the independent original structure coordinate are retained.
-/
/-! Implementation provenance:
  `Quillen/Waldhausen/SConstruction/Iterated/PrespectrumCompositionHomotopy.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, simplex faces,
whole fixed-zero family, and independent structure parameters are retained under native ownership.
  -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

variable {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
  (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))

/-- The actual degree-zero loop family evaluates the whole stage comparison pointwise. -/
def transformationCompositionLoopFamily :
    C(unitInterval × (unitInterval × Path (stagePoint 0 V) (stagePoint 0 V)),
      Path (stagePoint 0 W) (stagePoint 0 W)) where
  toFun z :=
    { toFun q := stageTransformationCompositionHomotopy η θ hη hθ 0
        (z.1, (z.2.1, z.2.2 q))
      continuous_toFun := by fun_prop
      source' := by
        rw [Path.source]
        exact stageTransformationCompositionHomotopy_fixed_point η θ hη hθ 0 z.1 z.2.1
      target' := by
        rw [Path.target]
        exact stageTransformationCompositionHomotopy_fixed_point η θ hη hθ 0 z.1 z.2.1 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z :
      (unitInterval × (unitInterval × Path (stagePoint 0 V) (stagePoint 0 V))) × unitInterval ↦
      stageTransformationCompositionHomotopy η θ hη hθ 0 (z.1.1, (z.1.2.1, z.1.2.2 z.2)))
    fun_prop

/-- Degree zero retains the two homotopy endpoints and the entire based-loop line. -/
def transformationCompositionLoopHomotopy :
    ((prespectrumTransformationHomotopy (η ≫ θ)
      (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A))).level 0).HomotopyRel
      (((prespectrumTransformationHomotopy η hη).trans
        (prespectrumTransformationHomotopy θ hθ)).level 0)
      (fun z : unitInterval × (prespectrum V).space 0 ↦
        z.1 = 0 ∨ z.1 = 1 ∨ z.2 = (prespectrum V).point 0) where
  toFun := transformationCompositionLoopFamily η θ hη hθ
  continuous_toFun := (transformationCompositionLoopFamily η θ hη hθ).continuous
  map_zero_left z := by
    change unitInterval × Path (stagePoint 0 V) (stagePoint 0 V) at z
    apply Path.ext
    funext q
    exact (stageTransformationCompositionHomotopy η θ hη hθ 0).apply_zero (z.1, z.2 q)
  map_one_left z := by
    change unitInterval × Path (stagePoint 0 V) (stagePoint 0 V) at z
    apply Path.ext
    funext q
    change stageTransformationCompositionHomotopy η θ hη hθ 0 (1, (z.1, z.2 q)) = _
    rw [(stageTransformationCompositionHomotopy η θ hη hθ 0).apply_one]
    change ((stageTransformationTopHomotopy 0 η hη).trans
      (stageTransformationTopHomotopy 0 θ hθ)) (z.1, z.2 q) =
      (show Path (stagePoint 0 W) (stagePoint 0 W) from
        (((prespectrumTransformationHomotopy η hη).levelHomotopy 0).trans
          ((prespectrumTransformationHomotopy θ hθ).levelHomotopy 0)) z) q
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split_ifs <;> rfl
  prop' s z hz := by
    change unitInterval × Path (stagePoint 0 V) (stagePoint 0 V) at z
    apply Path.ext
    funext q
    change stageTransformationCompositionHomotopy η θ hη hθ 0 (s, (z.1, z.2 q)) = _
    apply (stageTransformationCompositionHomotopy η θ hη hθ 0).eq_fst
    rcases hz with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by rw [h]; rfl))

/-- The original composite-transformation homotopy and concatenation are genuinely relatively
homotopic as whole prespectrum homotopies. -/
def prespectrumTransformationCompositionHomotopy :
    (prespectrumTransformationHomotopy (η ≫ θ)
      (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A))).RelHomotopy
      ((prespectrumTransformationHomotopy η hη).trans
        (prespectrumTransformationHomotopy θ hθ)) where
  level n := Nat.casesOn n (transformationCompositionLoopHomotopy η θ hη hθ)
    (fun r ↦ stageTransformationCompositionHomotopy η θ hη hθ r)
  comm n s t x q := by
    cases n with
    | zero => rfl
    | succ r => exact stageTransformationCompositionHomotopy_structure η θ hη hθ r s t q x

/-- Every positive level retains the original actual stage comparison. -/
@[simp]
theorem prespectrumTransformationCompositionHomotopy_succ
    (r : ℕ) (s t : unitInterval) (x : stageSpace r V) :
    (prespectrumTransformationCompositionHomotopy η θ hη hθ).level (r + 1) (s, (t, x)) =
      stageTransformationCompositionHomotopy η θ hη hθ r (s, (t, x)) := rfl

/-- At level zero the original loop coordinate remains independent of both homotopy times. -/
@[simp]
theorem prespectrumTransformationCompositionHomotopy_zero_apply
    (s t q : unitInterval) (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      (prespectrumTransformationCompositionHomotopy η θ hη hθ).level 0 (s, (t, γ))) q =
      stageTransformationCompositionHomotopy η θ hη hθ 0 (s, (t, γ q)) := rfl

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0277"]
  CategoryTheory.Waldhausen.IteratedS.prespectrumTransformationCompositionHomotopy
  CategoryTheory.Waldhausen.IteratedS.prespectrumTransformationCompositionHomotopy_succ
  CategoryTheory.Waldhausen.IteratedS.prespectrumTransformationCompositionHomotopy_zero_apply
