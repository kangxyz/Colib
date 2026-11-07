/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.FunctorChain
public import Colib.Topology.HomotopyFiber.Nullhomotopy

/-!
# Actual moving-source homotopies between categorical fiber lifts

## Implementation provenance

Adapted from `Quillen/CategoryTheory/TheoremB/NaturalTransformationFiberLift.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology SSet HomotopyGroup
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace CategoryTheory.TheoremB
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {A C D : Type u} [SmallCategory A] [SmallCategory C] [SmallCategory D]

/-- Join a moving point of the first edge to the terminal vertex of the actual triangle. -/
def sourceTriangleParameter (s t : unitInterval) : Convexity.StdSimplex ℝ (Fin 3) :=
  Convexity.convexCombPair (R := ℝ) (unitInterval.symm t) t
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp)
    (triangleEdge 0 1 s) (Convexity.StdSimplex.single 2)

/-- The source triangle retains the original affine weights at every vertex. -/
@[simp] theorem sourceTriangleParameter_apply (s t : unitInterval) (i : Fin 3) :
    (sourceTriangleParameter s t).weights i =
      ![(1 - (t : ℝ)) * (1 - (s : ℝ)), (1 - (t : ℝ)) * s, (t : ℝ)] i := by
  fin_cases i <;>
    simp [sourceTriangleParameter, Convexity.StdSimplex.weights_convexCombPair,
      triangleEdge, Convexity.StdSimplex.duple, unitInterval.coe_symm_eq]

@[fun_prop] theorem continuous_sourceTriangleParameter :
    Continuous (fun z : unitInterval × unitInterval ↦ sourceTriangleParameter z.1 z.2) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).continuous_iff]
  unfold Function.comp
  refine continuous_pi (fun i ↦ ?_)
  simp only [sourceTriangleParameter_apply]
  fin_cases i <;> dsimp <;> fun_prop

/-- The initial source gives the composite edge. -/
lemma sourceTriangleParameter_zero (t : unitInterval) :
    sourceTriangleParameter 0 t = triangleEdge 0 2 t := by
  apply Convexity.StdSimplex.ext
  ext i
  fin_cases i <;> simp

/-- The terminal source gives the final edge. -/
lemma sourceTriangleParameter_one (t : unitInterval) :
    sourceTriangleParameter 1 t = triangleEdge 1 2 t := by
  apply Convexity.StdSimplex.ext
  ext i
  fin_cases i <;> simp

/-- The initial endpoint is the genuine moving-source edge. -/
lemma sourceTriangleParameter_source (s : unitInterval) :
    sourceTriangleParameter s 0 = triangleEdge 0 1 s := by
  simp [sourceTriangleParameter]

/-- The terminal endpoint remains the original terminal vertex. -/
lemma sourceTriangleParameter_target (s : unitInterval) :
    sourceTriangleParameter s 1 = Convexity.StdSimplex.single 2 := by
  simp [sourceTriangleParameter]

/-- The direct nullhomotopy of an actual transformation to the constant functor. -/
def naturalTransformationNullhomotopy (P : A ⥤ C) (F : C ⥤ D) (d : D)
    (ε : P ⋙ F ⟶ (Functor.const A).obj d) :
    ((classifyingSpaceMap F).hom.comp (classifyingSpaceMap P).hom).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint d)) :=
  (classifyingSpaceNaturalTransformationHomotopy ε).cast
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
    (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- The original fiber lift supplied by a transformation to the specified base object. -/
def naturalTransformationFiberLift (P : A ⥤ C) (F : C ⥤ D) (d : D)
    (ε : P ⋙ F ⟶ (Functor.const A).obj d) :
    C(ClassifyingSpace A, HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  HomotopyFiber.lift _ _ (classifyingSpaceMap P).hom
    (naturalTransformationNullhomotopy P F d ε)

/-- An actual transformation of source functors moves the source coordinate along its
original realization track while the two-simplex supplies the entire remaining fiber path. -/
def naturalTransformationFiberHomotopy {P Q : A ⥤ C} (τ : P ⟶ Q)
    (F : C ⥤ D) (d : D) (ε : Q ⋙ F ⟶ (Functor.const A).obj d) :
    (naturalTransformationFiberLift P F d (Functor.whiskerRight τ F ≫ ε)).Homotopy
      (naturalTransformationFiberLift Q F d ε) where
  toFun z :=
    ⟨(classifyingSpaceNaturalTransformationHomotopy τ z,
      ⟨fun t ↦ functorChainBarycentric (ComposableArrows.mk₂ (Functor.whiskerRight τ F) ε)
        (z.2, sourceTriangleParameter z.1 t), by fun_prop⟩), by
      change functorChainBarycentric
        (ComposableArrows.mk₂ (Functor.whiskerRight τ F) ε)
          (z.2, sourceTriangleParameter z.1 0) = _
      rw [sourceTriangleParameter_source, functorChainBarycentric_two_first,
        classifyingSpaceNaturalTransformationHomotopy_whiskerRight], by
      change functorChainBarycentric
        (ComposableArrows.mk₂ (Functor.whiskerRight τ F) ε)
          (z.2, sourceTriangleParameter z.1 1) = _
      rw [sourceTriangleParameter_target, ← triangleEdge_one 1 2,
        functorChainBarycentric_two_second]
      rw [(classifyingSpaceNaturalTransformationHomotopy ε).apply_one]
      exact ConcreteCategory.congr_hom (classifyingSpaceMap_const_direct _) z.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (classifyingSpaceNaturalTransformationHomotopy τ).continuous
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (unitInterval × ClassifyingSpace A) × unitInterval ↦
        functorChainBarycentric (ComposableArrows.mk₂ (Functor.whiskerRight τ F) ε)
          (z.1.2, sourceTriangleParameter z.1.1 z.2))
      fun_prop
  map_zero_left x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (classifyingSpaceNaturalTransformationHomotopy τ).apply_zero x
    · apply ContinuousMap.ext
      intro t
      change functorChainBarycentric
        (ComposableArrows.mk₂ (Functor.whiskerRight τ F) ε)
          (x, sourceTriangleParameter 0 t) = _
      rw [sourceTriangleParameter_zero, functorChainBarycentric_two_composite]
      rfl
  map_one_left x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (classifyingSpaceNaturalTransformationHomotopy τ).apply_one x
    · apply ContinuousMap.ext
      intro t
      change functorChainBarycentric
        (ComposableArrows.mk₂ (Functor.whiskerRight τ F) ε)
          (x, sourceTriangleParameter 1 t) = _
      rw [sourceTriangleParameter_one, functorChainBarycentric_two_second]
      rfl

/-- The moving source is precisely the original transformation track. -/
theorem naturalTransformationFiberHomotopy_source {P Q : A ⥤ C} (τ : P ⟶ Q)
    (F : C ⥤ D) (d : D) (ε : Q ⋙ F ⟶ (Functor.const A).obj d)
    (t : unitInterval) (x : ClassifyingSpace A) :
    (naturalTransformationFiberHomotopy τ F d ε (t, x)).val.1 =
      classifyingSpaceNaturalTransformationHomotopy τ (t, x) := rfl

/-- The entire path is the genuine original two-simplex family. -/
theorem naturalTransformationFiberHomotopy_path {P Q : A ⥤ C} (τ : P ⟶ Q)
    (F : C ⥤ D) (d : D) (ε : Q ⋙ F ⟶ (Functor.const A).obj d)
    (s t : unitInterval) (x : ClassifyingSpace A) :
    (naturalTransformationFiberHomotopy τ F d ε (s, x)).val.2 t =
      functorChainBarycentric (ComposableArrows.mk₂ (Functor.whiskerRight τ F) ε)
        (x, sourceTriangleParameter s t) := rfl

end CategoryTheory.TheoremB
