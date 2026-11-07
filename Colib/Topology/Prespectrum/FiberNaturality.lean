/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.FiberSequence
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.FiveLemma
public import Colib.Topology.Prespectrum.StableEquivalence

/-! Original strict-square maps of actual fiber prespectra and stable boundaries. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/FiberNaturality.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual fiber coordinates, strict
structure maps, specified whole nullhomotopies, integer grading and connecting signs
are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {A B C : Arrow LoopPrespectrum.{u}}

/-- The levelwise homotopy-fiber map induced by a commutative prespectrum square. -/
def homotopyFiberMap (sq : A ⟶ B) : homotopyFiber A.hom ⟶ homotopyFiber B.hom where
  map n :=
    { toFun z := ⟨(sq.left.map n z.1.1, (sq.right.map n).comp z.1.2),
        by
          change sq.right.map n (z.1.2 0) = B.hom.map n (sq.left.map n z.1.1)
          rw [z.2.1]
          exact congrArg (fun h ↦ h.map n z.1.1) sq.w.symm,
        by
          change sq.right.map n (z.1.2 1) = B.right.point n
          rw [z.2.2, sq.right.map_point]⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.prodMk
        · fun_prop
        · exact (ContinuousMap.continuous_postcomp (sq.right.map n)).comp (by fun_prop) }
  map_point n := by
    apply Subtype.ext
    apply Prod.ext
    · exact sq.left.map_point n
    · apply ContinuousMap.ext
      intro s
      exact sq.right.map_point n
  comm n z := by
    apply Path.ext
    funext t
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun p ↦ p t) (sq.left.comm n z.1.1)
    · apply ContinuousMap.ext
      intro s
      exact congrArg (fun p ↦ p t) (sq.right.comm n (z.1.2 s))

@[simp] theorem homotopyFiberMap_source (sq : A ⟶ B) (n : ℕ)
    (z : (homotopyFiber A.hom).space n) :
    ((homotopyFiberMap sq).map n z).1.1 = sq.left.map n z.1.1 := rfl

@[simp] theorem homotopyFiberMap_path (sq : A ⟶ B) (n : ℕ)
    (z : (homotopyFiber A.hom).space n) (s : unitInterval) :
    ((homotopyFiberMap sq).map n z).1.2 s = sq.right.map n (z.1.2 s) := rfl

/-- The functor assigning a prespectrum map its levelwise homotopy-fiber prespectrum. -/
def homotopyFiberFunctor : Arrow LoopPrespectrum.{u} ⥤ LoopPrespectrum.{u} where
  obj A := homotopyFiber A.hom
  map := homotopyFiberMap
  map_id A := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    rfl
  map_comp sq sq' := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    rfl

theorem homotopyFiberProjection_naturality (sq : A ⟶ B) :
    homotopyFiberMap sq ≫ homotopyFiberProjection B.hom =
      homotopyFiberProjection A.hom ≫ sq.left := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  rfl

theorem homotopyFiberLoopInclusion_naturality (sq : A ⟶ B) :
    parameterLoopingMap sq.right ≫ homotopyFiberLoopInclusion B.hom =
      homotopyFiberLoopInclusion A.hom ≫ homotopyFiberMap sq := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Subtype.ext
  apply Prod.ext
  · exact (sq.left.map_point n).symm
  · rfl

theorem stableFiberConnecting_naturality (sq : A ⟶ B) (d : ℤ) :
    (stableHomotopyFunctor (d+1)).map sq.right ≫ stableFiberConnecting B.hom d =
      stableFiberConnecting A.hom d ≫ (stableHomotopyFunctor d).map (homotopyFiberMap sq) := by
  unfold stableFiberConnecting
  rw [← Category.assoc, ← parameterStableHomotopyIso_inv_naturality]
  rw [Category.assoc, ← Functor.map_comp, homotopyFiberLoopInclusion_naturality,
    Functor.map_comp, Category.assoc]

/-- The original map of fiber prespectra is a stable equivalence when both
original sides of the strict arrow square are stable equivalences. -/
theorem homotopyFiberMap_isStableEquivalence (sq : A ⟶ B)
    (hl : IsStableEquivalence sq.left) (hr : IsStableEquivalence sq.right) :
    IsStableEquivalence (homotopyFiberMap sq) := by
  intro d
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    ((stableHomotopyFunctor (d+1)).map A.hom).hom (stableFiberConnecting A.hom d).hom
    ((stableHomotopyFunctor d).map (homotopyFiberProjection A.hom)).hom
    ((stableHomotopyFunctor d).map A.hom).hom
    ((stableHomotopyFunctor (d+1)).map B.hom).hom (stableFiberConnecting B.hom d).hom
    ((stableHomotopyFunctor d).map (homotopyFiberProjection B.hom)).hom
    ((stableHomotopyFunctor d).map B.hom).hom
    ((stableHomotopyFunctor (d+1)).map sq.left).hom
    ((stableHomotopyFunctor (d+1)).map sq.right).hom
    ((stableHomotopyFunctor d).map (homotopyFiberMap sq)).hom
    ((stableHomotopyFunctor d).map sq.left).hom
    ((stableHomotopyFunctor d).map sq.right).hom
    ?_ ?_ ?_ ?_
    (stableFiberConnecting_exact_target A.hom d)
    (stableFiberConnecting_exact_fiber A.hom d)
    (stableHomotopyFiber_exact_source A.hom d)
    (stableFiberConnecting_exact_target B.hom d)
    (stableFiberConnecting_exact_fiber B.hom d)
    (stableHomotopyFiber_exact_source B.hom d)
    ((ConcreteCategory.isIso_iff_bijective _).mp (hl (d+1))).surjective
    ((ConcreteCategory.isIso_iff_bijective _).mp (hr (d+1)))
    ((ConcreteCategory.isIso_iff_bijective _).mp (hl d))
    ((ConcreteCategory.isIso_iff_bijective _).mp (hr d)).injective
  · ext x
    have he := congrArg ((stableHomotopyFunctor (d+1)).map) sq.w
    rw [Functor.map_comp, Functor.map_comp] at he
    exact ConcreteCategory.congr_hom he x
  · ext x
    exact ConcreteCategory.congr_hom (stableFiberConnecting_naturality sq d) x
  · ext x
    have he := congrArg ((stableHomotopyFunctor d).map) (homotopyFiberProjection_naturality sq)
    rw [Functor.map_comp, Functor.map_comp] at he
    exact ConcreteCategory.congr_hom he x
  · ext x
    have he := congrArg ((stableHomotopyFunctor d).map) sq.w
    rw [Functor.map_comp, Functor.map_comp] at he
    exact ConcreteCategory.congr_hom he x

end Topology.LoopPrespectrum
