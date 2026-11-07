/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.ConnectingLoopPathClass
public import Colib.Topology.LocalCoefficients.Prism
public import Colib.Analysis.Convex.StdSimplex.PathHomotopy
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Actual capped source words and their connecting classes

A source loop with a displayed null path for its image gives an actual loop
in the original homotopy fiber. Concatenation and reversal retain both path
parameters. If the source word bounds a displayed source disk, the original
iterated-fiber return gives a concrete target sphere whose original connecting
image is the lifted word. The coordinate-transposition inversion sign is kept.

For an actual singular source triangle with based vertices, this gives its
three-edge identity in the abelianization of the original fiber group. This is
one local chain-coherence identity, not a relative Hurewicz or perfectness theorem.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/CappedTriangle.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual fiber paths, source returns,
ordered face maps and signs are retained directly on native singular simplices. -/
@[expose] public section

open Convexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
open StdSimplex FundamentalGroupoid
universe u

namespace Topology.HomotopyFiber

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)

/-- A displayed image null path defines the original loop-map fiber point. -/
def cappedLoopPoint (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) :
    HomotopyFiber (basedLoopMap f h) (Path.refl y) :=
  ⟨(p, P.toContinuousMap), P.source, P.target⟩

/-- The actual fiber loop retains the source-loop time and null-path time separately. -/
def cappedLoop (p : Path x x) (P : Path (basedLoopMap f h p) (Path.refl y)) :
    Path (basepoint f y x h) (basepoint f y x h) :=
  loopFiberHomeomorph f h (cappedLoopPoint f h p P)

@[simp] theorem cappedLoop_source (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) (s : unitInterval) :
    (cappedLoop f h p P s).val.1 = p s := rfl

@[simp] theorem cappedLoop_path (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) (s t : unitInterval) :
    (cappedLoop f h p P s).val.2 t = P t s := rfl

/-- The capped loop is marked in the installed cubical Pi-one group. -/
def cappedLoopClass (p : Path x x) (P : Path (basedLoopMap f h p) (Path.refl y)) :
    HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x h) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm (FundamentalGroup.fromPath ⟦cappedLoop f h p P⟧)

private theorem basedLoopMap_trans (p q : Path x x) :
    basedLoopMap f h (p.trans q) = (basedLoopMap f h p).trans (basedLoopMap f h q) := by
  subst y
  exact Path.map_trans p q f.continuous

/-- Concatenate the original image null paths in the spatial loop coordinate. -/
def cappedLoopTransNull (p q : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y))
    (Q : Path (basedLoopMap f h q) (Path.refl y)) :
    Path (basedLoopMap f h (p.trans q)) (Path.refl y) :=
  ((P.prod Q).map Path.continuous_trans).cast (basedLoopMap_trans f h p q)
    Path.refl_trans_refl.symm

/-- Spatial concatenation of the caps is exactly concatenation of the actual fiber loops. -/
theorem cappedLoop_trans (p q : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y))
    (Q : Path (basedLoopMap f h q) (Path.refl y)) :
    cappedLoop f h (p.trans q) (cappedLoopTransNull f h p q P Q) =
      (cappedLoop f h p P).trans (cappedLoop f h q Q) := by
  ext s
  apply Subtype.ext
  apply Prod.ext
  · change (p.trans q) s = _
    simp only [Path.trans, Path.coe_mk_mk, Function.comp_apply]
    split_ifs <;> rfl
  · apply ContinuousMap.ext
    intro t
    change ((P t).trans (Q t)) s = _
    simp only [Path.trans, Path.coe_mk_mk, Function.comp_apply]
    split_ifs <;> rfl

/-- The installed fundamental-group multiplication has the original composition order. -/
theorem cappedLoopClass_trans (p q : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y))
    (Q : Path (basedLoopMap f h q) (Path.refl y)) :
    cappedLoopClass f h (p.trans q) (cappedLoopTransNull f h p q P Q) =
      cappedLoopClass f h q Q * cappedLoopClass f h p P := by
  unfold cappedLoopClass
  rw [cappedLoop_trans, ← map_mul]
  rfl

/-- Reverse each original image loop while preserving the null-path time. -/
def cappedLoopSymmNull (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) :
    Path (basedLoopMap f h p.symm) (Path.refl y) :=
  (P.map Path.continuous_symm).cast (by ext t; rfl) (by ext t; rfl)

/-- Reversing the spatial source and cap gives exactly the inverse fiber loop. -/
theorem cappedLoop_symm (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) :
    cappedLoop f h p.symm (cappedLoopSymmNull f h p P) = (cappedLoop f h p P).symm := by
  ext s
  rfl

theorem cappedLoopClass_symm (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) :
    cappedLoopClass f h p.symm (cappedLoopSymmNull f h p P) =
      (cappedLoopClass f h p P)⁻¹ := by
  unfold cappedLoopClass
  rw [cappedLoop_symm]
  change HomotopyGroup.pi1MulEquivFundamentalGroup.symm
    (((FundamentalGroup.fromPath ⟦cappedLoop f h p P⟧) :
      FundamentalGroup _ (basepoint f y x h))⁻¹) = _
  exact map_inv HomotopyGroup.pi1MulEquivFundamentalGroup.symm _

/-- An actual source return and original image cap form the old iterated-fiber point. -/
def cappedLoopReturnPoint (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) (ρ : Path p (Path.refl x)) :
    IteratedFiber (basedLoopMap f h) (Path.refl y) (Path.refl x) :=
  ⟨(cappedLoopPoint f h p P, ρ.toContinuousMap), ρ.source, ρ.target⟩

/-- The actual returned double loop retains the whole source return and cap. -/
def cappedLoopReturn (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) (ρ : Path p (Path.refl x)) :
    Path (Path.refl y) (Path.refl y) :=
  iteratedToLoops (basedLoopMap f h) (Path.refl y) (Path.refl x)
    (basedLoopMap_refl f h) (cappedLoopReturnPoint f h p P ρ)

/-- The full returned path is the inverse image return followed by the original cap. -/
theorem cappedLoopReturn_eq (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) (ρ : Path p (Path.refl x)) :
    cappedLoopReturn f h p P ρ =
      (((ρ.map (basedLoopMap f h).continuous).symm.cast
        (basedLoopMap_refl f h).symm rfl).trans P) := rfl

/-- The genuine old iterated inverse homotopy returns the original capped fiber loop. -/
def cappedLoopReturnPath (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) (ρ : Path p (Path.refl x)) :
    Path (loopConnectingMap f h (cappedLoopReturn f h p P ρ)) (cappedLoop f h p P) := by
  let q := (iteratedLeftInverseHomotopy (basedLoopMap f h) (Path.refl y) (Path.refl x)
    (basedLoopMap_refl f h)).toHomotopy.evalAt (cappedLoopReturnPoint f h p P ρ)
  exact (q.map
    (projection (projection (basedLoopMap f h) (Path.refl y)) (Path.refl x)).continuous).map
      (loopFiberHomeomorph f h).continuous

/-- The sphere class includes the proved coordinate-transposition inversion. -/
def cappedLoopSphereClass (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) (ρ : Path p (Path.refl x)) :
    HomotopyGroup.Pi 2 Y y :=
  ((loopShiftMulEquiv 0).symm
    (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (FundamentalGroup.fromPath ⟦cappedLoopReturn f h p P ρ⟧)))⁻¹

/-- A capped actual source boundary has exactly its original fiber-loop connecting image. -/
theorem connectingHom_cappedLoopSphereClass (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) (ρ : Path p (Path.refl x)) :
    connectingHom f y x h 0 (cappedLoopSphereClass f h p P ρ) =
      cappedLoopClass f h p P := by
  rw [cappedLoopSphereClass, ← LoopComponentTransport.connectingHom_loop_path]
  apply congrArg HomotopyGroup.pi1MulEquivFundamentalGroup.symm
  apply CategoryTheory.End.ext
  exact Quotient.sound ⟨LoopComponentTransport.pathHomotopyOfPath
    (cappedLoopReturnPath f h p P ρ)⟩

variable (τ : C(StdSimplex ℝ (Fin 3), X)) (hτ : ∀ i, τ (StdSimplex.single i) = x)

/-- The actual increasing edge of a source triangle, based by its displayed vertex equalities. -/
def sourceTriangleEdge (i j : Fin 3) : Path x x :=
  ((LocalCoefficients.simplexEdgePath i j).map τ.continuous).cast (hτ i).symm (hτ j).symm

/-- The oriented source boundary travels along 01, then 12, then the inverse of 02. -/
def sourceTriangleBoundary : Path x x :=
  ((sourceTriangleEdge τ hτ 0 1).trans (sourceTriangleEdge τ hτ 1 2)).trans
    (sourceTriangleEdge τ hτ 0 2).symm

/-- The exact three-edge loop in the standard source simplex. -/
def standardTriangleBoundary :
    Path (StdSimplex.single (R := ℝ) (0 : Fin 3)) (StdSimplex.single 0) :=
  ((LocalCoefficients.simplexEdgePath 0 1).trans
    (LocalCoefficients.simplexEdgePath 1 2)).trans (LocalCoefficients.simplexEdgePath 0 2).symm

/-- The displayed based source boundary is the original simplex image with endpoint casts. -/
theorem sourceTriangleBoundary_eq_map :
    sourceTriangleBoundary τ hτ =
      (standardTriangleBoundary.map τ.continuous).cast (hτ 0).symm (hτ 0).symm := by
  rw [standardTriangleBoundary, Path.map_trans, Path.map_trans, ← Path.map_symm]
  rfl

/-- Convex interpolation inside the actual source simplex supplies its complete source return. -/
def sourceTriangleReturn : Path (sourceTriangleBoundary τ hτ) (Path.refl x) := by
  let H := ((StdSimplex.pathHomotopy standardTriangleBoundary
    (Path.refl (StdSimplex.single 0))).map τ).pathCast (hτ 0).symm (hτ 0).symm
  apply LoopComponentTransport.pathOfPathHomotopy
  exact H.cast (sourceTriangleBoundary_eq_map τ hτ).symm (by ext t; exact hτ 0)

variable
  (P₀₁ : Path (basedLoopMap f h (sourceTriangleEdge τ hτ 0 1)) (Path.refl y))
  (P₁₂ : Path (basedLoopMap f h (sourceTriangleEdge τ hτ 1 2)) (Path.refl y))
  (P₀₂ : Path (basedLoopMap f h (sourceTriangleEdge τ hτ 0 2)) (Path.refl y))

/-- Three displayed edge caps give the literal null path of the oriented source boundary. -/
def cappedTriangleNull :
    Path (basedLoopMap f h (sourceTriangleBoundary τ hτ)) (Path.refl y) :=
  cappedLoopTransNull f h
    ((sourceTriangleEdge τ hτ 0 1).trans (sourceTriangleEdge τ hτ 1 2))
    (sourceTriangleEdge τ hτ 0 2).symm
    (cappedLoopTransNull f h _ _ P₀₁ P₁₂) (cappedLoopSymmNull f h _ P₀₂)

/-- Cap the actual source triangle, retaining the exact source return and the transpose sign. -/
def cappedTriangleSphereClass : HomotopyGroup.Pi 2 Y y :=
  cappedLoopSphereClass f h (sourceTriangleBoundary τ hτ)
    (cappedTriangleNull f h τ hτ P₀₁ P₁₂ P₀₂) (sourceTriangleReturn τ hτ)

/-- The concrete sphere is the one constructed from the actual image triangle and the same caps. -/
theorem cappedTriangleSphereClass_image :
    cappedTriangleSphereClass f h τ hτ P₀₁ P₁₂ P₀₂ =
      cappedTriangleSphereClass (ContinuousMap.id Y) (rfl : y = y) (f.comp τ)
        (fun i ↦ (congrArg f (hτ i)).trans h) P₀₁ P₁₂ P₀₂ := by
  rfl

/-- The original connecting map evaluates the capped triangle as its three actual fiber edges. -/
theorem connectingHom_cappedTriangleSphereClass :
    connectingHom f y x h 0 (cappedTriangleSphereClass f h τ hτ P₀₁ P₁₂ P₀₂) =
      (cappedLoopClass f h (sourceTriangleEdge τ hτ 0 2) P₀₂)⁻¹ *
        (cappedLoopClass f h (sourceTriangleEdge τ hτ 1 2) P₁₂ *
          cappedLoopClass f h (sourceTriangleEdge τ hτ 0 1) P₀₁) := by
  rw [cappedTriangleSphereClass, connectingHom_cappedLoopSphereClass]
  change cappedLoopClass f h _ (cappedLoopTransNull f h _ _ _ _) = _
  rw [cappedLoopClass_trans, cappedLoopClass_trans, cappedLoopClass_symm]

/-- The actual edge value in the abelianization of the original fiber Pi one. -/
def abelianCappedLoopValue (p : Path x x)
    (P : Path (basedLoopMap f h p) (Path.refl y)) :
    Additive (Abelianization
      (HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x h))) :=
  Additive.ofMul (Abelianization.of (cappedLoopClass f h p P))

/-- The alternating increasing-face signs are the original singular triangle boundary signs. -/
theorem abelian_connecting_cappedTriangleSphereClass :
    Additive.ofMul (Abelianization.of
      (connectingHom f y x h 0 (cappedTriangleSphereClass f h τ hτ P₀₁ P₁₂ P₀₂))) =
      abelianCappedLoopValue f h (sourceTriangleEdge τ hτ 1 2) P₁₂ -
        abelianCappedLoopValue f h (sourceTriangleEdge τ hτ 0 2) P₀₂ +
          abelianCappedLoopValue f h (sourceTriangleEdge τ hτ 0 1) P₀₁ := by
  rw [connectingHom_cappedTriangleSphereClass]
  simp only [map_mul, map_inv]
  change -abelianCappedLoopValue f h (sourceTriangleEdge τ hτ 0 2) P₀₂ +
    (abelianCappedLoopValue f h (sourceTriangleEdge τ hτ 1 2) P₁₂ +
      abelianCappedLoopValue f h (sourceTriangleEdge τ hτ 0 1) P₀₁) = _
  abel

end Topology.HomotopyFiber
