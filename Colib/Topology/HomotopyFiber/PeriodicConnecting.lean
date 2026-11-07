/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.ConnectingBasepointTransport
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportFundamentalGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Colib.Topology.HomotopyFiber.SquareEquivalence
public import Colib.Topology.HomotopyFiber.BasedSquareMap
public import Colib.Topology.HomotopyFiber.Homeomorph

/-!
# The original connecting class of a periodic square homotopy

The vertex of the square homotopy may move. Its entire path is retained in the
fiber basepoint, the loop-prefix map, and the original right-unit transport.
The explicit sweep appends the remaining first-coordinate segment of the
marked target square. Thus its orientation uses the original loop shift.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/PeriodicConnecting.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The literal square sweep,
ordered axes, whole endpoint paths and inverse-commutator sign are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open HomotopyGroup
open scoped Topology unitInterval commutatorElement
universe u v w u' v'
namespace Topology.HomotopyFiber.PeriodicConnecting

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual class of a based path, with the installed reversed multiplication. -/
def loopClass {Z : Type w} [TopologicalSpace Z] {z : Z} (p : Path z z) :
    HomotopyGroup.Pi 1 Z z :=
  Quotient.mk' ((genLoopEquivOfUnique (Fin 1)).symm p)

@[simp] theorem loopClass_toFundamentalGroup
    {Z : Type w} [TopologicalSpace Z] {z : Z} (p : Path z z) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (loopClass p) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) : FundamentalGroup Z z) := by
  apply CategoryTheory.End.ext
  change Path.Homotopic.Quotient.mk
    (genLoopEquivOfUnique (Fin 1) ((genLoopEquivOfUnique (Fin 1)).symm p)) = _
  rw [Equiv.apply_symm_apply]

theorem loopClass_map {Z : Type w} [TopologicalSpace Z] {z : Z}
    (p : Path z z) (g : C(Z, Y)) :
    piMap 0 g rfl (loopClass p) = loopClass (p.map g.continuous) := rfl

/-- A genuine square gives its oriented edge relation in the actual first homotopy group. -/
theorem square_loop_relation {Z : Type w} [TopologicalSpace Z] {z : Z}
    (p q a : Path z z) (F : C(unitInterval × unitInterval, Z))
    (h0 : ∀ s, F (0, s) = p s) (h1 : ∀ s, F (1, s) = q s)
    (hs0 : ∀ t, F (t, 0) = a t) (hs1 : ∀ t, F (t, 1) = a t) :
    loopClass a * loopClass p = loopClass q * loopClass a := by
  let H : p.toContinuousMap.Homotopy q.toContinuousMap := {
    toContinuousMap := F
    map_zero_left := h0
    map_one_left := h1 }
  have ht : (p.trans a).Homotopic (a.trans q) := by
    obtain ⟨K⟩ := Path.Homotopic.map_trans_evalAt H (Path.id : Path (0 : unitInterval) 1)
    refine ⟨(K.pathCast p.source.symm q.target.symm).cast ?_ ?_⟩
    · ext t
      change ((Path.id.map p.continuous).trans (H.evalAt 1)) t = (p.trans a) t
      simp only [Path.trans_apply]
      split_ifs
      · rfl
      · exact hs1 _
    · ext t
      change ((H.evalAt 0).trans (Path.id.map q.continuous)) t = (a.trans q) t
      simp only [Path.trans_apply]
      split_ifs
      · exact hs0 _
      · rfl
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  simp only [map_mul, loopClass_toFundamentalGroup]
  apply CategoryTheory.End.ext
  change (Path.Homotopic.Quotient.mk (p.trans a) : Path.Homotopic.Quotient z z) =
    Path.Homotopic.Quotient.mk (a.trans q)
  exact Quotient.sound ht

variable (f : C(X, Y)) (y : Y) (z : HomotopyFiber f y)

/-- The original prefix map corrected by its original right-unit path. -/
def prefixPiOne : HomotopyGroup.Pi 1 (Path y y) (Path.refl y) →*
    HomotopyGroup.Pi 1 (HomotopyFiber f y) z :=
  (pathTransportMulEquiv (loopPrefixUnitPath f z.val.1 y (toPath f y z)) 0).toMonoidHom.comp
    (piMap 0 (loopPrefix f z.val.1 y (toPath f y z)) rfl)

/-- The original right action, with its actual nonconstant basepoint track removed. -/
def actionPiOne : HomotopyGroup.Pi 1 (HomotopyFiber f y × Path y y) (z, Path.refl y) →*
    HomotopyGroup.Pi 1 (HomotopyFiber f y) z :=
  (pathTransportMulEquiv (loopPrefixUnitPath f z.val.1 y (toPath f y z)) 0).toMonoidHom.comp
    (piMap 0 (rightLoopAction f y) rfl)

private def firstInclusion : C(HomotopyFiber f y, HomotopyFiber f y × Path y y) :=
  (ContinuousMap.id _).prodMk (ContinuousMap.const _ (Path.refl y))

private def secondInclusion : C(Path y y, HomotopyFiber f y × Path y y) :=
  (ContinuousMap.const _ z).prodMk (ContinuousMap.id _)

private def firstPi : HomotopyGroup.Pi 1 (HomotopyFiber f y) z →*
    HomotopyGroup.Pi 1 (HomotopyFiber f y × Path y y) (z, Path.refl y) :=
  piMap 0 (firstInclusion f y) rfl

private def secondPi : HomotopyGroup.Pi 1 (Path y y) (Path.refl y) →*
    HomotopyGroup.Pi 1 (HomotopyFiber f y × Path y y) (z, Path.refl y) :=
  piMap 0 (secondInclusion f y z) rfl

private theorem action_first (a : HomotopyGroup.Pi 1 (HomotopyFiber f y) z) :
    actionPiOne f y z (firstPi f y z a) = a := by
  have ht := pathTransport_homotopyGroupMap_homotopy
    (rightLoopActionUnitHomotopy f y) z 1 a
  have he : (rightLoopActionUnitHomotopy f y).evalAt z =
      loopPrefixUnitPath f z.val.1 y (toPath f y z) := by ext; rfl
  rw [he, HomotopyGroup.map_id] at ht
  change pathTransport (loopPrefixUnitPath f z.val.1 y (toPath f y z)) 1
    (HomotopyGroup.map (rightLoopAction f y) rfl
      (HomotopyGroup.map (firstInclusion f y) rfl a)) = a
  rw [← HomotopyGroup.map_comp]
  exact ht

private theorem action_second (a : HomotopyGroup.Pi 1 (Path y y) (Path.refl y)) :
    actionPiOne f y z (secondPi f y z a) = prefixPiOne f y z a := by
  change pathTransport (loopPrefixUnitPath f z.val.1 y (toPath f y z)) 1
    (HomotopyGroup.map (rightLoopAction f y) rfl
      (HomotopyGroup.map (secondInclusion f y z) rfl a)) = _
  rw [← HomotopyGroup.map_comp]
  rfl

private theorem product_first (a : HomotopyGroup.Pi 1 (HomotopyFiber f y) z) :
    piProdMap 0 z (Path.refl y) (firstPi f y z a) = (a, 1) := by
  induction a using Quotient.inductionOn with | h p => rfl

private theorem product_second (a : HomotopyGroup.Pi 1 (Path y y) (Path.refl y)) :
    piProdMap 0 z (Path.refl y) (secondPi f y z a) = (1, a) := by
  induction a using Quotient.inductionOn with | h p => rfl

/-- The original corrected prefix image commutes with every actual fiber loop. -/
theorem commute_prefixPiOne (a : HomotopyGroup.Pi 1 (HomotopyFiber f y) z)
    (b : HomotopyGroup.Pi 1 (Path y y) (Path.refl y)) :
    Commute a (prefixPiOne f y z b) := by
  have hc : Commute (firstPi f y z a)
      (secondPi f y z b) := by
    apply (piProdMap_bijective 0 z (Path.refl y)).injective
    rw [map_mul, map_mul, product_first, product_second]
    simp
  have hh := congrArg (actionPiOne f y z) hc.eq
  change a * prefixPiOne f y z b = prefixPiOne f y z b * a
  simpa only [map_mul, action_first, action_second] using hh

/-- Product-loop evaluation gives the ordered factorization of the actual action. -/
theorem actionPiOne_factors
    (a : HomotopyGroup.Pi 1 (HomotopyFiber f y × Path y y) (z, Path.refl y)) :
    actionPiOne f y z a =
      prefixPiOne f y z (piProdMap 0 z (Path.refl y) a).2 *
        (piProdMap 0 z (Path.refl y) a).1 := by
  have he : a = secondPi f y z (piProdMap 0 z (Path.refl y) a).2 *
      firstPi f y z (piProdMap 0 z (Path.refl y) a).1 := by
    apply (piProdMap_bijective 0 z (Path.refl y)).injective
    rw [map_mul, product_first, product_second]
    simp
  calc
    actionPiOne f y z a = actionPiOne f y z
        (secondPi f y z (piProdMap 0 z (Path.refl y) a).2 *
          firstPi f y z (piProdMap 0 z (Path.refl y) a).1) :=
      congrArg (actionPiOne f y z) he
    _ = _ := by rw [map_mul, action_first, action_second]

/-- Degree two uses exactly the original first-coordinate loop shift and displayed prefix. -/
def connectingAtPath (x : X) (b : Path (f x) y) : HomotopyGroup.Pi 2 Y y →*
    HomotopyGroup.Pi 1 (HomotopyFiber f y) (pointWithPath f x y b) :=
  (prefixPiOne f y (pointWithPath f x y b)).comp
    (loopShiftMulEquiv (x := y) 0).toMonoidHom

/-- At a constant-path point this is precisely the original LES connecting homomorphism. -/
theorem connectingAtPath_constant (x : X) (h : f x = y) (a : HomotopyGroup.Pi 2 Y y) :
    connectingAtPath f y x (toPath f y (basepoint f y x h)) a =
      connectingHom f y x h 0 a :=
  canonical_loopPrefix_corrected_piOne f y x h (loopShiftMulEquiv (x := y) 0 a)

/-- The same two square coordinates as the original loop shift. -/
def cubeSquare (β : GenLoop (Fin 2) Y y) : C(unitInterval × unitInterval, Y) where
  toFun z := β (Fin.cons z.1 (fun _ : Fin 1 => z.2))
  continuous_toFun := by fun_prop

@[simp] theorem cubeSquare_zero_left (β : GenLoop (Fin 2) Y y) (s : unitInterval) :
    cubeSquare y β (0, s) = y := GenLoop.boundary β _ ⟨0, Or.inl rfl⟩

@[simp] theorem cubeSquare_one_left (β : GenLoop (Fin 2) Y y) (s : unitInterval) :
    cubeSquare y β (1, s) = y := GenLoop.boundary β _ ⟨0, Or.inr rfl⟩

@[simp] theorem cubeSquare_zero_right (β : GenLoop (Fin 2) Y y) (t : unitInterval) :
    cubeSquare y β (t, 0) = y := GenLoop.boundary β _ ⟨1, Or.inl rfl⟩

@[simp] theorem cubeSquare_one_right (β : GenLoop (Fin 2) Y y) (t : unitInterval) :
    cubeSquare y β (t, 1) = y := GenLoop.boundary β _ ⟨1, Or.inr rfl⟩

/-- The actual based path in the loop space obtained by the original currying. -/
def markedLoop (β : GenLoop (Fin 2) Y y) : Path (Path.refl y) (Path.refl y) :=
  genLoopEquivOfUnique (Fin 1) (loopCurry β)

@[simp] theorem markedLoop_class (β : GenLoop (Fin 2) Y y) :
    loopClass (markedLoop y β) = loopShiftMulEquiv (x := y) 0 (Quotient.mk' β) := by
  change Quotient.mk' ((genLoopEquivOfUnique (Fin 1)).symm
    (genLoopEquivOfUnique (Fin 1) (loopCurry β))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Padding by the actual constant target loop, without assuming the stored path is constant. -/
def unitMap : C(HomotopyFiber f y, HomotopyFiber f y) :=
  (rightLoopAction f y).comp
    ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (Path.refl y)))

/-- The remaining first-coordinate segment of the original marked square. -/
def remainingFirst (β : GenLoop (Fin 2) Y y) (t s : unitInterval) :
    Path (cubeSquare y β (t, s)) y where
  toFun u := cubeSquare y β (Set.Icc.convexComb t 1 u, s)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp] theorem remainingFirst_zero (β : GenLoop (Fin 2) Y y) (s u : unitInterval) :
    remainingFirst y β 0 s u = markedLoop y β s u := by
  change cubeSquare y β (Set.Icc.convexComb 0 1 u, s) = cubeSquare y β (u, s)
  simp

@[simp] theorem remainingFirst_one (β : GenLoop (Fin 2) Y y) (s u : unitInterval) :
    remainingFirst y β 1 s u = y := by
  change cubeSquare y β (Set.Icc.convexComb 1 1 u, s) = y
  simp

@[simp] theorem remainingFirst_zero_right
    (β : GenLoop (Fin 2) Y y) (t u : unitInterval) : remainingFirst y β t 0 u = y := by
  exact cubeSquare_zero_right y β _

@[simp] theorem remainingFirst_one_right
    (β : GenLoop (Fin 2) Y y) (t u : unitInterval) : remainingFirst y β t 1 u = y := by
  exact cubeSquare_one_right y β _

variable (τ : C(unitInterval × unitInterval, X)) (β : GenLoop (Fin 2) Y y)
  (P : (f.comp τ).Homotopy (cubeSquare y β))

/-- The complete original vertex track, with only the target boundary equality cast. -/
def vertexTrack : Path (f (τ (0, 0))) y :=
  (P.evalAt (0, 0)).cast rfl (cubeSquare_zero_left y β 0).symm

/-- The displayed fiber point stores the entire moving-vertex track. -/
abbrev vertexPoint : HomotopyFiber f y := pointWithPath f (τ (0, 0)) y (vertexTrack f y τ β P)

/-- The first ordered axis uses exactly the original stored homotopy paths. -/
def firstAxis (hτ : ∀ s, τ (0, s) = τ (1, s))
    (hP : ∀ u s, P (u, (0, s)) = P (u, (1, s))) :
    Path (vertexPoint f y τ β P) (vertexPoint f y τ β P) where
  toFun t := ⟨(τ (t, 0), ⟨fun u => P (u, (t, 0)), by fun_prop⟩),
    P.apply_zero (t, 0), (P.apply_one (t, 0)).trans (cubeSquare_zero_right y β t)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × unitInterval => P (z.2, (z.1, 0)))
    fun_prop
  source' := rfl
  target' := by
    apply Subtype.ext
    apply Prod.ext
    · exact (hτ 0).symm
    · ext u
      exact (hP u 0).symm

/-- The second ordered axis uses exactly the original stored homotopy paths. -/
def secondAxis (hτ : ∀ t, τ (t, 0) = τ (t, 1))
    (hP : ∀ u t, P (u, (t, 0)) = P (u, (t, 1))) :
    Path (vertexPoint f y τ β P) (vertexPoint f y τ β P) where
  toFun s := ⟨(τ (0, s), ⟨fun u => P (u, (0, s)), by fun_prop⟩),
    P.apply_zero (0, s), (P.apply_one (0, s)).trans (cubeSquare_zero_left y β s)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × unitInterval => P (z.2, (0, z.1)))
    fun_prop
  source' := rfl
  target' := by
    apply Subtype.ext
    apply Prod.ext
    · exact (hτ 0).symm
    · ext u
      exact (hP u 0).symm

/-- The actual three-parameter sweep: original homotopy path, then the unused first segment. -/
def sweep : C(unitInterval × unitInterval, HomotopyFiber f y) where
  toFun z := ⟨(τ z, ((P.evalAt z).trans (remainingFirst y β z.1 z.2)).toContinuousMap),
    ((P.evalAt z).trans (remainingFirst y β z.1 z.2)).source,
    ((P.evalAt z).trans (remainingFirst y β z.1 z.2)).target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk τ.continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × unitInterval) × unitInterval =>
      ((P.evalAt z.1).trans (remainingFirst y β z.1.1 z.1.2)) z.2)
    refine Path.trans_continuous_family (fun z : unitInterval × unitInterval => P.evalAt z) ?_
      (fun z => remainingFirst y β z.1 z.2) ?_
    · change Continuous (fun z : (unitInterval × unitInterval) × unitInterval => P (z.2, z.1))
      fun_prop
    · change Continuous (fun z : (unitInterval × unitInterval) × unitInterval =>
        cubeSquare y β (Set.Icc.convexComb z.1.1 1 z.2, z.1.2))
      fun_prop

/-- The initial sweep edge is the second axis acted on by the original curried marked square. -/
theorem sweep_zero (hτ : ∀ t, τ (t, 0) = τ (t, 1))
    (hP : ∀ u t, P (u, (t, 0)) = P (u, (t, 1))) (s : unitInterval) :
    sweep f y τ β P (0, s) =
      rightLoopAction f y (secondAxis f y τ β P hτ hP s, markedLoop y β s) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  ext u
  change ((P.evalAt (0, s)).trans (remainingFirst y β 0 s)) u =
    ((toPath f y (secondAxis f y τ β P hτ hP s)).trans (markedLoop y β s)) u
  simp only [Path.trans_apply]
  split_ifs
  · rfl
  · exact remainingFirst_zero y β s _

/-- Opposite-edge periodicity identifies the terminal sweep edge with the padded second axis. -/
theorem sweep_one (hτ₁ : ∀ s, τ (0, s) = τ (1, s))
    (hτ₂ : ∀ t, τ (t, 0) = τ (t, 1))
    (hP₁ : ∀ u s, P (u, (0, s)) = P (u, (1, s)))
    (hP₂ : ∀ u t, P (u, (t, 0)) = P (u, (t, 1))) (s : unitInterval) :
    sweep f y τ β P (1, s) = unitMap f y (secondAxis f y τ β P hτ₂ hP₂ s) := by
  apply Subtype.ext
  apply Prod.ext (hτ₁ s).symm
  ext u
  change ((P.evalAt (1, s)).trans (remainingFirst y β 1 s)) u =
    ((toPath f y (secondAxis f y τ β P hτ₂ hP₂ s)).trans (Path.refl y)) u
  simp only [Path.trans_apply]
  split_ifs
  · exact (hP₁ _ s).symm
  · exact remainingFirst_one y β s _

/-- The first side of the sweep is the padded first axis, with its original vertex track. -/
theorem sweep_zero_right (hτ : ∀ s, τ (0, s) = τ (1, s))
    (hP : ∀ u s, P (u, (0, s)) = P (u, (1, s))) (t : unitInterval) :
    sweep f y τ β P (t, 0) = unitMap f y (firstAxis f y τ β P hτ hP t) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  ext u
  change ((P.evalAt (t, 0)).trans (remainingFirst y β t 0)) u =
    ((toPath f y (firstAxis f y τ β P hτ hP t)).trans (Path.refl y)) u
  simp only [Path.trans_apply]
  split_ifs
  · rfl
  · exact remainingFirst_zero_right y β t _

/-- Periodicity identifies the other side with exactly the same padded first axis. -/
theorem sweep_one_right (hτ₁ : ∀ s, τ (0, s) = τ (1, s))
    (hτ₂ : ∀ t, τ (t, 0) = τ (t, 1))
    (hP₁ : ∀ u s, P (u, (0, s)) = P (u, (1, s)))
    (hP₂ : ∀ u t, P (u, (t, 0)) = P (u, (t, 1))) (t : unitInterval) :
    sweep f y τ β P (t, 1) = unitMap f y (firstAxis f y τ β P hτ₁ hP₁ t) := by
  apply Subtype.ext
  apply Prod.ext (hτ₂ t).symm
  ext u
  change ((P.evalAt (t, 1)).trans (remainingFirst y β t 1)) u =
    ((toPath f y (firstAxis f y τ β P hτ₁ hP₁ t)).trans (Path.refl y)) u
  simp only [Path.trans_apply]
  split_ifs
  · exact (hP₂ _ t).symm
  · exact remainingFirst_one_right y β t _

/-- Pointwise pairing of paths retains both original first-homotopy-group coordinates. -/
theorem loopClass_prod {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (p : Path a a) (q : Path b b) :
    piProdMap 0 a b (loopClass (p.prod q)) = (loopClass p, loopClass q) := by
  apply Prod.ext <;> rfl

/-- Unit correction takes the padded original path to precisely its original class. -/
theorem unit_corrected_loopClass (a : Path z z) :
    pathTransport (loopPrefixUnitPath f z.val.1 y (toPath f y z)) 1
      (loopClass (a.map (unitMap f y).continuous)) = loopClass a := by
  have ht := pathTransport_homotopyGroupMap_homotopy
    (rightLoopActionUnitHomotopy f y) z 1 (loopClass a)
  have he : (rightLoopActionUnitHomotopy f y).evalAt z =
      loopPrefixUnitPath f z.val.1 y (toPath f y z) := by ext; rfl
  rw [he, HomotopyGroup.map_id] at ht
  exact ht

/-- The exact loop obtained by pointwise action splits into prefix and fiber factors. -/
theorem action_corrected_loopClass (a : Path z z) (c : Path (Path.refl y) (Path.refl y)) :
    pathTransport (loopPrefixUnitPath f z.val.1 y (toPath f y z)) 1
      (loopClass ((a.prod c).map (rightLoopAction f y).continuous)) =
        prefixPiOne f y z (loopClass c) * loopClass a := by
  have ht := actionPiOne_factors f y z (loopClass (a.prod c))
  rw [loopClass_prod] at ht
  exact ht

/-- The periodic square homotopy gives the inverse commutator of its ordered actual fiber axes.
The target class uses the original first-coordinate loop shift and the full vertex prefix. -/
theorem connecting_eq_commutator_inv
    (hτ₁ : ∀ s, τ (0, s) = τ (1, s)) (hτ₂ : ∀ t, τ (t, 0) = τ (t, 1))
    (hP₁ : ∀ u s, P (u, (0, s)) = P (u, (1, s)))
    (hP₂ : ∀ u t, P (u, (t, 0)) = P (u, (t, 1))) :
    connectingAtPath f y (τ (0, 0)) (vertexTrack f y τ β P) (Quotient.mk' β) =
      ⁅loopClass (firstAxis f y τ β P hτ₁ hP₁),
        loopClass (secondAxis f y τ β P hτ₂ hP₂)⁆⁻¹ := by
  let z := vertexPoint f y τ β P
  let A := firstAxis f y τ β P hτ₁ hP₁
  let B := secondAxis f y τ β P hτ₂ hP₂
  let D : HomotopyGroup.Pi 1 (HomotopyFiber f y) z :=
    connectingAtPath f y (τ (0, 0)) (vertexTrack f y τ β P) (Quotient.mk' β)
  let u := loopPrefixUnitPath f z.val.1 y (toPath f y z)
  let T := pathTransportMulEquiv u 0
  let p : Path (unitMap f y z) (unitMap f y z) :=
    (B.prod (markedLoop y β)).map (rightLoopAction f y).continuous
  let q := B.map (unitMap f y).continuous
  let a := A.map (unitMap f y).continuous
  have hs := square_loop_relation p q a (sweep f y τ β P)
    (sweep_zero f y τ β P hτ₂ hP₂)
    (sweep_one f y τ β P hτ₁ hτ₂ hP₁ hP₂)
    (sweep_zero_right f y τ β P hτ₁ hP₁)
    (sweep_one_right f y τ β P hτ₁ hτ₂ hP₁ hP₂)
  have hA : T (loopClass a) = loopClass A := unit_corrected_loopClass f y z A
  have hB : T (loopClass q) = loopClass B := unit_corrected_loopClass f y z B
  have hD : T (loopClass p) = D * loopClass B := by
    have hh := action_corrected_loopClass f y z B (markedLoop y β)
    rw [markedLoop_class] at hh
    exact hh
  have hrel := congrArg T hs
  rw [map_mul, map_mul, hA, hB, hD] at hrel
  have hc : Commute (loopClass A) D :=
    commute_prefixPiOne f y z (loopClass A) (loopShiftMulEquiv (x := y) 0 (Quotient.mk' β))
  have he : D * (loopClass A * loopClass B) = loopClass B * loopClass A := by
    calc
      _ = loopClass A * (D * loopClass B) := by rw [← mul_assoc, ← hc.eq, mul_assoc]
      _ = _ := hrel
  change D = ⁅loopClass A, loopClass B⁆⁻¹
  calc
    D = (loopClass B * loopClass A) * (loopClass A * loopClass B)⁻¹ :=
      eq_mul_inv_iff_mul_eq.mpr he
    _ = _ := by simp [commutatorElement_def, mul_assoc]

/-- The original vertex track at a separately named equal source vertex. -/
def vertexTrackAt (x : X) (hx : τ (0, 0) = x) : Path (f x) y :=
  (vertexTrack f y τ β P).cast (congrArg f hx).symm rfl

@[simp] theorem vertexTrackAt_apply (x : X) (hx : τ (0, 0) = x) (u : unitInterval) :
    vertexTrackAt f y τ β P x hx u = P (u, (0, 0)) := rfl

/-- Equality of the source vertex changes neither the displayed fiber point nor its stored path. -/
theorem vertexPoint_eq_at (x : X) (hx : τ (0, 0) = x) :
    vertexPoint f y τ β P = pointWithPath f x y (vertexTrackAt f y τ β P x hx) := by
  subst x
  rfl

/-- The first original axis at a named equal source vertex. -/
def firstAxisAt (x : X) (hx : τ (0, 0) = x)
    (hτ : ∀ s, τ (0, s) = τ (1, s))
    (hP : ∀ u s, P (u, (0, s)) = P (u, (1, s))) :
    Path (pointWithPath f x y (vertexTrackAt f y τ β P x hx))
      (pointWithPath f x y (vertexTrackAt f y τ β P x hx)) :=
  (firstAxis f y τ β P hτ hP).cast (vertexPoint_eq_at f y τ β P x hx).symm
    (vertexPoint_eq_at f y τ β P x hx).symm

/-- The second original axis at a named equal source vertex. -/
def secondAxisAt (x : X) (hx : τ (0, 0) = x)
    (hτ : ∀ t, τ (t, 0) = τ (t, 1))
    (hP : ∀ u t, P (u, (t, 0)) = P (u, (t, 1))) :
    Path (pointWithPath f x y (vertexTrackAt f y τ β P x hx))
      (pointWithPath f x y (vertexTrackAt f y τ β P x hx)) :=
  (secondAxis f y τ β P hτ hP).cast (vertexPoint_eq_at f y τ β P x hx).symm
    (vertexPoint_eq_at f y τ β P x hx).symm

/-- The same marked inverse-commutator formula at an explicitly named equal source vertex. -/
theorem connecting_eq_commutator_inv_at (x : X) (hx : τ (0, 0) = x)
    (hτ₁ : ∀ s, τ (0, s) = τ (1, s)) (hτ₂ : ∀ t, τ (t, 0) = τ (t, 1))
    (hP₁ : ∀ u s, P (u, (0, s)) = P (u, (1, s)))
    (hP₂ : ∀ u t, P (u, (t, 0)) = P (u, (t, 1))) :
    connectingAtPath f y x (vertexTrackAt f y τ β P x hx) (Quotient.mk' β) =
      ⁅loopClass (firstAxisAt f y τ β P x hx hτ₁ hP₁),
        loopClass (secondAxisAt f y τ β P x hx hτ₂ hP₂)⁆⁻¹ := by
  subst x
  exact connecting_eq_commutator_inv f y τ β P hτ₁ hτ₂ hP₁ hP₂

private theorem corrected_map_congr
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {g h : C(A, B)} (he : g = h) (a : A) (b : B)
    (p : Path (g a) b) (q : Path (h a) b) (hpq : ∀ t, p t = q t)
    (n : ℕ) (c : HomotopyGroup.Pi n A a) :
    pathTransport p n (HomotopyGroup.map g rfl c) =
      pathTransport q n (HomotopyGroup.map h rfl c) := by
  subst h
  have heq : p = q := Path.ext (funext hpq)
  subst q
  rfl

/-- A strict square preserves the original corrected prefix map, at every displayed fiber point. -/
theorem prefixPiOne_map {X' : Type u'} {Y' : Type v'}
    [TopologicalSpace X'] [TopologicalSpace Y'] {g : C(X', Y')}
    (U : C(X, X')) (V : C(Y, Y')) (sq : V.comp f = g.comp U)
    (a : HomotopyGroup.Pi 1 (Path y y) (Path.refl y)) :
    piMap 0 (map U V sq y) rfl (prefixPiOne f y z a) =
      prefixPiOne g (V y) (map U V sq y z)
        (piMap 0 (basedLoopMap V rfl) rfl a) := by
  let M := map U V sq y
  let i := loopPrefix f z.val.1 y (toPath f y z)
  let j := loopPrefix g (M z).val.1 (V y) (toPath g (V y) (M z))
  let L := basedLoopMap V (x := y) rfl
  let p := loopPrefixUnitPath f z.val.1 y (toPath f y z)
  let q := loopPrefixUnitPath g (M z).val.1 (V y) (toPath g (V y) (M z))
  have he : M.comp i = j.comp L := loopPrefix_map_square U V sq _ _ _
  have hpq : ∀ t, (p.map M.continuous) t = q t :=
    loopPrefixUnitPath_map_square U V sq _ _ _
  have hn := (pathTransport_naturality M p 1 (HomotopyGroup.map i rfl a)).symm
  rw [← HomotopyGroup.map_comp] at hn
  have hc := corrected_map_congr he (Path.refl y) (M z) (p.map M.continuous) q hpq 1 a
  exact hn.trans (hc.trans (congrArg (pathTransport q 1)
    (HomotopyGroup.map_comp L rfl j rfl a)))

/-- Strict squares preserve the original shifted connecting image at arbitrary fiber points. -/
theorem connectingAtPath_map {X' : Type u'} {Y' : Type v'}
    [TopologicalSpace X'] [TopologicalSpace Y'] {g : C(X', Y')}
    (U : C(X, X')) (V : C(Y, Y')) (sq : V.comp f = g.comp U)
    (a : HomotopyGroup.Pi 2 Y y) :
    piMap 0 (map U V sq y) rfl (connectingAtPath f y z.val.1 (toPath f y z) a) =
      connectingAtPath g (V y) (map U V sq y z).val.1
        (toPath g (V y) (map U V sq y z)) (piMap 1 V rfl a) := by
  change piMap 0 (map U V sq y) rfl
    (prefixPiOne f y z (loopShiftMulEquiv (x := y) 0 a)) =
      prefixPiOne g (V y) (map U V sq y z)
        (loopShiftMulEquiv (x := V y) 0 (piMap 1 V rfl a))
  rw [prefixPiOne_map]
  exact congrArg (prefixPiOne g (V y) (map U V sq y z))
    (loopShiftEquiv_natural 1 V rfl a).symm

/-- The same original connecting square retains both displayed endpoint equalities. -/
theorem connectingAtPath_mapAt {X' : Type u'} {Y' : Type v'}
    [TopologicalSpace X'] [TopologicalSpace Y'] {g : C(X', Y')}
    (U : C(X, X')) (V : C(Y, Y')) (sq : V.comp f = g.comp U)
    (y' : Y') (hy : V y = y') (z' : HomotopyFiber g y')
    (hz : mapAt U V sq y y' hy z = z') (a : HomotopyGroup.Pi 2 Y y) :
    piMap 0 (mapAt U V sq y y' hy) hz
        (connectingAtPath f y z.val.1 (toPath f y z) a) =
      connectingAtPath g y' z'.val.1 (toPath g y' z') (piMap 1 V hy a) := by
  subst y'
  subst z'
  exact connectingAtPath_map f y z U V sq a

section EndpointChange
variable {S : Type w} {T : Type v'} [TopologicalSpace S] [TopologicalSpace T]
  (g : C(S, T)) (x : S) (y : T) (b : Path (g x) y)

/-- The original source map, viewed as constant free paths. -/
def constantPathMap : C(S, C(unitInterval, T)) := ContinuousMap.const'.comp g

/-- Every endpoint evaluation gives the same original source map. -/
theorem constantPathMap_evaluation (t : unitInterval) :
    (freePathEvaluation T t).comp (constantPathMap g) = g.comp (ContinuousMap.id S) := rfl

/-- The canonical path of initial subpaths from the constant path to the whole given path. -/
def initialPathTrack : Path (constantPathMap g x) b.toContinuousMap where
  toFun t := ⟨fun s => b (t * s), by fun_prop⟩
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × unitInterval => b (z.1 * z.2))
    fun_prop
  source' := by ext s; change b (0 * s) = g x; simp
  target' := by ext s; simp

/-- A single actual free-path-space fiber point supplies both endpoint basepoints. -/
def endpointFiberPoint : HomotopyFiber (constantPathMap g) b.toContinuousMap :=
  pointWithPath (constantPathMap g) x b.toContinuousMap (initialPathTrack g x y b)

/-- The original fiber map induced by initial evaluation of free paths. -/
def endpointStartMap : C(HomotopyFiber (constantPathMap g) b.toContinuousMap,
    HomotopyFiber g (g x)) :=
  mapAt (ContinuousMap.id S) (freePathEvaluation T 0) (constantPathMap_evaluation g 0)
    b.toContinuousMap (g x) b.source

/-- The original fiber map induced by terminal evaluation of free paths. -/
def endpointEndMap : C(HomotopyFiber (constantPathMap g) b.toContinuousMap,
    HomotopyFiber g y) :=
  mapAt (ContinuousMap.id S) (freePathEvaluation T 1) (constantPathMap_evaluation g 1)
    b.toContinuousMap y b.target

/-- Initial evaluation sends the explicit intermediate point to the canonical constant path. -/
theorem endpointStartMap_point :
    endpointStartMap g x y b (endpointFiberPoint g x y b) = basepoint g (g x) x rfl := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  ext t
  change b (t * 0) = g x
  simp

/-- Terminal evaluation retains precisely the given endpoint path in the original fiber. -/
theorem endpointEndMap_point :
    endpointEndMap g x y b (endpointFiberPoint g x y b) = pointWithPath g x y b := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  ext t
  change b (t * 1) = b t
  simp

/-- A genuine base equivalence gives the original endpoint-aware fiber map bijectivity. -/
theorem mapAt_bijective_of_base_equiv
    {A B : Type v'} [TopologicalSpace A] [TopologicalSpace B]
    (p : C(S, A)) (q : C(S, B)) (e : ContinuousMap.HomotopyEquiv A B)
    (sq : e.toFun.comp p = q.comp (ContinuousMap.id S))
    (a : A) (b' : B) (hb : e.toFun a = b')
    (z : HomotopyFiber p a) (z' : HomotopyFiber q b')
    (hz : mapAt (ContinuousMap.id S) e.toFun sq a b' hb z = z') :
    Function.Bijective (piMap 0 (mapAt (ContinuousMap.id S) e.toFun sq a b' hb) hz) := by
  subst b'
  let eS : ULift.{v'} S ≃ₜ S := Homeomorph.ulift
  let eA : ULift.{w} A ≃ₜ A := Homeomorph.ulift
  let eB : ULift.{w} B ≃ₜ B := Homeomorph.ulift
  let p' : C(ULift.{v'} S, ULift.{w} A) := ⟨fun z => ULift.up (p z.down), by fun_prop⟩
  let q' : C(ULift.{v'} S, ULift.{w} B) := ⟨fun z => ULift.up (q z.down), by fun_prop⟩
  let e' := (eA.toHomotopyEquiv.trans e).trans eB.symm.toHomotopyEquiv
  have sq' : e'.toFun.comp p' = q'.comp (ContinuousMap.id (ULift.{v'} S)) := by
    ext z
    exact ContinuousMap.congr_fun sq z.down
  let hp := homeomorphOfSquare p' p eS eA (by ext z; rfl) (ULift.up a)
  let hq := homeomorphOfSquare q' q eS eB (by ext z; rfl) (e' (ULift.up a))
  let em := mapHomotopyEquivOfEquivalences
    (ContinuousMap.HomotopyEquiv.refl (ULift.{v'} S)) e' sq' (ULift.up a)
  let E : ContinuousMap.HomotopyEquiv (HomotopyFiber p a) (HomotopyFiber q (e a)) :=
    hp.symm.toHomotopyEquiv.trans (em.trans hq.toHomotopyEquiv)
  have he : E.toFun = mapAt (ContinuousMap.id S) e.toFun sq a (e a) rfl := by
    ext t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext u
      rfl
  have hzE : E.toFun z = z' := (ContinuousMap.congr_fun he z).trans hz
  simpa only [he] using piMap_bijective_of_homotopyEquiv E hzE 0

/-- The initial original fiber map gives a based Pi-one equivalence. -/
def endpointStartPiOneEquiv :
    HomotopyGroup.Pi 1 (HomotopyFiber (constantPathMap g) b.toContinuousMap)
        (endpointFiberPoint g x y b) ≃*
      HomotopyGroup.Pi 1 (HomotopyFiber g (g x)) (basepoint g (g x) x rfl) :=
  MulEquiv.ofBijective (piMap 0 (endpointStartMap g x y b) (endpointStartMap_point g x y b))
    (mapAt_bijective_of_base_equiv (constantPathMap g) g
      (freePathEvaluationHomotopyEquiv T 0) (constantPathMap_evaluation g 0)
      b.toContinuousMap (g x) b.source _ _ (endpointStartMap_point g x y b))

/-- The terminal original fiber map gives a based Pi-one equivalence. -/
def endpointEndPiOneEquiv :
    HomotopyGroup.Pi 1 (HomotopyFiber (constantPathMap g) b.toContinuousMap)
        (endpointFiberPoint g x y b) ≃*
      HomotopyGroup.Pi 1 (HomotopyFiber g y) (pointWithPath g x y b) :=
  MulEquiv.ofBijective (piMap 0 (endpointEndMap g x y b) (endpointEndMap_point g x y b))
    (mapAt_bijective_of_base_equiv (constantPathMap g) g
      (freePathEvaluationHomotopyEquiv T 1) (constantPathMap_evaluation g 1)
      b.toContinuousMap y b.target _ _ (endpointEndMap_point g x y b))

/-- Change the target endpoint through its actual free-path evaluations, retaining both points. -/
def endpointPiOneEquiv :
    HomotopyGroup.Pi 1 (HomotopyFiber g (g x)) (basepoint g (g x) x rfl) ≃*
      HomotopyGroup.Pi 1 (HomotopyFiber g y) (pointWithPath g x y b) :=
  (endpointStartPiOneEquiv g x y b).symm.trans (endpointEndPiOneEquiv g x y b)

/-- Initial evaluation retains the original projection on the actual first homotopy groups. -/
theorem endpointStartPiOneEquiv_projection
    (a : HomotopyGroup.Pi 1 (HomotopyFiber (constantPathMap g) b.toContinuousMap)
      (endpointFiberPoint g x y b)) :
    piMap 0 (projection g (g x)) rfl (endpointStartPiOneEquiv g x y b a) =
      piMap 0 (projection (constantPathMap g) b.toContinuousMap) rfl a := by
  change HomotopyGroup.map (projection g (g x)) rfl
    (HomotopyGroup.map (endpointStartMap g x y b) (endpointStartMap_point g x y b) a) = _
  rw [← HomotopyGroup.map_comp]
  rfl

/-- Terminal evaluation retains the same original projection on the first homotopy groups. -/
theorem endpointEndPiOneEquiv_projection
    (a : HomotopyGroup.Pi 1 (HomotopyFiber (constantPathMap g) b.toContinuousMap)
      (endpointFiberPoint g x y b)) :
    piMap 0 (projection g y) rfl (endpointEndPiOneEquiv g x y b a) =
      piMap 0 (projection (constantPathMap g) b.toContinuousMap) rfl a := by
  change HomotopyGroup.map (projection g y) rfl
    (HomotopyGroup.map (endpointEndMap g x y b) (endpointEndMap_point g x y b) a) = _
  rw [← HomotopyGroup.map_comp]
  rfl

/-- The actual endpoint-change equivalence retains the unchanged source projection. -/
theorem endpointPiOneEquiv_projection
    (a : HomotopyGroup.Pi 1 (HomotopyFiber g (g x)) (basepoint g (g x) x rfl)) :
    piMap 0 (projection g y) rfl (endpointPiOneEquiv g x y b a) =
      piMap 0 (projection g (g x)) rfl a := by
  change piMap 0 (projection g y) rfl
    (endpointEndPiOneEquiv g x y b ((endpointStartPiOneEquiv g x y b).symm a)) = _
  rw [endpointEndPiOneEquiv_projection, ← endpointStartPiOneEquiv_projection,
    MulEquiv.apply_symm_apply]

/-- Initial evaluation takes the corrected arbitrary-point connecting map to the original LES. -/
theorem endpointStartPiOneEquiv_connecting
    (a : HomotopyGroup.Pi 2 C(unitInterval, T) b.toContinuousMap) :
    endpointStartPiOneEquiv g x y b
      (connectingAtPath (constantPathMap g) b.toContinuousMap x (initialPathTrack g x y b) a) =
        connectingHom g (g x) x rfl 0 (piMap 1 (freePathEvaluation T 0) b.source a) := by
  have h := connectingAtPath_mapAt (constantPathMap g) b.toContinuousMap
    (endpointFiberPoint g x y b) (ContinuousMap.id S) (freePathEvaluation T 0)
    (constantPathMap_evaluation g 0) (g x) b.source (basepoint g (g x) x rfl)
    (endpointStartMap_point g x y b) a
  exact h.trans (connectingAtPath_constant g (g x) x rfl _)

/-- Terminal evaluation retains the exact original endpoint path in the corrected connecting map. -/
theorem endpointEndPiOneEquiv_connecting
    (a : HomotopyGroup.Pi 2 C(unitInterval, T) b.toContinuousMap) :
    endpointEndPiOneEquiv g x y b
      (connectingAtPath (constantPathMap g) b.toContinuousMap x (initialPathTrack g x y b) a) =
        connectingAtPath g y x b (piMap 1 (freePathEvaluation T 1) b.target a) :=
  connectingAtPath_mapAt (constantPathMap g) b.toContinuousMap
    (endpointFiberPoint g x y b) (ContinuousMap.id S) (freePathEvaluation T 1)
    (constantPathMap_evaluation g 1) y b.target (pointWithPath g x y b)
    (endpointEndMap_point g x y b) a

/-- The original canonical connecting map commutes with endpoint change and the original Pi-two
path transport. Both sides arise from the same actual free-path-space fiber point. -/
theorem endpointPiOneEquiv_connecting (a : HomotopyGroup.Pi 2 T (g x)) :
    endpointPiOneEquiv g x y b (connectingHom g (g x) x rfl 0 a) =
      connectingAtPath g y x b (pathTransportMulEquiv b 1 a) := by
  let c := (pathStartEquiv b 2).symm a
  have h0 : piMap 1 (freePathEvaluation T 0) b.source c = a :=
    (pathStartEquiv b 2).apply_symm_apply a
  have h1 : piMap 1 (freePathEvaluation T 1) b.target c = pathTransportMulEquiv b 1 a :=
    (pathTransport_homotopyGroupMap_start b 2 c).symm.trans
      (congrArg (pathTransport b 2) h0)
  have hs := endpointStartPiOneEquiv_connecting g x y b c
  rw [h0] at hs
  change endpointEndPiOneEquiv g x y b
    ((endpointStartPiOneEquiv g x y b).symm (connectingHom g (g x) x rfl 0 a)) = _
  rw [← hs, MulEquiv.symm_apply_apply, endpointEndPiOneEquiv_connecting, h1]

/-- The exact inverse-transport form needed for a marked sphere based at the moving endpoint. -/
theorem endpointPiOneEquiv_connecting_inverse (a : HomotopyGroup.Pi 2 T y) :
    endpointPiOneEquiv g x y b
      (connectingHom g (g x) x rfl 0 ((pathTransportMulEquiv b 1).symm a)) =
        connectingAtPath g y x b a := by
  have h := endpointPiOneEquiv_connecting g x y b ((pathTransportMulEquiv b 1).symm a)
  rw [MulEquiv.apply_symm_apply] at h
  exact h

end EndpointChange
end Topology.HomotopyFiber.PeriodicConnecting
