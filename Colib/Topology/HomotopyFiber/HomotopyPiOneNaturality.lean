/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.HomotopyFiber.WeakBasePositive
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportGroup

/-!
Implementation provenance:
`Quillen/Topology/HomotopyFiber/HomotopyPiOneNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original fiber Pi-one naturality along an arbitrary map homotopy

The whole homotopy defines a map into the free path space. Its two actual
endpoint evaluations give strict squares of the original homotopy fibers.
Their induced fundamental-group equivalences define transport, preserving
the actual projection and the original connecting map with precisely the
homotopy's basepoint track. No stationary-track hypothesis is imposed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open scoped Topology unitInterval
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)} (H : f.Homotopy g)

/-- The whole displayed homotopy as a continuous map into the free path space. -/
def homotopyPathMap : C(X, C(unitInterval, Y)) where
  toFun x := (H.evalAt x).toContinuousMap
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact H.continuous.comp (continuous_snd.prodMk continuous_fst)

/-- Initial evaluation retains the original source map exactly. -/
theorem homotopyPathMap_zero :
    (freePathEvaluation Y 0).comp (homotopyPathMap H) = f.comp (ContinuousMap.id X) := by
  ext x
  exact H.apply_zero x

/-- Terminal evaluation retains the original target map exactly. -/
theorem homotopyPathMap_one :
    (freePathEvaluation Y 1).comp (homotopyPathMap H) = g.comp (ContinuousMap.id X) := by
  ext x
  exact H.apply_one x

/-- The original fiber map induced by initial evaluation of the whole homotopy. -/
def homotopyFiberStart (x : X) :
    C(HomotopyFiber (homotopyPathMap H) (homotopyPathMap H x), HomotopyFiber f (f x)) :=
  mapAt (ContinuousMap.id X) (freePathEvaluation Y 0) (homotopyPathMap_zero H)
    (homotopyPathMap H x) (f x) (H.apply_zero x)

/-- The original fiber map induced by terminal evaluation of the whole homotopy. -/
def homotopyFiberEnd (x : X) :
    C(HomotopyFiber (homotopyPathMap H) (homotopyPathMap H x), HomotopyFiber g (g x)) :=
  mapAt (ContinuousMap.id X) (freePathEvaluation Y 1) (homotopyPathMap_one H)
    (homotopyPathMap H x) (g x) (H.apply_one x)

/-- Initial evaluation preserves the actual constant-path fiber basepoint. -/
theorem homotopyFiberStart_basepoint (x : X) :
    homotopyFiberStart H x
      (basepoint (homotopyPathMap H) (homotopyPathMap H x) x rfl) =
      basepoint f (f x) x rfl :=
  mapAt_basepoint (ContinuousMap.id X) (freePathEvaluation Y 0)
    (homotopyPathMap_zero H) x (homotopyPathMap H x) x (f x) rfl rfl rfl (H.apply_zero x)

/-- Terminal evaluation preserves the actual constant-path fiber basepoint. -/
theorem homotopyFiberEnd_basepoint (x : X) :
    homotopyFiberEnd H x
      (basepoint (homotopyPathMap H) (homotopyPathMap H x) x rfl) =
      basepoint g (g x) x rfl :=
  mapAt_basepoint (ContinuousMap.id X) (freePathEvaluation Y 1)
    (homotopyPathMap_one H) x (homotopyPathMap H x) x (g x) rfl rfl rfl (H.apply_one x)

/-- Initial evaluation gives its actual induced isomorphism on the fiber fundamental groups. -/
def homotopyFiberStartPiOneEquiv (x : X) :
    HomotopyGroup.Pi 1 (HomotopyFiber (homotopyPathMap H) (homotopyPathMap H x))
        (basepoint (homotopyPathMap H) (homotopyPathMap H x) x rfl) ≃*
      HomotopyGroup.Pi 1 (HomotopyFiber f (f x)) (basepoint f (f x) x rfl) :=
  MulEquiv.ofBijective
    (HomotopyGroup.piMap 0 (homotopyFiberStart H x) (homotopyFiberStart_basepoint H x))
    (mapAt_piOne_bijective (homotopyPathMap H) f (freePathEvaluation Y 0)
      (homotopyPathMap_zero H) x (homotopyPathMap H x) rfl (f x) (H.apply_zero x) rfl
      (homotopyGroupMap_bijective_of_homotopyEquiv
        (freePathEvaluationHomotopyEquiv Y 0) (H.apply_zero x) 1).injective
      (homotopyGroupMap_bijective_of_homotopyEquiv
        (freePathEvaluationHomotopyEquiv Y 0) (H.apply_zero x) 2))

/-- Terminal evaluation gives its actual induced isomorphism on the fiber fundamental groups. -/
def homotopyFiberEndPiOneEquiv (x : X) :
    HomotopyGroup.Pi 1 (HomotopyFiber (homotopyPathMap H) (homotopyPathMap H x))
        (basepoint (homotopyPathMap H) (homotopyPathMap H x) x rfl) ≃*
      HomotopyGroup.Pi 1 (HomotopyFiber g (g x)) (basepoint g (g x) x rfl) :=
  MulEquiv.ofBijective
    (HomotopyGroup.piMap 0 (homotopyFiberEnd H x) (homotopyFiberEnd_basepoint H x))
    (mapAt_piOne_bijective (homotopyPathMap H) g (freePathEvaluation Y 1)
      (homotopyPathMap_one H) x (homotopyPathMap H x) rfl (g x) (H.apply_one x) rfl
      (homotopyGroupMap_bijective_of_homotopyEquiv
        (freePathEvaluationHomotopyEquiv Y 1) (H.apply_one x) 1).injective
      (homotopyGroupMap_bijective_of_homotopyEquiv
        (freePathEvaluationHomotopyEquiv Y 1) (H.apply_one x) 2))

/-- Fiber Pi-one transport obtained from the two original endpoint maps of the whole homotopy. -/
def homotopyFiberPiOneEquiv (x : X) :
    HomotopyGroup.Pi 1 (HomotopyFiber f (f x)) (basepoint f (f x) x rfl) ≃*
      HomotopyGroup.Pi 1 (HomotopyFiber g (g x)) (basepoint g (g x) x rfl) :=
  (homotopyFiberStartPiOneEquiv H x).symm.trans (homotopyFiberEndPiOneEquiv H x)

/-- The actual endpoint transport retains the original fiber projection. -/
theorem homotopyFiberPiOneEquiv_projection (x : X)
    (a : HomotopyGroup.Pi 1 (HomotopyFiber f (f x)) (basepoint f (f x) x rfl)) :
    HomotopyGroup.piMap 0 (projection g (g x)) (projection_basepoint g (g x) x rfl)
      (homotopyFiberPiOneEquiv H x a) =
    HomotopyGroup.piMap 0 (projection f (f x)) (projection_basepoint f (f x) x rfl) a := by
  let i := HomotopyGroup.piMap 0 (projection (homotopyPathMap H) (homotopyPathMap H x))
    (projection_basepoint (homotopyPathMap H) (homotopyPathMap H x) x rfl)
  have h0 (z) : HomotopyGroup.piMap 0 (projection f (f x)) (projection_basepoint f (f x) x rfl)
      (homotopyFiberStartPiOneEquiv H x z) = i z := by
    have hh := DFunLike.congr_fun (projectionHom_mapAt_natural (ContinuousMap.id X)
      (freePathEvaluation Y 0) (homotopyPathMap_zero H) x (homotopyPathMap H x) x
      (f x) rfl rfl rfl (H.apply_zero x) 0) z
    change HomotopyGroup.piMap 0 (projection f (f x)) (projection_basepoint f (f x) x rfl)
      (homotopyFiberStartPiOneEquiv H x z) =
        HomotopyGroup.map (ContinuousMap.id X) rfl (i z) at hh
    simpa only [HomotopyGroup.map_id] using hh
  have h1 (z) : HomotopyGroup.piMap 0 (projection g (g x)) (projection_basepoint g (g x) x rfl)
      (homotopyFiberEndPiOneEquiv H x z) = i z := by
    have hh := DFunLike.congr_fun (projectionHom_mapAt_natural (ContinuousMap.id X)
      (freePathEvaluation Y 1) (homotopyPathMap_one H) x (homotopyPathMap H x) x
      (g x) rfl rfl rfl (H.apply_one x) 0) z
    change HomotopyGroup.piMap 0 (projection g (g x)) (projection_basepoint g (g x) x rfl)
      (homotopyFiberEndPiOneEquiv H x z) =
        HomotopyGroup.map (ContinuousMap.id X) rfl (i z) at hh
    simpa only [HomotopyGroup.map_id] using hh
  change HomotopyGroup.piMap 0 (projection g (g x)) (projection_basepoint g (g x) x rfl)
    (homotopyFiberEndPiOneEquiv H x ((homotopyFiberStartPiOneEquiv H x).symm a)) = _
  rw [h1, ← h0, MulEquiv.apply_symm_apply]

/-- Original connecting naturality retains the exact track of the given homotopy. -/
theorem homotopyFiberPiOneEquiv_connecting (x : X) (a : HomotopyGroup.Pi 2 Y (f x)) :
    homotopyFiberPiOneEquiv H x (connectingHom f (f x) x rfl 0 a) =
      connectingHom g (g x) x rfl 0 (pathTransport (H.evalAt x) 2 a) := by
  let c := (pathStartEquiv (H.evalAt x) 2).symm a
  let d := connectingHom (homotopyPathMap H) (homotopyPathMap H x) x rfl 0
  have h0 : homotopyFiberStartPiOneEquiv H x (d c) = connectingHom f (f x) x rfl 0 a := by
    have hh := DFunLike.congr_fun (connectingHom_mapAt_natural (ContinuousMap.id X)
      (freePathEvaluation Y 0) (homotopyPathMap_zero H) x (homotopyPathMap H x) x
      (f x) rfl rfl rfl (H.apply_zero x) 0) c
    change homotopyFiberStartPiOneEquiv H x (d c) =
      connectingHom f (f x) x rfl 0 (pathStartEquiv (H.evalAt x) 2 c) at hh
    exact hh.trans (congrArg (connectingHom f (f x) x rfl 0)
      ((pathStartEquiv (H.evalAt x) 2).apply_symm_apply a))
  change homotopyFiberEndPiOneEquiv H x
    ((homotopyFiberStartPiOneEquiv H x).symm (connectingHom f (f x) x rfl 0 a)) = _
  rw [← h0, MulEquiv.symm_apply_apply]
  exact DFunLike.congr_fun (connectingHom_mapAt_natural (ContinuousMap.id X)
    (freePathEvaluation Y 1) (homotopyPathMap_one H) x (homotopyPathMap H x) x
    (g x) rfl rfl rfl (H.apply_one x) 0) c


section Square
variable {X' : Type u'} {Y' : Type v'} [TopologicalSpace X'] [TopologicalSpace Y']
  {p : C(X, Y)} {q : C(X', Y')}
  (u : C(X, X')) (v : C(Y, Y')) (K : (v.comp p).Homotopy (q.comp u))
  (x : X) (x' : X') (hx : u x = x')

/-- The original base-map square acts on the actual fiber fundamental group. -/
def squareSourcePiOneMap :
    HomotopyGroup.Pi 1 (HomotopyFiber p (p x)) (basepoint p (p x) x rfl) →*
      HomotopyGroup.Pi 1 (HomotopyFiber (v.comp p) (v (p x)))
        (basepoint (v.comp p) (v (p x)) x rfl) :=
  HomotopyGroup.piMap 0 (mapAt (ContinuousMap.id X) v rfl (p x) (v (p x)) rfl)
    (mapAt_basepoint (ContinuousMap.id X) v rfl x (p x) x (v (p x)) rfl rfl rfl rfl)

/-- The original total-space square acts on the actual fiber fundamental group. -/
def squareTargetPiOneMap :
    HomotopyGroup.Pi 1 (HomotopyFiber (q.comp u) (q (u x)))
        (basepoint (q.comp u) (q (u x)) x rfl) →*
      HomotopyGroup.Pi 1 (HomotopyFiber q (q x')) (basepoint q (q x') x' rfl) :=
  HomotopyGroup.piMap 0 (mapAt u (ContinuousMap.id Y') rfl (q (u x)) (q x') (congrArg q hx))
    (mapAt_basepoint u (ContinuousMap.id Y') rfl x (q (u x)) x' (q x')
      rfl rfl hx (congrArg q hx))

/-- An arbitrary actual homotopy square acts on the original based fiber fundamental groups. -/
def homotopySquarePiOneMap :
    HomotopyGroup.Pi 1 (HomotopyFiber p (p x)) (basepoint p (p x) x rfl) →*
      HomotopyGroup.Pi 1 (HomotopyFiber q (q x')) (basepoint q (q x') x' rfl) :=
  (squareTargetPiOneMap u x x' hx).comp
    ((homotopyFiberPiOneEquiv K x).toMonoidHom.comp (squareSourcePiOneMap v x))

/-- The whole homotopy-square construction retains its original total-space map. -/
theorem homotopySquarePiOneMap_projection
    (a : HomotopyGroup.Pi 1 (HomotopyFiber p (p x)) (basepoint p (p x) x rfl)) :
    HomotopyGroup.piMap 0 (projection q (q x')) (projection_basepoint q (q x') x' rfl)
      (homotopySquarePiOneMap u v K x x' hx a) =
    HomotopyGroup.piMap 0 u hx
      (HomotopyGroup.piMap 0 (projection p (p x)) (projection_basepoint p (p x) x rfl) a) := by
  have hA :
      HomotopyGroup.piMap 0 (projection (v.comp p) (v (p x)))
        (projection_basepoint (v.comp p) (v (p x)) x rfl) (squareSourcePiOneMap v x a) =
      HomotopyGroup.piMap 0 (projection p (p x)) (projection_basepoint p (p x) x rfl) a := by
    have hh := DFunLike.congr_fun (projectionHom_mapAt_natural (f := p) (g := v.comp p)
      (ContinuousMap.id X) v rfl
      x (p x) x (v (p x)) rfl rfl rfl rfl 0) a
    change HomotopyGroup.piMap 0 (projection (v.comp p) (v (p x)))
      (projection_basepoint (v.comp p) (v (p x)) x rfl) (squareSourcePiOneMap v x a) =
        HomotopyGroup.map (ContinuousMap.id X) rfl
          (HomotopyGroup.piMap 0 (projection p (p x)) (projection_basepoint p (p x) x rfl) a) at hh
    simpa only [HomotopyGroup.map_id] using hh
  have hD := DFunLike.congr_fun (projectionHom_mapAt_natural (f := q.comp u) (g := q)
    u (ContinuousMap.id Y') rfl
    x (q (u x)) x' (q x') rfl rfl hx (congrArg q hx) 0)
      (homotopyFiberPiOneEquiv K x (squareSourcePiOneMap v x a))
  exact hD.trans (congrArg (HomotopyGroup.piMap 0 u hx)
    ((homotopyFiberPiOneEquiv_projection K x (squareSourcePiOneMap v x a)).trans hA))

/-- The original connecting maps commute with the actual square and its full vertex track. -/
theorem homotopySquarePiOneMap_connecting (a : HomotopyGroup.Pi 2 Y (p x)) :
    homotopySquarePiOneMap u v K x x' hx (connectingHom p (p x) x rfl 0 a) =
      connectingHom q (q x') x' rfl 0
        (pathTransport ((K.evalAt x).cast rfl (congrArg q hx).symm) 2
          (HomotopyGroup.piMap 1 v rfl a)) := by
  subst x'
  have hA := DFunLike.congr_fun (connectingHom_mapAt_natural (f := p) (g := v.comp p)
    (ContinuousMap.id X) v rfl
    x (p x) x (v (p x)) rfl rfl rfl rfl 0) a
  change squareSourcePiOneMap v x (connectingHom p (p x) x rfl 0 a) =
    connectingHom (v.comp p) (v (p x)) x rfl 0 (HomotopyGroup.piMap 1 v rfl a) at hA
  change squareTargetPiOneMap u x (u x) rfl
    (homotopyFiberPiOneEquiv K x
      (squareSourcePiOneMap v x (connectingHom p (p x) x rfl 0 a))) = _
  rw [hA]
  have hD := DFunLike.congr_fun (connectingHom_mapAt_natural (f := q.comp u) (g := q)
    u (ContinuousMap.id Y') rfl
    x (q (u x)) (u x) (q (u x)) rfl rfl rfl rfl 0)
      (pathTransport (K.evalAt x) 2 (HomotopyGroup.piMap 1 v rfl a))
  change squareTargetPiOneMap u x (u x) rfl
    (connectingHom (q.comp u) (q (u x)) x rfl 0
      (pathTransport (K.evalAt x) 2 (HomotopyGroup.piMap 1 v rfl a))) =
    connectingHom q (q (u x)) (u x) rfl 0
      (HomotopyGroup.map (ContinuousMap.id Y') rfl
        (pathTransport (K.evalAt x) 2 (HomotopyGroup.piMap 1 v rfl a))) at hD
  exact (congrArg (squareTargetPiOneMap u x (u x) rfl)
    (homotopyFiberPiOneEquiv_connecting K x (HomotopyGroup.piMap 1 v rfl a))).trans
      (by simpa only [HomotopyGroup.map_id, Path.cast_rfl_rfl, ContinuousMap.comp_apply] using hD)
end Square

end Topology.HomotopyFiber
