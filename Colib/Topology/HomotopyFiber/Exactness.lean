/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Basic

/-!
# Exactness at the source of a map

For the concrete path-space homotopy fiber of a based continuous map `f : X → Y`,
the image of the homotopy-fiber projection on each positive-dimensional homotopy
group is precisely the kernel of the map induced by `f`.

The reverse inclusion is proved geometrically: a representative cube whose
image under `f` is nullhomotopic relative to its boundary lifts to the homotopy
fiber by taking the nullhomotopy paths as its second coordinates. No fibration,
long-exact-sequence, or localization theorem is assumed.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/Exactness.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space models,
basepoint tracks, maps and universe parameters are retained. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval

universe w u v

namespace Topology.HomotopyFiber

variable {N : Type w} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (y : Y) (x : X) (h : f x = y)

/-- A based cube whose image is nullhomotopic relative to the boundary lifts
as a based cube to the actual path-space homotopy fiber. -/
def liftGenLoop (p : GenLoop N X x)
    (H : (GenLoop.postcomp f h p).val.HomotopyRel
      (GenLoop.const : GenLoop N Y y).val (Cube.boundary N)) :
    GenLoop N (HomotopyFiber f y) (basepoint f y x h) :=
  ⟨lift f y p.val H.toHomotopy, by
    intro z hz
    apply Subtype.ext
    apply Prod.ext
    · exact p.property z hz
    · apply ContinuousMap.ext
      intro t
      exact H.eq_snd t hz⟩

/-- Projection recovers the original cube pointwise, and hence strictly. -/
@[simp]
theorem genLoopPostcomp_liftGenLoop (p : GenLoop N X x)
    (H : (GenLoop.postcomp f h p).val.HomotopyRel
      (GenLoop.const : GenLoop N Y y).val (Cube.boundary N)) :
    GenLoop.postcomp (projection f y) (projection_basepoint f y x h)
      (liftGenLoop f y x h p H) = p := by
  ext z
  rfl

/-- The consecutive induced homomorphisms compose to zero (multiplicatively,
to the trivial homomorphism), for an arbitrary nonempty cube index type. -/
theorem homotopyGroupMapHom_projection_comp [DecidableEq N] [Nonempty N] :
    (HomotopyGroup.mapHom (N := N) f h).comp
      (HomotopyGroup.mapHom (projection f y) (projection_basepoint f y x h)) = 1 := by
  rw [← HomotopyGroup.mapHom_comp]
  exact (HomotopyGroup.mapHom_eq_of_based_homotopy _ rfl
    (projectionNullhomotopy f y) (projectionNullhomotopy_basepoint f y x h)).trans
      HomotopyGroup.mapHom_const

/-- A homotopy class lies in the image of the homotopy-fiber projection
exactly when its image under the original based map is trivial. -/
theorem mem_range_projection_iff [DecidableEq N] [Nonempty N]
    (a : HomotopyGroup N X x) :
    a ∈ (HomotopyGroup.mapHom (projection f y) (projection_basepoint f y x h)).range ↔
      HomotopyGroup.mapHom f h a = 1 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact congrArg (fun k : HomotopyGroup N (HomotopyFiber f y) (basepoint f y x h) →*
      HomotopyGroup N Y y => k b) (homotopyGroupMapHom_projection_comp f y x h)
  · refine Quotient.inductionOn a (fun p hp => ?_)
    change Quotient.mk' (GenLoop.postcomp f h p) = Quotient.mk' GenLoop.const at hp
    obtain ⟨H⟩ := Quotient.exact hp
    refine ⟨Quotient.mk' (liftGenLoop f y x h p H), ?_⟩
    change Quotient.mk' (GenLoop.postcomp (projection f y)
      (projection_basepoint f y x h) (liftGenLoop f y x h p H)) = Quotient.mk' p
    rw [genLoopPostcomp_liftGenLoop]

/-- Genuine image-equals-kernel exactness at the source homotopy group,
with an arbitrary nonempty cube index type. -/
theorem range_projection_eq_ker [DecidableEq N] [Nonempty N] :
    (HomotopyGroup.mapHom (N := N) (projection f y)
      (projection_basepoint f y x h)).range = (HomotopyGroup.mapHom f h).ker := by
  ext a
  exact mem_range_projection_iff f y x h a

/-- The homotopy-fiber sequence is exact at `π_(n+1) X`, for every `n ≥ 0`.
This is one exactness position; it does not assert a full long exact sequence. -/
theorem piMap_range_projection_eq_ker (n : ℕ) :
    (HomotopyGroup.piMap n (projection f y) (projection_basepoint f y x h)).range =
      (HomotopyGroup.piMap n f h).ker :=
  range_projection_eq_ker f y x h

end Topology.HomotopyFiber
