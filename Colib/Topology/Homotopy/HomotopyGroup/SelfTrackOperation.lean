/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackTransport
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackTimeOperations
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackSpatialProduct
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackNaturality

/-!
# Operations from whole based identity self-homotopies

A whole identity self-homotopy fixed at the basepoint gives an operation from
Pi(n+1) to Pi(n+2). Descent is proved as the input cube varies, using the actual
fundamental-groupoid conjugation of its tracks and the existing normalization.

The second spatial coordinate proves source additivity in degrees at least two.
Time composition, relative homotopy invariance and strict based-map naturality
retain the whole tracks. The representative API keeps the original track-first
coordinate order, including its inverse relative to spatial-first normalization.
No loop-shift or localization-boundary sign compatibility is asserted here.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/SelfTrackOperation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original cube coordinates,
whole tracks and group laws are retained under native Colib ownership. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Topology.IdentityTrack
variable {X : Type u} [TopologicalSpace X] {x : X}
variable (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
  (hH : ∀ t, H (t, x) = x)

/-- The whole based identity self-homotopy acts continuously on the original
cube space, with its original time and every original spatial coordinate. -/
def cubeHomotopy (m : ℕ) :
    (ContinuousMap.id (GenLoop (Fin (m + 1)) X x)).Homotopy (ContinuousMap.id _) where
  toFun z := ⟨⟨fun s => H (z.1, z.2 s), by fun_prop⟩, by
    intro s hs
    change H (z.1, z.2 s) = x
    exact (congrArg (fun y => H (z.1, y)) (z.2.property s hs)).trans (hH z.1)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × GenLoop (Fin (m + 1)) X x) ×
      (Fin (m + 1) → unitInterval) => H (z.1.1, z.1.2 z.2))
    fun_prop
  map_zero_left p := by ext s; exact H.apply_zero (p s)
  map_one_left p := by ext s; exact H.apply_one (p s)

/-- The actual whole self-track of one input cube. -/
def track (m : ℕ) (p : GenLoop (Fin (m + 1)) X x) : Path p p :=
  (cubeHomotopy H hH m).evalAt p

/-- Naturality of a whole self-homotopy gives the genuine conjugation law
between the tracks at the ends of every path in the input space. -/
theorem track_transport (m : ℕ) {p q : GenLoop (Fin (m + 1)) X x} (β : Path p q) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath β
      (⟦track H hH m p⟧ : FundamentalGroup _ p) =
        (⟦track H hH m q⟧ : FundamentalGroup _ q) := by
  let K := cubeHomotopy H hH m
  let b : FundamentalGroupoid.mk p ⟶ FundamentalGroupoid.mk q := ⟦β⟧
  have hn := (FundamentalGroupoidFunctor.homotopicMapsNatIso K).naturality b
  change b ≫ (Path.Homotopic.Quotient.mk (K.evalAt q)) =
    (Path.Homotopic.Quotient.mk (K.evalAt p)) ≫ b at hn
  change Groupoid.inv b ≫
    (Path.Homotopic.Quotient.mk (K.evalAt p)) ≫ b =
      (Path.Homotopic.Quotient.mk (K.evalAt q))
  rw [← hn]
  simp

/-- The normalized higher class is unchanged as the actual input cube moves. -/
theorem class_eq_of_path (m : ℕ) {p q : GenLoop (Fin (m + 1)) X x} (β : Path p q) :
    genLoopSelfTrackClass m p (track H hH m p) =
      genLoopSelfTrackClass m q (track H hH m q) := by
  have ht := genLoopSelfTrackNormalization_transport m β
    (⟦track H hH m p⟧ : FundamentalGroup _ p)
  rw [track_transport H hH m β] at ht
  exact ht.symm

/-- Descent uses the original boundary-relative homotopy quotient. -/
def operation (m : ℕ) : HomotopyGroup.Pi (m + 1) X x → HomotopyGroup.Pi (m + 2) X x :=
  Quotient.lift (fun p => genLoopSelfTrackClass m p (track H hH m p)) (by
    intro p q hpq
    obtain ⟨K⟩ := hpq
    exact class_eq_of_path H hH m (genLoopPathOfHomotopyRel K))

/-- The descended operation retains its original input cube and entire track. -/
@[simp] theorem operation_mk (m : ℕ) (p : GenLoop (Fin (m + 1)) X x) :
    operation H hH m ⟦p⟧ = genLoopSelfTrackClass m p (track H hH m p) := rfl

/-- The fixed original basepoint makes the constant input operation trivial. -/
@[simp] theorem operation_one (m : ℕ) : operation H hH m 1 = 1 := by
  change genLoopSelfTrackClass m GenLoop.const (track H hH m GenLoop.const) = 1
  have ht : track H hH m GenLoop.const = Path.refl GenLoop.const := by
    ext t s
    exact hH t
  rw [ht, genLoopSelfTrackClass_refl]

private theorem track_transAt (m : ℕ) (i : Fin (m + 1))
    (p q : GenLoop (Fin (m + 1)) X x) :
    track H hH m (GenLoop.transAt i p q) =
      genLoopTransAtPath i (track H hH m p) (track H hH m q) := by
  ext t s
  change H (t, GenLoop.transAt i p q s) =
    GenLoop.transAt i (track H hH m p t) (track H hH m q t) s
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

/-- For input degree at least two, the distinct second spatial coordinate
proves additivity without any action-triviality assumption. -/
theorem operation_mul_succ (m : ℕ)
    (a b : HomotopyGroup.Pi (m + 2) X x) :
    operation H hH (m + 1) (a * b) =
      operation H hH (m + 1) a * operation H hH (m + 1) b := by
  refine Quotient.inductionOn₂ a b ?_
  intro p q
  refine (congrArg (operation H hH (m + 1))
    (HomotopyGroup.mul_spec (i := (1 : Fin (m + 2))) (p := p) (q := q))).trans ?_
  rw [operation_mk, track_transAt, ← genLoopNormalizedSelfTrackCube_class,
    genLoopNormalizedSelfTrackCube_transAt (m + 1) (1 : Fin (m + 2)) (by
      intro h
      have hval := congrArg Fin.val h
      simp at hval)]
  exact (HomotopyGroup.mul_spec (i := (1 : Fin (m + 2)).succ)
    (p := genLoopNormalizedSelfTrackCube (m + 1) p (track H hH (m + 1) p))
    (q := genLoopNormalizedSelfTrackCube (m + 1) q (track H hH (m + 1) q))).symm.trans
      (congrArg₂ (· * ·) (genLoopNormalizedSelfTrackCube_class (m + 1) p _)
        (genLoopNormalizedSelfTrackCube_class (m + 1) q _))

/-- The higher source operation as an actual homomorphism. -/
def hom (m : ℕ) : HomotopyGroup.Pi (m + 2) X x →* HomotopyGroup.Pi (m + 3) X x where
  toFun := operation H hH (m + 1)
  map_one' := operation_one H hH (m + 1)
  map_mul' := operation_mul_succ H hH m

/-- Time concatenation uses the library's original track-product order. -/
theorem operation_trans
    (K : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (hK : ∀ t, K (t, x) = x)
    (hHK : ∀ t, (H.trans K) (t, x) = x) (m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) X x) :
    operation (H.trans K) hHK m a = operation K hK m a * operation H hH m a := by
  refine Quotient.inductionOn a ?_
  intro p
  have ht : track (H.trans K) hHK m p = (track H hH m p).trans (track K hK m p) := by
    ext t z
    change (H.trans K) (t, p z) = _
    simp only [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs <;> rfl
  exact (congrArg (genLoopSelfTrackClass m p) ht).trans
    (genLoopSelfTrackClass_trans m p _ _)

/-- Strictly commuting whole self-homotopies give natural operations on
the original homotopy groups, with the original based map. -/
theorem operation_natural
    {Y : Type v} [TopologicalSpace Y] {y : Y}
    (K : (ContinuousMap.id Y).Homotopy (ContinuousMap.id Y))
    (hK : ∀ t, K (t, y) = y) (f : C(X, Y)) (hf : f x = y)
    (hsq : ∀ t z, f (H (t, z)) = K (t, f z)) (m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) X x) :
    HomotopyGroup.piMap (m + 1) f hf (operation H hH m a) =
      operation K hK m (HomotopyGroup.piMap m f hf a) := by
  refine Quotient.inductionOn a ?_
  intro p
  change HomotopyGroup.piMap (m + 1) f hf (genLoopSelfTrackClass m p (track H hH m p)) = _
  rw [genLoopSelfTrackClass_naturality]
  have ht : ((track H hH m p).map (genLoopPostcompContinuousMap f hf).continuous) =
      track K hK m (GenLoop.postcomp f hf p) := by
    ext t z
    exact hsq t (p z)
  rw [ht]
  rfl

/-- A two-parameter homotopy fixing both track endpoints and the original
basepoint gives a relative homotopy between the actual cube tracks. -/
def trackHomotopy
    (K : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (hK : ∀ t, K (t, x) = x)
    (J : H.toContinuousMap.HomotopyRel K.toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1})
    (hJ : ∀ s t, J (s, (t, x)) = x)
    (m : ℕ) (p : GenLoop (Fin (m + 1)) X x) :
    (track H hH m p).Homotopy (track K hK m p) where
  toFun st := ⟨⟨fun z => J (st.1, (st.2, p z)), by fun_prop⟩, by
    intro z hz
    exact (congrArg (fun y => J (st.1, (st.2, y))) (p.property z hz)).trans (hJ st.1 st.2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × unitInterval) × (Fin (m + 1) → unitInterval) =>
      J (z.1.1, (z.1.2, p z.2)))
    fun_prop
  map_zero_left t := by ext z; exact J.apply_zero (t, p z)
  map_one_left t := by ext z; exact J.apply_one (t, p z)
  prop' s t ht := by
    ext z
    change J (s, (t, p z)) = H (t, p z)
    apply J.eq_fst s
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq] using ht

/-- The operation depends only on the whole relative self-homotopy class;
pointwise homotopies without joint continuity would not suffice here. -/
theorem operation_eq_of_relative_homotopy
    (K : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (hK : ∀ t, K (t, x) = x)
    (J : H.toContinuousMap.HomotopyRel K.toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1})
    (hJ : ∀ s t, J (s, (t, x)) = x)
    (m : ℕ) (a : HomotopyGroup.Pi (m + 1) X x) :
    operation H hH m a = operation K hK m a := by
  refine Quotient.inductionOn a ?_
  intro p
  exact (genLoopSelfTrackClass_eq_iff m p _ _).mpr ⟨trackHomotopy H hH K hK J hJ m p⟩

end Topology.IdentityTrack
