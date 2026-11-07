/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackSpatial
public import Colib.Topology.HomotopyFiber.LoopPrefixUnitCoherence
public import Colib.Topology.Homotopy.SquareBoundaryPaths

/-! # Original inverse-prefix and supplied-null coherence on generalized loops

All paths use coordinate zero of the original cube. The entire supplied null path survives
four actual square comparisons and the original associator/unit coherence, including degree one.
-/
/-! Adapted from `Quillen/Topology/HomotopyGroups/GenLoopPrefixNullCoherence.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual paths and coordinates. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology.GenLoopPrefix
variable {X : Type u} [TopologicalSpace X] {x : X} (n : ℕ)

/-- The original continuous spatial prefix, in coordinate zero. -/
def prefixMap (p : GenLoop (Fin (n + 1)) X x) :
    C(GenLoop (Fin (n + 1)) X x, GenLoop (Fin (n + 1)) X x) :=
  (genLoopTransAtContinuousMap 0).comp
    ⟨fun q ↦ (p, q), continuous_const.prodMk continuous_id⟩

/-- The original continuous spatial suffix, in coordinate zero. -/
def suffix (q : GenLoop (Fin (n + 1)) X x) :
    C(GenLoop (Fin (n + 1)) X x, GenLoop (Fin (n + 1)) X x) :=
  (genLoopTransAtContinuousMap 0).comp
    ⟨fun p ↦ (p, q), continuous_id.prodMk continuous_const⟩

/-- The original coordinate homeomorphism preserves the displayed concatenation. -/
theorem toLoop_trans (p q : GenLoop (Fin (n + 1)) X x) :
    GenLoop.toLoop 0 (GenLoop.transAt 0 p q) =
      (GenLoop.toLoop 0 p).trans (GenLoop.toLoop 0 q) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

/-- The original constant cube corresponds to the literal constant residual-cube loop. -/
theorem toLoop_const :
    GenLoop.toLoop (X := X) (x := x) (0 : Fin (n + 1)) GenLoop.const =
      Path.refl GenLoop.const := by
  ext t z
  rfl

/-- Restoring the original constant residual-cube loop gives the original constant cube. -/
theorem fromLoop_const :
    GenLoop.fromLoop (X := X) (x := x) (0 : Fin (n + 1)) (Path.refl GenLoop.const) =
      GenLoop.const := by
  ext z
  rfl

/-- The original associator is jointly continuous in the final cube. -/
def associatorFamily (p q : GenLoop (Fin (n + 1)) X x) :
    C(unitInterval × GenLoop (Fin (n + 1)) X x, GenLoop (Fin (n + 1)) X x) :=
  (⟨GenLoop.fromLoop 0, GenLoop.continuous_fromLoop 0⟩ :
    C(Path (GenLoop.const : GenLoop {j : Fin (n + 1) // j ≠ 0} X x) GenLoop.const,
      GenLoop (Fin (n + 1)) X x)).comp
    ((HomotopyFiber.pathPrefixAssociator (GenLoop.toLoop 0 p)
      (GenLoop.toLoop 0 q)).toContinuousMap.comp
        ⟨fun z ↦ (z.1, GenLoop.toLoop 0 z.2),
          continuous_fst.prodMk ((GenLoop.continuous_toLoop 0).comp continuous_snd)⟩)

/-- The composition keeps the complete original jointly continuous path associator. -/
theorem associatorFamily_apply (p q r : GenLoop (Fin (n + 1)) X x) (t : unitInterval) :
    associatorFamily n p q (t, r) = GenLoop.fromLoop 0
      (HomotopyFiber.pathPrefixAssociator (GenLoop.toLoop 0 p) (GenLoop.toLoop 0 q)
        (t, GenLoop.toLoop 0 r)) := rfl

/-- The initial associator face retains the original left-parenthesized cube. -/
theorem associatorFamily_zero (p q r : GenLoop (Fin (n + 1)) X x) :
    associatorFamily n p q (0, r) = GenLoop.transAt 0 (GenLoop.transAt 0 p q) r := by
  rw [associatorFamily_apply, ContinuousMap.Homotopy.apply_zero]
  change GenLoop.fromLoop 0 (((GenLoop.toLoop 0 p).trans (GenLoop.toLoop 0 q)).trans
    (GenLoop.toLoop 0 r)) = _
  rw [← toLoop_trans n, GenLoop.fromLoop_trans_toLoop]

/-- The final associator face retains the original right-parenthesized cube. -/
theorem associatorFamily_one (p q r : GenLoop (Fin (n + 1)) X x) :
    associatorFamily n p q (1, r) = GenLoop.transAt 0 p (GenLoop.transAt 0 q r) := by
  rw [associatorFamily_apply, ContinuousMap.Homotopy.apply_one]
  change GenLoop.fromLoop 0 ((GenLoop.toLoop 0 p).trans
    ((GenLoop.toLoop 0 q).trans (GenLoop.toLoop 0 r))) = _
  rw [← toLoop_trans n, GenLoop.fromLoop_trans_toLoop]

/-- The actual spatial associator, retaining its original homotopy parameter. -/
def associator (p q r : GenLoop (Fin (n + 1)) X x) :
    Path (GenLoop.transAt 0 (GenLoop.transAt 0 p q) r)
      (GenLoop.transAt 0 p (GenLoop.transAt 0 q r)) where
  toFun t := associatorFamily n p q (t, r)
  continuous_toFun := (associatorFamily n p q).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := associatorFamily_zero n p q r
  target' := associatorFamily_one n p q r

/-- The complete original constant-prefix delay. -/
def leftUnitFamily :
    C(unitInterval × GenLoop (Fin (n + 1)) X x, GenLoop (Fin (n + 1)) X x) where
  toFun z := GenLoop.fromLoop 0 (Path.delayReflLeft z.1 (GenLoop.toLoop 0 z.2))
  continuous_toFun := (GenLoop.continuous_fromLoop 0).comp
    (Path.continuous_delayReflLeft.comp
      (continuous_fst.prodMk ((GenLoop.continuous_toLoop 0).comp continuous_snd)))

/-- The complete original constant-suffix delay. -/
def rightUnitFamily :
    C(unitInterval × GenLoop (Fin (n + 1)) X x, GenLoop (Fin (n + 1)) X x) where
  toFun z := GenLoop.fromLoop 0 (Path.delayReflRight z.1 (GenLoop.toLoop 0 z.2))
  continuous_toFun := (GenLoop.continuous_fromLoop 0).comp
    (Path.continuous_delayReflRight.comp
      (continuous_fst.prodMk ((GenLoop.continuous_toLoop 0).comp continuous_snd)))

/-- Remove the actual constant spatial prefix. -/
def leftUnit (p : GenLoop (Fin (n + 1)) X x) :
    Path (GenLoop.transAt 0 GenLoop.const p) p where
  toFun t := leftUnitFamily n (t, p)
  continuous_toFun := (leftUnitFamily n).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := by
    change GenLoop.fromLoop 0 (Path.delayReflLeft 0 (GenLoop.toLoop 0 p)) = _
    rw [Path.delayReflLeft_zero, ← toLoop_const n, GenLoop.fromLoop_trans_toLoop]
  target' := by
    change GenLoop.fromLoop 0 (Path.delayReflLeft 1 (GenLoop.toLoop 0 p)) = _
    rw [Path.delayReflLeft_one]
    exact (GenLoop.loopHomeo 0).symm_apply_apply p

/-- Remove the actual constant spatial suffix. -/
def rightUnit (p : GenLoop (Fin (n + 1)) X x) :
    Path (GenLoop.transAt 0 p GenLoop.const) p where
  toFun t := rightUnitFamily n (t, p)
  continuous_toFun := (rightUnitFamily n).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := by
    change GenLoop.fromLoop 0 (Path.delayReflRight 0 (GenLoop.toLoop 0 p)) = _
    rw [Path.delayReflRight_zero, ← toLoop_const n, GenLoop.fromLoop_trans_toLoop]
  target' := by
    change GenLoop.fromLoop 0 (Path.delayReflRight 1 (GenLoop.toLoop 0 p)) = _
    rw [Path.delayReflRight_one]
    exact (GenLoop.loopHomeo 0).symm_apply_apply p

/-- Both original unit tracks at the constant cube retain their actual common endpoints. -/
theorem unit_const :
    rightUnit (X := X) (x := x) n GenLoop.const = leftUnit n GenLoop.const := by
  apply Path.ext
  funext t
  ext z
  rfl

/-- The original inverse-prefix map. -/
def inversePrefix (a : GenLoop (Fin (n + 1)) X x) :
    C(GenLoop (Fin (n + 1)) X x, GenLoop (Fin (n + 1)) X x) :=
  prefixMap n (GenLoop.symmAt 0 a)

/-- The complete original cancellation, with both restored endpoint casts. -/
def cancellation (a : GenLoop (Fin (n + 1)) X x) :
    Path (inversePrefix n a a) GenLoop.const := by
  let L := GenLoop.loopHomeo (X := X) (x := x) (0 : Fin (n + 1))
  have hs : inversePrefix n a a =
      L.symm ((L a).symm.trans (L a)) := by
    change GenLoop.transAt 0 (GenLoop.symmAt 0 a) a = _
    rw [← GenLoop.fromLoop_symm_toLoop]
    rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]
    rfl
  have ht : (GenLoop.const : GenLoop (Fin (n + 1)) X x) =
      L.symm (Path.refl GenLoop.const) := (fromLoop_const n).symm
  exact ((loopInversePrefixCancellation (L a)).map L.symm.continuous).cast hs ht

/-- The complete inverse-associator, supplied return, and original left-unit tail. -/
def tail (rho q c : GenLoop (Fin (n + 1)) X x)
    (nu : Path (GenLoop.transAt 0 rho q) GenLoop.const) :
    Path (GenLoop.transAt 0 rho (GenLoop.transAt 0 q c)) c :=
  (associator n rho q c).symm.trans
    ((nu.map (suffix n c).continuous).trans (leftUnit n c))

/-- Restore a literal prefix with an arbitrary original residual-loop suffix. -/
theorem fromLoop_prefix (p : GenLoop (Fin (n + 1)) X x)
    (r : Path (GenLoop.const : GenLoop {j : Fin (n + 1) // j ≠ 0} X x) GenLoop.const) :
    GenLoop.fromLoop 0 ((GenLoop.toLoop 0 p).trans r) =
      GenLoop.transAt 0 p (GenLoop.fromLoop 0 r) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

/-- The already constructed original unit/associator homotopy on coordinate-zero cubes. -/
def unitAssociator (p q : GenLoop (Fin (n + 1)) X x) :
    (rightUnit n (GenLoop.transAt 0 p q)).Homotopy
      ((associator n p q GenLoop.const).trans
        ((rightUnit n q).map (prefixMap n p).continuous)) := by
  let M : C(Path (GenLoop.const : GenLoop {j : Fin (n + 1) // j ≠ 0} X x)
      GenLoop.const, GenLoop (Fin (n + 1)) X x) :=
    ⟨GenLoop.fromLoop 0, GenLoop.continuous_fromLoop 0⟩
  have hs : GenLoop.transAt 0 (GenLoop.transAt 0 p q) GenLoop.const =
      M (((GenLoop.toLoop 0 p).trans (GenLoop.toLoop 0 q)).trans
        (Path.refl GenLoop.const)) := by
    change _ = GenLoop.fromLoop 0 _
    rw [← GenLoop.fromLoop_trans_toLoop, toLoop_trans n, toLoop_const n]
  have ht : GenLoop.transAt 0 p q =
      M ((GenLoop.toLoop 0 p).trans (GenLoop.toLoop 0 q)) :=
    GenLoop.fromLoop_trans_toLoop.symm
  let H := ((HomotopyFiber.pathUnitAssociatorHomotopy (GenLoop.toLoop 0 p)
    (GenLoop.toLoop 0 q)).map M).pathCast hs ht
  refine H.cast ?_ ?_
  · apply Path.ext
    funext t
    change GenLoop.fromLoop 0
      (Path.delayReflRight t ((GenLoop.toLoop 0 p).trans (GenLoop.toLoop 0 q))) =
      GenLoop.fromLoop 0 (Path.delayReflRight t (GenLoop.toLoop 0 (GenLoop.transAt 0 p q)))
    rw [toLoop_trans n]
  · apply Path.ext
    funext t
    change M (HomotopyFiber.pathAssociatorUnitRoute
      (GenLoop.toLoop 0 p) (GenLoop.toLoop 0 q) t) = _
    unfold HomotopyFiber.pathAssociatorUnitRoute
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · change GenLoop.fromLoop 0 ((Path.Homotopy.transAssoc _ _ (Path.refl _)).eval _) =
        GenLoop.fromLoop 0 ((Path.Homotopy.transAssoc _ _
          (GenLoop.toLoop 0 GenLoop.const)).eval _)
      rw [toLoop_const n]
      rfl
    · exact fromLoop_prefix n p _

/-- Compare the four supplied entire edges using the original square interpolation. -/
def squareEdges {Y : Type v} [TopologicalSpace Y] {a b c d : Y}
    (L : Path a b) (T : Path b d) (B : Path a c) (R : Path c d)
    (F : C(unitInterval × unitInterval, Y))
    (hL : ∀ t, F (0, t) = L t) (hT : ∀ t, F (t, 1) = T t)
    (hB : ∀ t, F (t, 0) = B t) (hR : ∀ t, F (1, t) = R t) :
    (L.trans T).Homotopy (B.trans R) := by
  have ha : a = F (0, 0) := ((hL 0).trans L.source).symm
  have hd : d = F (1, 1) := ((hT 1).trans T.target).symm
  refine ((squareBoundaryPathHomotopy F).pathCast ha hd).cast ?_ ?_
  · apply Path.ext
    funext t
    change (((Path.refl (0 : unitInterval)).prod Path.id).map F.continuous |>.trans
      ((Path.id.prod (Path.refl (1 : unitInterval))).map F.continuous)) t = (L.trans T) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hL _
    · exact hT _
  · apply Path.ext
    funext t
    change (((Path.id.prod (Path.refl (0 : unitInterval))).map F.continuous).trans
      (((Path.refl (1 : unitInterval)).prod Path.id).map F.continuous)) t = (B.trans R) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hB _
    · exact hR _

/-- The original associator square evaluates the entire supplied null path. -/
def associatorNull (rho q c : GenLoop (Fin (n + 1)) X x)
    (N : Path c GenLoop.const) :
    ((N.map (prefixMap n (GenLoop.transAt 0 rho q)).continuous).trans
      (associator n rho q GenLoop.const)).Homotopy
    ((associator n rho q c).trans
      ((N.map (prefixMap n q).continuous).map (prefixMap n rho).continuous)) := by
  let F : C(unitInterval × unitInterval, GenLoop (Fin (n + 1)) X x) :=
    (associatorFamily n rho q).comp
      ⟨fun z ↦ (z.1, N z.2), continuous_fst.prodMk (N.continuous.comp continuous_snd)⟩
  refine squareEdges _ _ _ _ F ?_ ?_ ?_ ?_
  · intro t
    exact associatorFamily_zero n rho q (N t)
  · intro t
    change associatorFamily n rho q (t, N 1) = _
    rw [N.target]
    rfl
  · intro t
    change associatorFamily n rho q (t, N 0) = _
    rw [N.source]
    rfl
  · intro t
    exact associatorFamily_one n rho q (N t)

/-- The entire right-unit square retains the supplied moving return path. -/
def rightUnitNull {p : GenLoop (Fin (n + 1)) X x}
    (nu : Path p GenLoop.const) :
    ((nu.map (suffix n GenLoop.const).continuous).trans
      (rightUnit n GenLoop.const)).Homotopy ((rightUnit n p).trans nu) := by
  let F : C(unitInterval × unitInterval, GenLoop (Fin (n + 1)) X x) :=
    (rightUnitFamily n).comp
      ⟨fun z ↦ (z.1, nu z.2), continuous_fst.prodMk (nu.continuous.comp continuous_snd)⟩
  refine squareEdges _ _ _ _ F ?_ ?_ ?_ ?_
  · intro t
    exact (rightUnit n (nu t)).source
  · intro t
    change rightUnitFamily n (t, nu 1) = _
    rw [nu.target]
    rfl
  · intro t
    change rightUnitFamily n (t, nu 0) = _
    rw [nu.source]
    rfl
  · intro t
    exact (rightUnit n (nu t)).target

/-- The entire left-unit square retains the supplied null path. -/
def leftUnitNull {c : GenLoop (Fin (n + 1)) X x}
    (N : Path c GenLoop.const) :
    ((N.map (prefixMap n GenLoop.const).continuous).trans
      (leftUnit n GenLoop.const)).Homotopy ((leftUnit n c).trans N) := by
  let F : C(unitInterval × unitInterval, GenLoop (Fin (n + 1)) X x) :=
    (leftUnitFamily n).comp
      ⟨fun z ↦ (z.1, N z.2), continuous_fst.prodMk (N.continuous.comp continuous_snd)⟩
  refine squareEdges _ _ _ _ F ?_ ?_ ?_ ?_
  · intro t
    exact (leftUnit n (N t)).source
  · intro t
    change leftUnitFamily n (t, N 1) = _
    rw [N.target]
    rfl
  · intro t
    change leftUnitFamily n (t, N 0) = _
    rw [N.source]
    rfl
  · intro t
    exact (leftUnit n (N t)).target

/-- The actual two-time return/null square retains both complete supplied paths. -/
def interchangeNull {p c : GenLoop (Fin (n + 1)) X x}
    (nu : Path p GenLoop.const) (N : Path c GenLoop.const) :
    ((N.map (prefixMap n p).continuous).trans
      (nu.map (suffix n GenLoop.const).continuous)).Homotopy
    ((nu.map (suffix n c).continuous).trans
      (N.map (prefixMap n GenLoop.const).continuous)) := by
  let F : C(unitInterval × unitInterval, GenLoop (Fin (n + 1)) X x) :=
    (genLoopTransAtContinuousMap 0).comp
      ⟨fun z ↦ (nu z.1, N z.2),
        (nu.continuous.comp continuous_fst).prodMk (N.continuous.comp continuous_snd)⟩
  refine squareEdges _ _ _ _ F ?_ ?_ ?_ ?_
  · intro t
    change GenLoop.transAt 0 (nu 0) (N t) = _
    rw [nu.source]
    rfl
  · intro t
    change GenLoop.transAt 0 (nu t) (N 1) = _
    rw [N.target]
    rfl
  · intro t
    change GenLoop.transAt 0 (nu t) (N 0) = _
    rw [N.source]
    rfl
  · intro t
    change GenLoop.transAt 0 (nu 1) (N t) = _
    rw [nu.target]
    rfl

/-- Remove a displayed prefix by the original associator and cancellation homotopies. -/
def unprefix {Y : Type v} [TopologicalSpace Y] {a b c : Y}
    (A : Path a b) (B : Path b c) (D : Path a c)
    (J : (A.trans B).Homotopy D) : B.Homotopy (A.symm.trans D) :=
  (Path.Homotopy.reflTrans B).symm.trans
    (((Path.Homotopy.reflSymmTrans A).hcomp (Path.Homotopy.refl B)).trans
      ((Path.Homotopy.transAssoc A.symm A B).trans
        ((Path.Homotopy.refl A.symm).hcomp J)))

/-- Actual inverse-prefix/null coherence, preserving the complete supplied null path. -/
def nullCoherence (rho q c : GenLoop (Fin (n + 1)) X x)
    (N : Path c GenLoop.const) (nu : Path (GenLoop.transAt 0 rho q) GenLoop.const) :
    ((((N.map (prefixMap n q).continuous).trans (rightUnit n q)).map
      (prefixMap n rho).continuous).trans nu).Homotopy ((tail n rho q c nu).trans N) := by
  let A := associator n rho q c
  let Ae := associator n rho q GenLoop.const
  let D := N.map (prefixMap n (GenLoop.transAt 0 rho q)).continuous
  let L := (N.map (prefixMap n q).continuous).map (prefixMap n rho).continuous
  let R := (rightUnit n q).map (prefixMap n rho).continuous
  let Vc := nu.map (suffix n c).continuous
  let Ve := nu.map (suffix n GenLoop.const).continuous
  let EN := N.map (prefixMap n GenLoop.const).continuous
  let B := (L.trans R).trans nu
  let RU := rightUnit n (GenLoop.transAt 0 rho q)
  let Re := rightUnit (X := X) (x := x) n GenLoop.const
  let Le := leftUnit (X := X) (x := x) n GenLoop.const
  let Lc := leftUnit n c
  have h1 : (A.trans B).Homotopy (((A.trans L).trans R).trans nu) :=
    (Path.Homotopy.transAssoc A (L.trans R) nu).symm.trans
      ((Path.Homotopy.transAssoc A L R).symm.hcomp (Path.Homotopy.refl nu))
  have h2 : (((A.trans L).trans R).trans nu).Homotopy
      (((D.trans Ae).trans R).trans nu) :=
    ((associatorNull n rho q c N).symm.hcomp (Path.Homotopy.refl R)).hcomp
      (Path.Homotopy.refl nu)
  have h3 : (((D.trans Ae).trans R).trans nu).Homotopy ((D.trans RU).trans nu) :=
    ((Path.Homotopy.transAssoc D Ae R).trans
      ((Path.Homotopy.refl D).hcomp (unitAssociator n rho q).symm)).hcomp
        (Path.Homotopy.refl nu)
  have h4 : ((D.trans RU).trans nu).Homotopy ((D.trans Ve).trans Re) :=
    (Path.Homotopy.transAssoc D RU nu).trans
      (((Path.Homotopy.refl D).hcomp (rightUnitNull n nu).symm).trans
        (Path.Homotopy.transAssoc D Ve Re).symm)
  have h5 : ((D.trans Ve).trans Re).Homotopy ((Vc.trans EN).trans Le) :=
    ((interchangeNull n nu N).hcomp (Path.Homotopy.refl Re)).cast rfl
      (congrArg (fun p ↦ (Vc.trans EN).trans p) (unit_const n))
  have h6 : ((Vc.trans EN).trans Le).Homotopy ((Vc.trans Lc).trans N) :=
    (Path.Homotopy.transAssoc Vc EN Le).trans
      (((Path.Homotopy.refl Vc).hcomp (leftUnitNull n N)).trans
        (Path.Homotopy.transAssoc Vc Lc N).symm)
  let J := h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))
  have K : B.Homotopy ((A.symm.trans (Vc.trans Lc)).trans N) :=
    (unprefix A B ((Vc.trans Lc).trans N) J).trans
      (Path.Homotopy.transAssoc A.symm (Vc.trans Lc) N).symm
  simpa only [B, L, R, A, Vc, Lc, tail, Path.map_trans] using K

variable {Y : Type v} [TopologicalSpace Y] {y : Y}

/-- Based postcomposition preserves the original spatial prefix. -/
theorem prefix_map (f : C(X, Y)) (h : f x = y)
    (p q : GenLoop (Fin (n + 1)) X x) :
    GenLoop.postcomp f h (prefixMap n p q) =
      prefixMap n (GenLoop.postcomp f h p) (GenLoop.postcomp f h q) :=
  GenLoop.postcomp_transAt f h 0 p q

/-- Based postcomposition preserves the original coordinate reversal. -/
theorem symm_map (f : C(X, Y)) (h : f x = y)
    (p : GenLoop (Fin (n + 1)) X x) :
    GenLoop.postcomp f h (GenLoop.symmAt 0 p) = GenLoop.symmAt 0 (GenLoop.postcomp f h p) := by
  ext z
  rfl

/-- The whole actual inverse-prefix map retains both original cubes. -/
theorem inversePrefix_map (f : C(X, Y)) (h : f x = y)
    (a p : GenLoop (Fin (n + 1)) X x) :
    GenLoop.postcomp f h (inversePrefix n a p) =
      inversePrefix n (GenLoop.postcomp f h a) (GenLoop.postcomp f h p) := by
  unfold inversePrefix
  rw [prefix_map, symm_map]

/-- The entire original inverse-prefix cancellation is natural with both endpoint transports. -/
theorem cancellation_map (f : C(X, Y)) (h : f x = y)
    (a : GenLoop (Fin (n + 1)) X x) :
    ((cancellation n a).map (genLoopPostcompContinuousMap f h).continuous).cast
      (inversePrefix_map n f h a a).symm (GenLoop.postcomp_const f h).symm =
      cancellation n (GenLoop.postcomp f h a) := by
  apply Path.ext
  funext t
  ext z
  rfl

/-- The original prefix-unit delay is natural at every independent path and cube coordinate. -/
theorem leftUnit_map_apply (f : C(X, Y)) (h : f x = y)
    (p : GenLoop (Fin (n + 1)) X x) (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    f (leftUnit n p t z) = leftUnit n (GenLoop.postcomp f h p) t z := rfl

/-- The original suffix-unit delay is natural at every independent path and cube coordinate. -/
theorem rightUnit_map_apply (f : C(X, Y)) (h : f x = y)
    (p : GenLoop (Fin (n + 1)) X x) (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    f (rightUnit n p t z) = rightUnit n (GenLoop.postcomp f h p) t z := rfl

/-- Pointwise agreement survives the original associator's fixed time reparametrization. -/
theorem associator_pointwise {A : Type*} {B : Type*} {Z : Type*}
    [TopologicalSpace A] [TopologicalSpace B] {a : A} {b : B}
    (u : A → Z) (v : B → Z) (p q r : Path a a) (p' q' r' : Path b b)
    (hp : ∀ s, u (p s) = v (p' s)) (hq : ∀ s, u (q s) = v (q' s))
    (hr : ∀ s, u (r s) = v (r' s)) (t s : unitInterval) :
    u ((Path.Homotopy.transAssoc p q r) (t, s)) =
      v ((Path.Homotopy.transAssoc p' q' r') (t, s)) := by
  change u ((p.trans (q.trans r)) _) = v ((p'.trans (q'.trans r')) _)
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact hp _
  · rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hq _
    · exact hr _

/-- The actual coordinate-zero associator is natural on each entire original cube. -/
theorem associator_map_apply (f : C(X, Y)) (h : f x = y)
    (p q r : GenLoop (Fin (n + 1)) X x) (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    f (associator n p q r t z) =
      associator n (GenLoop.postcomp f h p) (GenLoop.postcomp f h q)
        (GenLoop.postcomp f h r) t z := by
  exact associator_pointwise
    (fun a : GenLoop {j : Fin (n + 1) // j ≠ 0} X x ↦ f (a ((Cube.splitAt 0 z).2)))
    (fun b : GenLoop {j : Fin (n + 1) // j ≠ 0} Y y ↦ b ((Cube.splitAt 0 z).2))
    (GenLoop.toLoop 0 p) (GenLoop.toLoop 0 q) (GenLoop.toLoop 0 r)
    (GenLoop.toLoop 0 (GenLoop.postcomp f h p))
    (GenLoop.toLoop 0 (GenLoop.postcomp f h q))
    (GenLoop.toLoop 0 (GenLoop.postcomp f h r))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) t (z 0)

/-- The original return path after based postcomposition, with both endpoint casts. -/
def mappedReturn (f : C(X, Y)) (h : f x = y)
    (rho q : GenLoop (Fin (n + 1)) X x)
    (nu : Path (GenLoop.transAt 0 rho q) GenLoop.const) :
    Path (GenLoop.transAt 0 (GenLoop.postcomp f h rho) (GenLoop.postcomp f h q)) GenLoop.const :=
  (nu.map (genLoopPostcompContinuousMap f h).continuous).cast
    (GenLoop.postcomp_transAt f h 0 rho q).symm (GenLoop.postcomp_const f h).symm

/-- The exact source comparison for the mapped inverse-associator tail. -/
theorem tail_source_map (f : C(X, Y)) (h : f x = y)
    (rho q c : GenLoop (Fin (n + 1)) X x) :
    GenLoop.postcomp f h (GenLoop.transAt 0 rho (GenLoop.transAt 0 q c)) =
      GenLoop.transAt 0 (GenLoop.postcomp f h rho)
        (GenLoop.transAt 0 (GenLoop.postcomp f h q) (GenLoop.postcomp f h c)) := by
  rw [GenLoop.postcomp_transAt, GenLoop.postcomp_transAt]

/-- The complete tail is natural at each original path and cube coordinate. -/
theorem tail_map_apply (f : C(X, Y)) (h : f x = y)
    (rho q c : GenLoop (Fin (n + 1)) X x)
    (nu : Path (GenLoop.transAt 0 rho q) GenLoop.const)
    (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    f (tail n rho q c nu t z) =
      tail n (GenLoop.postcomp f h rho) (GenLoop.postcomp f h q)
        (GenLoop.postcomp f h c) (mappedReturn n f h rho q nu) t z := by
  unfold tail
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact associator_map_apply n f h rho q c _ z
  · rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact congrArg (fun p : GenLoop (Fin (n + 1)) Y y ↦ p z)
        (GenLoop.postcomp_transAt f h 0 (nu _) c)
    · exact leftUnit_map_apply n f h c _ z

/-- Whole-tail naturality retains the explicit source transport and unchanged target cube. -/
theorem tail_map (f : C(X, Y)) (h : f x = y)
    (rho q c : GenLoop (Fin (n + 1)) X x)
    (nu : Path (GenLoop.transAt 0 rho q) GenLoop.const) :
    ((tail n rho q c nu).map (genLoopPostcompContinuousMap f h).continuous).cast
      (tail_source_map n f h rho q c).symm rfl =
      tail n (GenLoop.postcomp f h rho) (GenLoop.postcomp f h q)
        (GenLoop.postcomp f h c) (mappedReturn n f h rho q nu) := by
  apply Path.ext
  funext t
  ext z
  exact tail_map_apply n f h rho q c nu t z

end Topology.GenLoopPrefix
