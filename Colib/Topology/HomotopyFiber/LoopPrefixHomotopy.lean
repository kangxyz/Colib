/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LoopPrefixNaturality
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
Implementation provenance:
`Quillen/Topology/HomotopyFiber/LoopPrefixHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Forward loop comparison for an actual homotopy square -/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v u' v'
namespace Topology.HomotopyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- Prefixing paths is an actual continuous map. -/
def pathPrefix {a b c : Y} (p : Path a b) : C(Path b c, Path a c) :=
  ⟨fun q ↦ p.trans q, by fun_prop⟩

/-- Path associativity is jointly continuous in the final path and homotopy parameter. -/
lemma continuous_pathAssociator {a b c d : Y} (p : Path a b) (q : Path b c) :
    Continuous (fun z : unitInterval × Path c d ↦
      (Path.Homotopy.transAssoc p q z.2).eval z.1) := by
  apply Path.continuous_uncurry_iff.mp
  change Continuous (fun z : (unitInterval × Path c d) × unitInterval ↦
    (Path.Homotopy.transAssoc p q z.1.2) (z.1.1, z.2))
  change Continuous (fun z : (unitInterval × Path c d) × unitInterval ↦
    (p.trans (q.trans z.1.2)) ⟨↑(unitInterval.symm (unitInterval.symm z.1.1)) * ↑z.2 +
      ↑(unitInterval.symm z.1.1) * Path.Homotopy.transAssocReparamAux z.2, _⟩)
  fun_prop

/-- The original associator homotopy for continuously varying final paths. -/
def pathPrefixAssociator {a b c d : Y} (p : Path a b) (q : Path b c) :
    (pathPrefix (c := d) (p.trans q)).Homotopy
      ((pathPrefix p).comp (pathPrefix q)) where
  toFun z := (Path.Homotopy.transAssoc p q z.2).eval z.1
  continuous_toFun := continuous_pathAssociator p q
  map_zero_left r := by ext t; exact (Path.Homotopy.transAssoc p q r).apply_zero t
  map_one_left r := by ext t; exact (Path.Homotopy.transAssoc p q r).apply_one t

/-- The original homotopy-square fiber map, retaining the reversed square track. -/
def homotopySquareMap {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u)) (y : Y) :
    C(HomotopyFiber f y, HomotopyFiber f' (v y)) :=
  (sourceMap f' u (v y)).comp ((homotopyMap H (v y)).comp
    (map (ContinuousMap.id X) v rfl y))

/-- The actual source coordinate of the homotopy-square map. -/
theorem homotopySquareMap_source {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (y : Y) (z : HomotopyFiber f y) :
    (homotopySquareMap u v H y z).val.1 = u z.val.1 := rfl

/-- The square map prefixes exactly the reversed original track. -/
theorem homotopySquareMap_path {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (y : Y) (z : HomotopyFiber f y) :
    (homotopySquareMap u v H y z).val.2 =
      ((H.evalAt z.val.1).symm.trans ((toPath f y z).map v.continuous)).toContinuousMap := rfl

/-- The forward square uses the actual associator, without a naturality assumption
on any chosen inverse or contraction. -/
def loopPrefixHomotopySquare {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (x : X) (y : Y) (γ : Path (f x) y) :
    ((loopPrefix f' (u x) (v y)
      ((H.evalAt x).symm.trans (γ.map v.continuous))).comp
        (basedLoopMap (x := y) (y := v y) v rfl)).Homotopy
        ((homotopySquareMap u v H y).comp (loopPrefix f x y γ)) where
  toFun z := by
    let P : Path (f' (u x)) (v y) :=
      pathPrefixAssociator (H.evalAt x).symm (γ.map v.continuous)
        (z.1, basedLoopMap (x := y) (y := v y) v rfl z.2)
    exact ⟨(u x, P.toContinuousMap), P.source, P.target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_const
    have hc := (pathPrefixAssociator (d := v y)
      (H.evalAt x).symm (γ.map v.continuous)).continuous.comp
        (show Continuous (fun z : unitInterval × Path y y ↦
          (z.1, basedLoopMap (x := y) (y := v y) v rfl z.2)) from
          continuous_fst.prodMk ((basedLoopMap v rfl).continuous.comp continuous_snd))
    exact continuous_induced_dom.comp hc
  map_zero_left δ := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    exact congrArg Path.toContinuousMap
      ((pathPrefixAssociator (H.evalAt x).symm (γ.map v.continuous)).apply_zero
        (basedLoopMap v rfl δ))
  map_one_left δ := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    change (pathPrefixAssociator (H.evalAt x).symm (γ.map v.continuous)
      (1, basedLoopMap v rfl δ)).toContinuousMap = _
    rw [(pathPrefixAssociator (H.evalAt x).symm (γ.map v.continuous)).apply_one]
    apply ContinuousMap.ext
    intro t
    change ((H.evalAt x).symm.trans ((γ.map v.continuous).trans
      (basedLoopMap v rfl δ))) t =
        ((H.evalAt x).symm.trans ((γ.trans δ).map v.continuous)) t
    rw [Path.map_trans]
    rfl

/-- The square homotopy keeps the actual total-space point fixed throughout. -/
theorem loopPrefixHomotopySquare_source {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (x : X) (y : Y) (γ : Path (f x) y) (t : unitInterval) (δ : Path y y) :
    (loopPrefixHomotopySquare u v H x y γ (t, δ)).val.1 = u x := rfl

/-- Its complete unit track is the original associator with the actual constant loop. -/
theorem loopPrefixHomotopySquare_unit_track {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (x : X) (y : Y) (γ : Path (f x) y) (t : unitInterval) :
    (loopPrefixHomotopySquare u v H x y γ (t, Path.refl y)).val.2 =
      ((Path.Homotopy.transAssoc (H.evalAt x).symm (γ.map v.continuous)
        (Path.refl (v y))).eval t).toContinuousMap := rfl

end Topology.HomotopyFiber
