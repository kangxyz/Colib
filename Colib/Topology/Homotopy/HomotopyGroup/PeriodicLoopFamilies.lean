/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrack
public import Colib.Topology.Homotopy.ConcatenationFamilies
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.FamilyCommutation
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopPrefixNullCoherence
public import Colib.Topology.Homotopy.HomotopyGroup.SelfTrackLoopShift

/-!
# Periodic loop families, cancellation, capping, and self-track comparison

Periodic loop families, cancellation, capping, and self-track comparison.

All comparisons retain the original maps and require only the stated hypotheses.
-/
/-! Adapted from `Quillen/Topology/HomotopyGroups/PeriodicLoopFamilies.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving actual paths and coordinates. -/
@[expose] public section
noncomputable section
namespace Topology.IdentityTrack
open scoped Topology
universe u v
variable {X : Type u} [TopologicalSpace X] {x : X}
  {Z : Type v} [TopologicalSpace Z]

/-- Concatenate two whole loop-valued families pointwise, retaining the original map. -/
def loopProduct (f g : C(Z, Path x x)) : C(Z, Path x x) :=
  ⟨fun z => (f z).trans (g z), Path.continuous_trans.comp (f.continuous.prodMk g.continuous)⟩

end Topology.IdentityTrack

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u v

namespace Topology.PeriodicFamilies

variable (X : Type u) [TopologicalSpace X]

/-- Periodic squares retain both pairs of opposite edges as literal equalities. -/
def PeriodicSquare := {f : C(unitInterval × unitInterval, X) //
  (∀ s, f (0,s) = f (1,s)) ∧ (∀ t, f (t,0) = f (t,1))}

instance : TopologicalSpace (PeriodicSquare X) := inferInstanceAs (TopologicalSpace
  {f : C(unitInterval × unitInterval, X) //
    (∀ s, f (0,s) = f (1,s)) ∧ (∀ t, f (t,0) = f (t,1))})

/-- The constant periodic square at the given point. -/
def periodicConstant (x : X) : PeriodicSquare X := ⟨ContinuousMap.const _ x, by simp⟩

variable {X} {x : X}

/-- Postcomposition of a periodic square by a continuous map. -/
def periodicPost {Y : Type v} [TopologicalSpace Y] (f : C(X, Y))
    (T : PeriodicSquare X) : PeriodicSquare Y :=
  ⟨f.comp T.val, (fun s => congrArg f (T.property.1 s)),
    (fun t => congrArg f (T.property.2 t))⟩

/-- Restriction of a whole-source homotopy preserves both periodic edge pairs,
including its possibly moving vertex. -/
def periodicPostHomotopy {Y : Type v} [TopologicalSpace Y] {f g : C(X, Y)}
    (H : f.Homotopy g) (T : PeriodicSquare X) :
    Path (periodicPost f T) (periodicPost g T) where
  toFun u := ⟨⟨fun z => H (u,T.val z), by fun_prop⟩,
    (fun s => congrArg (fun y => H (u,y)) (T.property.1 s)),
    (fun t => congrArg (fun y => H (u,y)) (T.property.2 t))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × (unitInterval × unitInterval) => H (z.1,T.val z.2))
    fun_prop
  source' := by apply Subtype.ext; ext z; exact H.apply_zero _
  target' := by apply Subtype.ext; ext z; exact H.apply_one _

/-- Curry the original inner-loop coordinate without changing either torus parameter. -/
def periodicLoop (f : PeriodicSquare (Path x x)) :
    Path (periodicConstant X x) (periodicConstant X x) where
  toFun q := ⟨⟨fun z => f.val z q, by fun_prop⟩,
    (fun s => congrArg (fun p : Path x x => p q) (f.property.1 s)),
    (fun t => congrArg (fun p : Path x x => p q) (f.property.2 t))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × (unitInterval × unitInterval) => f.val z.2 z.1)
    fun_prop
  source' := by apply Subtype.ext; ext z; exact (f.val z).source
  target' := by apply Subtype.ext; ext z; exact (f.val z).target

/-- Restore all three actual coordinates from a loop of periodic squares. -/
def periodicUnloop (p : Path (periodicConstant X x) (periodicConstant X x)) :
    PeriodicSquare (Path x x) :=
  ⟨⟨fun z =>
    { toFun q := (p q).val z
      continuous_toFun := by fun_prop
      source' := by rw [p.source]; rfl
      target' := by rw [p.target]; rfl }, by
      apply Path.continuous_uncurry_iff.mp
      change Continuous (fun z : (unitInterval × unitInterval) × unitInterval => (p z.2).val z.1)
      fun_prop⟩, by
    constructor
    · intro s; apply Path.ext; funext q; exact (p q).property.1 s
    · intro t; apply Path.ext; funext q; exact (p q).property.2 t⟩

/-- Exponential currying is a homeomorphism on the actual periodic subspaces. -/
def periodicLoopHomeomorph : PeriodicSquare (Path x x) ≃ₜ
    Path (periodicConstant X x) (periodicConstant X x) where
  toFun := periodicLoop
  invFun := periodicUnloop
  left_inv f := by apply Subtype.ext; ext z q; rfl
  right_inv p := by apply Path.ext; funext q; apply Subtype.ext; ext z; rfl
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (PeriodicSquare (Path x x) × unitInterval) ×
      (unitInterval × unitInterval) => z.1.1.val z.2 z.1.2)
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (Path (periodicConstant X x) (periodicConstant X x) ×
      (unitInterval × unitInterval)) × unitInterval => (z.1.1 z.2).val z.1.2)
    fun_prop

/-- Pointwise concatenation of two periodic loop families. -/
def periodicConcat (f g : PeriodicSquare (Path x x)) : PeriodicSquare (Path x x) :=
  ⟨⟨fun z => (f.val z).trans (g.val z), by fun_prop⟩,
    (fun s => congrArg₂ Path.trans (f.property.1 s) (g.property.1 s)),
    (fun t => congrArg₂ Path.trans (f.property.2 t) (g.property.2 t))⟩

/-- Pointwise reversal of a periodic loop family. -/
def periodicReverse (f : PeriodicSquare (Path x x)) : PeriodicSquare (Path x x) :=
  ⟨⟨fun z => (f.val z).symm, Path.continuous_symm.comp f.val.continuous⟩,
    (fun s => congrArg Path.symm (f.property.1 s)),
    (fun t => congrArg Path.symm (f.property.2 t))⟩

theorem periodicLoop_concat (f g : PeriodicSquare (Path x x)) :
    periodicLoop (periodicConcat f g) = (periodicLoop f).trans (periodicLoop g) := by
  apply Path.ext
  funext q
  apply Subtype.ext
  ext z
  change (f.val z).trans (g.val z) q = _
  simp only [Path.trans_apply]
  split_ifs <;> rfl

theorem periodicLoop_reverse (f : PeriodicSquare (Path x x)) :
    periodicLoop (periodicReverse f) = (periodicLoop f).symm := by
  apply Path.ext
  funext q
  apply Subtype.ext
  ext z
  rfl

/-- Opposition makes multiplication agree with chronological inner-loop concatenation. -/
abbrev PeriodicLoopClass :=
  (FundamentalGroup (PeriodicSquare X) (periodicConstant X x))ᵐᵒᵖ

/-- The opposite fundamental-group class of the curried periodic family. -/
def periodicClass (f : PeriodicSquare (Path x x)) : PeriodicLoopClass (x := x) :=
  MulOpposite.op (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (periodicLoop f)))

theorem periodicClass_concat (f g : PeriodicSquare (Path x x)) :
    periodicClass (periodicConcat f g) = periodicClass f * periodicClass g := by
  apply MulOpposite.unop_injective
  apply CategoryTheory.End.ext
  change Path.Homotopic.Quotient.mk (periodicLoop (periodicConcat f g)) =
    Path.Homotopic.Quotient.mk ((periodicLoop f).trans (periodicLoop g))
  rw [periodicLoop_concat]

theorem periodicClass_reverse (f : PeriodicSquare (Path x x)) :
    periodicClass (periodicReverse f) = (periodicClass f)⁻¹ := by
  apply MulOpposite.unop_injective
  apply CategoryTheory.End.ext
  change Path.Homotopic.Quotient.mk (periodicLoop (periodicReverse f)) =
    Path.Homotopic.Quotient.mk (periodicLoop f).symm
  rw [periodicLoop_reverse]

/-- A periodic path gives a genuine homotopy of the entire inner-loop path. -/
def periodicPathHomotopy {f g : PeriodicSquare (Path x x)} (P : Path f g) :
    (periodicLoop f).Homotopy (periodicLoop g) where
  toFun z := periodicLoop (P z.1) z.2
  continuous_toFun :=
    Path.continuous_uncurry_iff.mpr (periodicLoopHomeomorph.continuous.comp P.continuous)
  map_zero_left q := by rw [P.source]; rfl
  map_one_left q := by rw [P.target]; rfl
  prop' s q hq := by
    rcases hq with hq | hq
    · subst q; exact (periodicLoop (P s)).source.trans (periodicLoop f).source.symm
    · have hq' : q = 1 := hq
      subst q; exact (periodicLoop (P s)).target.trans (periodicLoop f).target.symm

theorem periodicClass_of_path {f g : PeriodicSquare (Path x x)} (P : Path f g) :
    periodicClass f = periodicClass g :=
  congrArg (fun q => MulOpposite.op (FundamentalGroup.fromPath q))
    (Quotient.sound ⟨periodicPathHomotopy P⟩)

/-- Class equality recovers an actual periodic homotopy, retaining its vertex track. -/
def periodicPathOfClassEq {f g : PeriodicSquare (Path x x)}
    (h : periodicClass f = periodicClass g) : Path f g := by
  have hh : (periodicLoop f).Homotopic (periodicLoop g) :=
    Quotient.exact (congrArg CategoryTheory.End.asHom (MulOpposite.op_injective h))
  let H := hh.some
  let P : Path (periodicLoop f) (periodicLoop g) := {
    toFun s := H.eval s
    continuous_toFun := Path.continuous_uncurry_iff.mp H.continuous
    source' := Path.Homotopy.eval_zero H
    target' := Path.Homotopy.eval_one H }
  exact (P.map periodicLoopHomeomorph.symm.continuous).cast
    (periodicLoopHomeomorph.symm_apply_apply f).symm
    (periodicLoopHomeomorph.symm_apply_apply g).symm

end Topology.PeriodicFamilies

end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u v

namespace Topology.PeriodicFamilies
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The periodic square obtained from a loop along the chosen axis. -/
def axisFamily {Y : Type u} [TopologicalSpace Y] {y : Y} (first : Bool)
    (α : Path y y) : PeriodicSquare Y :=
  ⟨⟨fun z => α (if first then z.1 else z.2), by cases first <;> dsimp <;> fun_prop⟩, by
    constructor
    · intro s; cases first
      · rfl
      · exact α.source.trans α.target.symm
    · intro t; cases first
      · exact α.source.trans α.target.symm
      · rfl⟩

/-- The path of axis squares induced by a based loop homotopy. -/
def axisHomotopy {Y : Type u} [TopologicalSpace Y] {y : Y} (first : Bool)
    {α β : Path y y} (H : α.Homotopy β) : Path (axisFamily first α) (axisFamily first β) where
  toFun r := ⟨⟨fun z => H (r, if first then z.1 else z.2), by
    cases first <;> dsimp <;> fun_prop⟩, by
    constructor
    · intro s; cases first
      · rfl
      · exact (H.eval r).source.trans (H.eval r).target.symm
    · intro t; cases first
      · exact (H.eval r).source.trans (H.eval r).target.symm
      · rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × (unitInterval × unitInterval) =>
      H (z.1, if first then z.2.1 else z.2.2))
    cases first <;> dsimp <;> fun_prop
  source' := by apply Subtype.ext; ext z; exact H.apply_zero _
  target' := by apply Subtype.ext; ext z; exact H.apply_one _

/-- The loop obtained by pointwise concatenation of two loop-space loops. -/
def pointwiseLoopProduct {p q : Path x x} (α : Path p p) (β : Path q q) :
    Path (p.trans q) (p.trans q) :=
  (α.prod β).map (IdentityTrack.loopProduct
    (ContinuousMap.fst : C(Path x x × Path x x, Path x x)) ContinuousMap.snd).continuous

/-- The actual commutation of a loop family caps the paired original axis loop.
The displayed endpoint equality only casts its original vertex; the vertex track
of the commutation need not be stationary and no object-loop nullity is assumed. -/
def inverseAxisCap {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z)
    (H : (⟨fun w => (f z).trans (f w), by fun_prop⟩ : C(Z, Path x x)).Homotopy
      ⟨fun w => (f w).trans (f z), by fun_prop⟩)
    (p : Path x x) (hp : f z = p) (δ : Path z z) :
    (pointwiseLoopProduct ((δ.map f.continuous).cast hp.symm hp.symm)
      ((δ.map f.continuous).cast hp.symm hp.symm).symm).Homotopy
        (Path.refl (p.trans p)) := by
  subst p
  exact loopFamilyInverseAxisCap f z H δ

/-- The cap retains the original choice of relative homotopy. Its construction
and the pinned cap both choose from this exact proposition using `Nonempty.some`.
Proof irrelevance identifies those choices; this does not identify arbitrary
homotopies merely because they share endpoints. -/
theorem inverseAxisCap_eq_some {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z)
    (H : (⟨fun w => (f z).trans (f w), by fun_prop⟩ : C(Z, Path x x)).Homotopy
      ⟨fun w => (f w).trans (f z), by fun_prop⟩)
    (p : Path x x) (hp : f z = p) (δ : Path z z)
    (hcap : (pointwiseLoopProduct ((δ.map f.continuous).cast hp.symm hp.symm)
      ((δ.map f.continuous).cast hp.symm hp.symm).symm).Homotopic
        (Path.refl (p.trans p))) :
    inverseAxisCap f z H p hp δ = hcap.some := by
  subst p
  rfl

/-- The actual paired-axis cap becomes a path of periodic families on either axis. -/
def inverseAxisPeriodicPath {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z)
    (H : (⟨fun w => (f z).trans (f w), by fun_prop⟩ : C(Z, Path x x)).Homotopy
      ⟨fun w => (f w).trans (f z), by fun_prop⟩)
    (first : Bool) (p : Path x x) (hp : f z = p) (δ : Path z z) :
    Path (periodicConcat
      (axisFamily first ((δ.map f.continuous).cast hp.symm hp.symm))
      (axisFamily first ((δ.map f.continuous).cast hp.symm hp.symm).symm))
      (periodicConstant (Path x x) (p.trans p)) := by
  exact (axisHomotopy first (inverseAxisCap f z H p hp δ)).cast (by
    apply Subtype.ext; ext z q; rfl) (by apply Subtype.ext; ext z q; rfl)

/-- The two actual axis classes cancel, retaining the double original object-loop factor. -/
theorem inverseAxis_periodic_class {Z : Type v} [TopologicalSpace Z]
    (f : C(Z, Path x x)) (z : Z)
    (H : (⟨fun w => (f z).trans (f w), by fun_prop⟩ : C(Z, Path x x)).Homotopy
      ⟨fun w => (f w).trans (f z), by fun_prop⟩)
    (first : Bool) (p : Path x x) (hp : f z = p) (δ : Path z z) :
    periodicClass (axisFamily first ((δ.map f.continuous).cast hp.symm hp.symm)) *
      periodicClass (axisFamily first ((δ.map f.continuous).cast hp.symm hp.symm).symm) =
      periodicClass (periodicConstant (Path x x) p) *
        periodicClass (periodicConstant (Path x x) p) := by
  have h := periodicClass_of_path (inverseAxisPeriodicPath f z H first p hp δ)
  have hc : periodicConstant (Path x x) (p.trans p) =
      periodicConcat (periodicConstant (Path x x) p) (periodicConstant (Path x x) p) := rfl
  rw [hc] at h
  simpa only [periodicClass_concat] using h

end Topology.PeriodicFamilies

end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u v

namespace Topology.PeriodicFamilies

variable {Y : Type u} [TopologicalSpace Y]

/-- The first-coordinate loop of a periodic square at a fixed second coordinate. -/
def periodicSlice (P : PeriodicSquare Y) (s : unitInterval) :
    Path (P.val (0, s)) (P.val (0, s)) where
  toFun t := P.val (t, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := (P.property.1 s).symm

/-- The initial cap segment ending at the chosen cap parameter. -/
def capPrefix (P : PeriodicSquare Y) (C : C(unitInterval × unitInterval, Y))
    (h₀ : ∀ s, C (0, s) = P.val (0, s)) (u s : unitInterval) :
    Path (P.val (0, s)) (C (u, s)) where
  toFun t := C (u * t, s)
  continuous_toFun := by fun_prop
  source' := by rw [mul_zero]; exact h₀ s
  target' := by rw [mul_one]

/-- Slide the original loop's vertex along the supplied cap, retaining the
complete cap and both original torus coordinates. -/
def capConjugatedRaw (P : PeriodicSquare Y) (C : C(unitInterval × unitInterval, Y))
    (h₀ : ∀ s, C (0, s) = P.val (0, s)) : C((unitInterval × unitInterval) × unitInterval, Y) where
  toFun z := (((capPrefix P C h₀ z.1.1 z.1.2).symm.trans (periodicSlice P z.1.2)).trans
    (capPrefix P C h₀ z.1.1 z.1.2)) z.2
  continuous_toFun := by
    have hp : Continuous (fun z : (unitInterval × unitInterval) × unitInterval =>
        capPrefix P C h₀ z.1.1 z.1.2 z.2) := by
      change Continuous (fun z : (unitInterval × unitInterval) × unitInterval =>
        C (z.1.1 * z.2, z.1.2))
      fun_prop
    have hs : Continuous (fun z : (unitInterval × unitInterval) × unitInterval =>
        periodicSlice P z.1.2 z.2) := by
      change Continuous (fun z : (unitInterval × unitInterval) × unitInterval => P.val (z.2, z.1.2))
      fun_prop
    have hfirst : Continuous (fun z : (unitInterval × unitInterval) × unitInterval =>
        ((capPrefix P C h₀ z.1.1 z.1.2).symm.trans (periodicSlice P z.1.2)) z.2) :=
      Path.trans_continuous_family
      (fun z : unitInterval × unitInterval => (capPrefix P C h₀ z.1 z.2).symm)
      (Path.symm_continuous_family _ hp)
      (fun z : unitInterval × unitInterval => periodicSlice P z.2) hs
    have hall : Continuous (fun z : (unitInterval × unitInterval) × unitInterval =>
        (((capPrefix P C h₀ z.1.1 z.1.2).symm.trans (periodicSlice P z.1.2)).trans
          (capPrefix P C h₀ z.1.1 z.1.2)) z.2) := Path.trans_continuous_family
      (fun z : unitInterval × unitInterval =>
        (capPrefix P C h₀ z.1 z.2).symm.trans (periodicSlice P z.2)) hfirst
      (fun z : unitInterval × unitInterval => capPrefix P C h₀ z.1 z.2) hp
    exact hall

/-- The continuous family formed by conjugating slices with cap prefixes. -/
def capConjugatedMap (P : PeriodicSquare Y) (C : C(unitInterval × unitInterval, Y))
    (h₀ : ∀ s, C (0, s) = P.val (0, s)) :
    C(unitInterval × (unitInterval × unitInterval), Y) :=
  (capConjugatedRaw P C h₀).comp
    ⟨fun z => ((z.1, z.2.2), z.2.1), by fun_prop⟩

/-- The periodic square obtained by cap-prefix conjugation at a fixed parameter. -/
def capConjugatedSquare (P : PeriodicSquare Y) (C : C(unitInterval × unitInterval, Y))
    (h₀ : ∀ s, C (0, s) = P.val (0, s)) (hper : ∀ u, C (u, 0) = C (u, 1))
    (u : unitInterval) : PeriodicSquare Y :=
  ⟨⟨fun z => capConjugatedMap P C h₀ (u, z), by fun_prop⟩, by
    constructor
    · intro s
      exact (((capPrefix P C h₀ u s).symm.trans (periodicSlice P s)).trans
        (capPrefix P C h₀ u s)).source.trans
          ((((capPrefix P C h₀ u s).symm.trans (periodicSlice P s)).trans
            (capPrefix P C h₀ u s)).target.symm)
    · intro t
      change (((capPrefix P C h₀ u 0).symm.trans (periodicSlice P 0)).trans
        (capPrefix P C h₀ u 0)) t =
        (((capPrefix P C h₀ u 1).symm.trans (periodicSlice P 1)).trans
          (capPrefix P C h₀ u 1)) t
      simp only [Path.trans_apply, Path.symm_apply]
      split_ifs
      · exact hper _
      · exact P.property.2 _
      · exact hper _⟩

/-- The path through periodic squares defined by cap-prefix conjugation. -/
def capConjugatedPath (P : PeriodicSquare Y) (C : C(unitInterval × unitInterval, Y))
    (h₀ : ∀ s, C (0, s) = P.val (0, s)) (hper : ∀ u, C (u, 0) = C (u, 1)) :
    Path (capConjugatedSquare P C h₀ hper 0) (capConjugatedSquare P C h₀ hper 1) where
  toFun u := capConjugatedSquare P C h₀ hper u
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (capConjugatedMap P C h₀).continuous
  source' := rfl
  target' := rfl

/-- Insert only the two actual constant path segments, by the original unit delays. -/
def periodicUnitPad (P : PeriodicSquare Y) (u : unitInterval) : PeriodicSquare Y :=
  ⟨⟨fun z => (Path.delayReflRight (unitInterval.symm u)
      (Path.delayReflLeft (unitInterval.symm u) (periodicSlice P z.2))) z.1, by
    change Continuous (fun z : unitInterval × unitInterval => P.val
      (unitInterval.symm (unitInterval.qRight
        (unitInterval.symm (unitInterval.qRight (z.1, unitInterval.symm u)),
          unitInterval.symm u)), z.2))
    fun_prop⟩, by
    constructor
    · intro s
      exact (Path.delayReflRight (unitInterval.symm u)
        (Path.delayReflLeft (unitInterval.symm u) (periodicSlice P s))).source.trans
          (Path.delayReflRight (unitInterval.symm u)
            (Path.delayReflLeft (unitInterval.symm u) (periodicSlice P s))).target.symm
    · intro t
      exact P.property.2 _⟩

/-- The path from a periodic square to its unit-padded square. -/
def periodicUnitPadPath (P : PeriodicSquare Y) : Path P (periodicUnitPad P 1) where
  toFun u := periodicUnitPad P u
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × (unitInterval × unitInterval) => P.val
      (unitInterval.symm (unitInterval.qRight
        (unitInterval.symm (unitInterval.qRight (z.2.1, unitInterval.symm z.1)),
          unitInterval.symm z.1)), z.2.2))
    fun_prop
  source' := by
    apply Subtype.ext
    ext z
    change Path.delayReflRight (unitInterval.symm 0)
      (Path.delayReflLeft (unitInterval.symm 0) (periodicSlice P z.2)) z.1 = _
    rw [unitInterval.symm_zero, Path.delayReflRight_one, Path.delayReflLeft_one]
    rfl
  target' := rfl

/-- The initial conjugation has exactly the two unit pauses just inserted. -/
theorem capConjugated_zero (P : PeriodicSquare Y) (C : C(unitInterval × unitInterval, Y))
    (h₀ : ∀ s, C (0, s) = P.val (0, s)) (hper : ∀ u, C (u, 0) = C (u, 1)) :
    capConjugatedSquare P C h₀ hper 0 = periodicUnitPad P 1 := by
  apply Subtype.ext
  ext z
  change (((capPrefix P C h₀ 0 z.2).symm.trans (periodicSlice P z.2)).trans
    (capPrefix P C h₀ 0 z.2)) z.1 =
      (Path.delayReflRight (unitInterval.symm 1)
        (Path.delayReflLeft (unitInterval.symm 1) (periodicSlice P z.2))) z.1
  rw [unitInterval.symm_one, Path.delayReflRight_zero, Path.delayReflLeft_zero]
  have hp (t : unitInterval) : capPrefix P C h₀ 0 z.2 t = P.val (0, z.2) := by
    change C (0 * t, z.2) = _
    rw [zero_mul]
    exact h₀ z.2
  simp only [Path.trans_apply, Path.symm_apply, Path.refl_apply]
  split_ifs <;> first | exact hp _ | rfl

/-- Actual one-axis cap insertion over the entire other circle. Opposite edges
remain equal at every stage; the supplied cap is the moving vertex track. -/
def insertPeriodicCaps (P : PeriodicSquare Y) (C : C(unitInterval × unitInterval, Y))
    (h₀ : ∀ s, C (0, s) = P.val (0, s)) (hper : ∀ u, C (u, 0) = C (u, 1)) :
    Path P (capConjugatedSquare P C h₀ hper 1) :=
  (periodicUnitPadPath P).trans
    ((capConjugatedPath P C h₀ hper).cast (capConjugated_zero P C h₀ hper).symm rfl)

end Topology.PeriodicFamilies

end

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u v

namespace Topology.PeriodicFamilies

variable {X : Type u} [TopologicalSpace X] {x : X}
variable (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
  (hH : ∀ t, H (t, x) = x)

/-- The loop-space map sending a loop to its inverse followed by itself. -/
def prefixBaseMap : C(Path x x, Path x x) :=
  ⟨fun q => q.symm.trans q, Path.continuous_symm.path_trans continuous_id⟩

/-- The exact inverse-prefix word of the original scalar track. -/
def prefixTrackHomotopy : (prefixBaseMap (x := x)).Homotopy prefixBaseMap where
  toFun z := z.2.symm.trans (IdentityTrack.loopedHomotopy H hH z)
  continuous_toFun := (Path.continuous_symm.comp continuous_snd).path_trans
    (IdentityTrack.loopedHomotopy H hH).continuous
  map_zero_left q := by rw [(IdentityTrack.loopedHomotopy H hH).apply_zero]; rfl
  map_one_left q := by rw [(IdentityTrack.loopedHomotopy H hH).apply_one]; rfl

/-- The original cancellation is continuous as the entire inner loop varies. -/
def prefixContraction : prefixBaseMap.Homotopy (ContinuousMap.const (Path x x) (Path.refl x)) where
  toFun z := loopInversePrefixCancellation z.2 z.1
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval × Path x x) × unitInterval =>
      z.1.2.symm ⟨Path.Homotopy.reflTransSymmAux (unitInterval.symm z.1.1, z.2),
        Path.Homotopy.reflTransSymmAux_mem_I _⟩)
    exact (Path.continuous_symm.comp (continuous_snd.comp continuous_fst)).eval (by fun_prop)
  map_zero_left q := (loopInversePrefixCancellation q).source
  map_one_left q := (loopInversePrefixCancellation q).target

/-- The self-track loop map with the cap concatenated on the left. -/
def leftCappedTrackMap : C(Path x x, Path (Path.refl x) (Path.refl x)) :=
  ConePair.closedLoopMap (((prefixContraction (x := x)).symm.trans
    (prefixTrackHomotopy H hH)).trans prefixContraction)

/-- The self-track loop map with the cap concatenated on the right. -/
def rightCappedTrackMap : C(Path x x, Path (Path.refl x) (Path.refl x)) :=
  ConePair.closedLoopMap ((prefixContraction (x := x)).symm.trans
    ((prefixTrackHomotopy H hH).trans prefixContraction))

/-- Only the original path associator changes the cap parentheses. It is joint
in the whole varying inner loop. -/
def cappedTrackAssociator :
    (leftCappedTrackMap H hH).Homotopy (rightCappedTrackMap H hH) :=
  ConePair.closedRelativeHomotopy _ _
    (homotopyAssociator prefixContraction.symm (prefixTrackHomotopy H hH) prefixContraction)

theorem rightCappedTrackMap_eq (q : Path x x) :
    rightCappedTrackMap H hH q =
      loopNormalizedSelfTrack q ((IdentityTrack.loopedHomotopy H hH).evalAt q) := by
  apply Path.ext
  funext t
  change (loopInversePrefixCancellation q).symm.trans
    (((prefixTrackHomotopy H hH).evalAt q).trans (loopInversePrefixCancellation q)) t = _
  have he : (prefixTrackHomotopy H hH).evalAt q =
      ((((IdentityTrack.loopedHomotopy H hH).evalAt q).map
        (loopLeftTranslationEquiv q.symm).continuous).cast
          (loopLeftTranslationEquiv_apply _ _).symm
          (loopLeftTranslationEquiv_apply _ _).symm) := by
    apply Path.ext
    funext r
    exact (loopLeftTranslationEquiv_apply _ _).symm
  rw [he]
  rfl

/-- The periodic square obtained by evaluating a loop through a loop-space map. -/
def trackPeriodic (q : Path (Path.refl x) (Path.refl x))
    (f : C(Path x x, Path (Path.refl x) (Path.refl x))) : PeriodicSquare (Path x x) :=
  ⟨⟨fun z => f (q z.2) z.1, by fun_prop⟩,
    (fun s => (f (q s)).source.trans (f (q s)).target.symm), by
      intro t
      change (f (q 0)) t = (f (q 1)) t
      rw [q.source, q.target]⟩

/-- The path of track squares induced by a homotopy of loop-space maps. -/
def trackPeriodicHomotopy (q : Path (Path.refl x) (Path.refl x))
    {f g : C(Path x x, Path (Path.refl x) (Path.refl x))} (K : f.Homotopy g) :
    Path (trackPeriodic q f) (trackPeriodic q g) where
  toFun r := ⟨⟨fun z => K (r, q z.2) z.1, by fun_prop⟩,
    (fun s => (K (r, q s)).source.trans (K (r, q s)).target.symm), by
      intro t
      change (K (r, q 0)) t = (K (r, q 1)) t
      rw [q.source, q.target]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × (unitInterval × unitInterval) =>
      K (z.1, q z.2.2) z.2.1)
    fun_prop
  source' := by apply Subtype.ext; ext z r; exact congrArg (fun p => p z.1 r) (K.apply_zero _)
  target' := by apply Subtype.ext; ext z r; exact congrArg (fun p => p z.1 r) (K.apply_one _)

/-- The original two-dimensional cube obtained by uncurrying the input loop. -/
def inputCube (q : Path (Path.refl x) (Path.refl x)) : GenLoop (Fin 2) X x :=
  loopUncurry ((genLoopEquivOfUnique (Fin 1)).symm q)

/-- The original normalized three-dimensional self-track cube. -/
def originalTrackCube (q : Path (Path.refl x) (Path.refl x)) : GenLoop (Fin 3) X x :=
  genLoopNormalizedSelfTrackCube 1 (inputCube q) (IdentityTrack.track H hH 1 (inputCube q))

/-- The original self-track cube after coordinate transposition and currying. -/
def originalTrackLoopCube (q : Path (Path.refl x) (Path.refl x)) :
    GenLoop (Fin 2) (Path x x) (Path.refl x) :=
  loopCurry (transposeGenLoop (0 : Fin 3) 1 (by decide) (originalTrackCube H hH q))

theorem normalizedTrack_evaluation (q : Path (Path.refl x) (Path.refl x))
    (t r s : unitInterval) :
    genLoopNormalizedSelfTrackPath 1 (inputCube q)
        (IdentityTrack.track H hH 1 (inputCube q)) t ![r, s] =
      loopNormalizedSelfTrack (q s) ((IdentityTrack.loopedHomotopy H hH).evalAt (q s)) t r := by
  let p := inputCube q
  let L := GenLoop.loopHomeo (X := X) (x := x) (0 : Fin 2)
  let α := IdentityTrack.track H hH 1 p
  change (loopNormalizedSelfTrack (L.toHomotopyEquiv.toFun p)
    (α.map L.toHomotopyEquiv.toFun.continuous) t r) ((Cube.splitAt 0 ![r, s]).2) = _
  exact loopNormalizedSelfTrack_pointwise
    (fun f : GenLoop {j : Fin 2 // j ≠ 0} X x => f ((Cube.splitAt 0 ![r, s]).2)) id
    _ (q s) _ ((IdentityTrack.loopedHomotopy H hH).evalAt (q s))
    (fun _ => rfl) (fun _ _ => rfl) t r

/-- The periodic square underlying a based two-dimensional generalized loop. -/
def periodicOfCube {Y : Type u} [TopologicalSpace Y] {y : Y}
    (p : GenLoop (Fin 2) Y y) : PeriodicSquare Y :=
  ⟨⟨fun z => p ![z.1, z.2], by
    apply p.val.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop⟩, by
    constructor
    · intro s
      exact (p.property _ ⟨0, Or.inl rfl⟩).trans (p.property _ ⟨0, Or.inr rfl⟩).symm
    · intro t
      exact (p.property _ ⟨1, Or.inl rfl⟩).trans (p.property _ ⟨1, Or.inr rfl⟩).symm⟩

/-- The capped periodic endpoint is the actual original three-cube, with its
first two coordinates exchanged before the existing loop curry. -/
theorem trackPeriodic_originalCube (q : Path (Path.refl x) (Path.refl x)) :
    trackPeriodic q (rightCappedTrackMap H hH) = periodicOfCube (originalTrackLoopCube H hH q) := by
  apply Subtype.ext
  ext z r
  rw [show (trackPeriodic q (rightCappedTrackMap H hH)).val z =
      rightCappedTrackMap H hH (q z.2) z.1 from rfl, rightCappedTrackMap_eq]
  have hc : cubeCoordinateSwap (0 : Fin 3) 1 (Fin.cons r ![z.1, z.2]) = ![z.1, r, z.2] := by
    funext i
    fin_cases i <;> simp [cubeCoordinateSwap]
  change loopNormalizedSelfTrack (q z.2)
    ((IdentityTrack.loopedHomotopy H hH).evalAt (q z.2)) z.1 r =
      originalTrackCube H hH q (cubeCoordinateSwap 0 1 (Fin.cons r ![z.1, z.2]))
  rw [hc]
  exact (normalizedTrack_evaluation H hH q z.1 r z.2).symm

/-- The sign is proved on the actual original cube and its existing loop shift. -/
theorem originalTrackLoopCube_class (q : Path (Path.refl x) (Path.refl x)) :
    (loopShiftMulEquiv (x := x) 1).symm
        (Quotient.mk' (originalTrackLoopCube H hH q)) =
      (IdentityTrack.operation H hH 1 (Quotient.mk' (inputCube q)) : HomotopyGroup.Pi 3 X x)⁻¹ := by
  change (Quotient.mk' (transposeGenLoop (0 : Fin 3) 1 (by decide)
    (originalTrackCube H hH q)) : HomotopyGroup.Pi 3 X x) = _
  rw [transposeGenLoop_class]
  exact congrArg (fun a : HomotopyGroup.Pi 3 X x => a⁻¹)
    (genLoopNormalizedSelfTrackCube_class 1 (inputCube q)
      (IdentityTrack.track H hH 1 (inputCube q)))

end Topology.PeriodicFamilies

end

end
