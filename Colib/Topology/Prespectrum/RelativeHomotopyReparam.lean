/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Colib.Topology.Prespectrum.RelativeHomotopyComposition
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-! Uniform path reparametrizations for actual whole prespectrum comparisons.
They are used to reassociate and cancel the original coefficient-square tracks in Bass pasting. -/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/RelativeHomotopyReparam.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original continuous families, independent
parameters, fixed boundaries and strict structure compatibility are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} {f g h k : E ⟶ F}

/-- Evaluation at an original point gives the actual endpoint-based path. -/
def Homotopy.path (H : Homotopy f g) (n : ℕ) (x : E.space n) :
    Path (f.map n x) (g.map n x) where
  toFun s := H.level n (s, x)
  continuous_toFun := by fun_prop
  source' := H.at_zero n x
  target' := H.at_one n x

/-- Pointwise evaluation retains the original concatenation parametrization. -/
theorem Homotopy.path_trans (H : Homotopy f g) (K : Homotopy g h) (n : ℕ) (x : E.space n) :
    (H.trans K).path n x = (H.path n x).trans (K.path n x) := by
  apply Path.ext
  funext s
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply, Path.trans_apply]
  split <;> rfl

/-- Pointwise evaluation retains the original reversed track. -/
theorem Homotopy.path_symm (H : Homotopy f g) (n : ℕ) (x : E.space n) :
    H.symm.path n x = (H.path n x).symm := rfl

/-- Evaluation of a constant whole homotopy is the literal constant path. -/
theorem Homotopy.path_refl (f : E ⟶ F) (n : ℕ) (x : E.space n) :
    (Homotopy.refl f).path n x = Path.refl (f.map n x) := rfl

/-- Reversing the same original time coordinate twice is literal equality. -/
theorem Homotopy.symm_symm (H : Homotopy f g) : H.symm.symm = H := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  exact congrArg (fun t ↦ H.level n (t, x)) (unitInterval.symm_symm s)

/-- A constant track is unchanged by reversal. -/
theorem Homotopy.symm_refl (f : E ⟶ F) : (Homotopy.refl f).symm = Homotopy.refl f := by
  apply Homotopy.ext
  rfl

/-- Reversal retains the actual opposite concatenation order and parametrization. -/
theorem Homotopy.symm_trans (H : Homotopy f g) (K : Homotopy g h) :
    (H.trans K).symm = K.symm.trans H.symm := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  have hp := Path.trans_symm (H.path n x) (K.path n x)
  simp only [← Homotopy.path_trans, ← Homotopy.path_symm] at hp
  exact DFunLike.congr_fun hp s

/-- Change only original path time by a continuous endpoint-preserving function. -/
def Homotopy.reparam (H : Homotopy f g) (φ : C(unitInterval, unitInterval))
    (h0 : φ 0 = 0) (h1 : φ 1 = 1) : Homotopy f g where
  level n := ⟨fun z ↦ H.level n (φ z.1, z.2), by fun_prop⟩
  at_zero n x := by
    change H.level n (φ 0, x) = _
    rw [h0]
    exact H.at_zero n x
  at_one n x := by
    change H.level n (φ 1, x) = _
    rw [h1]
    exact H.at_one n x
  at_point n s := H.at_point n (φ s)
  comm n s x t := H.comm n (φ s) x t

/-- Linear interpolation of the time function gives a genuine relative comparison. -/
def Homotopy.RelHomotopy.reparam (H : Homotopy f g) (φ : C(unitInterval, unitInterval))
    (h0 : φ 0 = 0) (h1 : φ 1 = 1) : H.RelHomotopy (H.reparam φ h0 h1) where
  level n := {
    toFun z := Path.Homotopy.reparam (H.path n z.2.2) φ φ.continuous h0 h1 (z.1, z.2.1)
    continuous_toFun := by
      change Continuous (fun z : unitInterval × (unitInterval × E.space n) ↦
        H.level n (⟨(unitInterval.symm z.1 : ℝ) * z.2.1 + (z.1 : ℝ) * φ z.2.1, _⟩, z.2.2))
      fun_prop
    map_zero_left z := (Path.Homotopy.reparam (H.path n z.2) φ φ.continuous h0 h1).apply_zero z.1
    map_one_left z := (Path.Homotopy.reparam (H.path n z.2) φ φ.continuous h0 h1).apply_one z.1
    prop' r z hz := by
      rcases z with ⟨s, x⟩
      change Path.Homotopy.reparam (H.path n x) φ φ.continuous h0 h1 (r, s) = H.level n (s, x)
      rcases hz with hz | hz | hz
      · change s = 0 at hz
        subst s
        exact ((Path.Homotopy.reparam (H.path n x) φ φ.continuous h0 h1).source r).trans
          (H.at_zero n x).symm
      · change s = 1 at hz
        subst s
        exact ((Path.Homotopy.reparam (H.path n x) φ φ.continuous h0 h1).target r).trans
          (H.at_one n x).symm
      · change x = E.point n at hz
        subst x
        exact (H.at_point n _).trans (H.at_point n s).symm }
  comm n r s x t := H.comm n _ x t

/-- Reassociate the original three tracks with their actual dyadic time partitions. -/
def Homotopy.RelHomotopy.transAssoc (H : Homotopy f g) (K : Homotopy g h)
    (L : Homotopy h k) : ((H.trans K).trans L).RelHomotopy (H.trans (K.trans L)) := by
  let φ : C(unitInterval, unitInterval) :=
    ⟨fun s ↦ ⟨Path.Homotopy.transAssocReparamAux s, Path.Homotopy.transAssocReparamAux_mem_I s⟩,
      by fun_prop⟩
  have h0 : φ 0 = 0 := Subtype.ext Path.Homotopy.transAssocReparamAux_zero
  have h1 : φ 1 = 1 := Subtype.ext Path.Homotopy.transAssocReparamAux_one
  have he : (H.trans K).trans L = (H.trans (K.trans L)).reparam φ h0 h1 := by
    apply Homotopy.ext
    funext n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    have hp := Path.Homotopy.trans_assoc_reparam (H.path n x) (K.path n x) (L.path n x)
    simp only [← Homotopy.path_trans] at hp
    change ((H.trans K).trans L).path n x s = (H.trans (K.trans L)).path n x (φ s)
    exact DFunLike.congr_fun hp s
  have J := (Homotopy.RelHomotopy.reparam (H.trans (K.trans L)) φ h0 h1).symm
  rw [← he] at J
  exact J

/-- Remove the terminal constant half of an actual whole track. -/
def Homotopy.RelHomotopy.transRefl (H : Homotopy f g) :
    (H.trans (Homotopy.refl g)).RelHomotopy H := by
  let φ : C(unitInterval, unitInterval) :=
    ⟨fun s ↦ ⟨Path.Homotopy.transReflReparamAux s, Path.Homotopy.transReflReparamAux_mem_I s⟩,
      by fun_prop⟩
  have h0 : φ 0 = 0 := Subtype.ext Path.Homotopy.transReflReparamAux_zero
  have h1 : φ 1 = 1 := Subtype.ext Path.Homotopy.transReflReparamAux_one
  have he : H.trans (Homotopy.refl g) = H.reparam φ h0 h1 := by
    apply Homotopy.ext
    funext n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    have hp := Path.Homotopy.trans_refl_reparam (H.path n x)
    rw [← Homotopy.path_refl g n x, ← Homotopy.path_trans] at hp
    change (H.trans (Homotopy.refl g)).path n x s = H.path n x (φ s)
    exact DFunLike.congr_fun hp s
  have J := (Homotopy.RelHomotopy.reparam H φ h0 h1).symm
  rw [← he] at J
  exact J

/-- Remove the initial constant half, retaining the entire original track. -/
def Homotopy.RelHomotopy.reflTrans (H : Homotopy f g) :
    ((Homotopy.refl f).trans H).RelHomotopy H := by
  simpa only [Homotopy.symm_trans, Homotopy.symm_refl, Homotopy.symm_symm] using
    (Homotopy.RelHomotopy.transRefl H.symm).symmPath

/-- The original track followed by its reversal is contracted by an actual joint family. -/
def Homotopy.RelHomotopy.reflTransSymm (H : Homotopy f g) :
    (Homotopy.refl f).RelHomotopy (H.trans H.symm) where
  level n := {
    toFun z := Path.Homotopy.reflTransSymm (H.path n z.2.2) (z.1, z.2.1)
    continuous_toFun := by
      change Continuous (fun z : unitInterval × (unitInterval × E.space n) ↦
        H.level n (⟨Path.Homotopy.reflTransSymmAux (z.1, z.2.1), _⟩, z.2.2))
      fun_prop
    map_zero_left z := (Path.Homotopy.reflTransSymm (H.path n z.2)).apply_zero z.1
    map_one_left z := by
      rcases z with ⟨s, x⟩
      change Path.Homotopy.reflTransSymm (H.path n x) (1, s) =
        ((H.trans H.symm).path n x).toContinuousMap s
      have hp := (Path.Homotopy.reflTransSymm (H.path n x)).apply_one s
      simpa only [← Homotopy.path_symm, ← Homotopy.path_trans] using hp
    prop' r z hz := by
      rcases z with ⟨s, x⟩
      change Path.Homotopy.reflTransSymm (H.path n x) (r, s) = f.map n x
      rcases hz with hz | hz | hz
      · change s = 0 at hz
        subst s
        exact (Path.Homotopy.reflTransSymm (H.path n x)).source r
      · change s = 1 at hz
        subst s
        exact (Path.Homotopy.reflTransSymm (H.path n x)).target r
      · change x = E.point n at hz
        subst x
        exact (H.at_point n _).trans (f.map_point n).symm }
  comm n r s x t := H.comm n _ x t

/-- Reversed followed by forward original tracks contract with the same independent coordinates. -/
def Homotopy.RelHomotopy.reflSymmTrans (H : Homotopy f g) :
    (Homotopy.refl g).RelHomotopy (H.symm.trans H) := by
  simpa only [Homotopy.symm_symm] using Homotopy.RelHomotopy.reflTransSymm H.symm

end Topology.LoopPrespectrum
