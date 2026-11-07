/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Path.CarrierSquareDescent
public import Colib.Topology.HELP.CubeBoundaryHomeomorph
public import Colib.Topology.HomotopyFiber.CappedTriangle
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Actual periodic squares and target cappings from commuting based loops

Commutativity in the original fundamental group supplies an actual based path
homotopy. The native compact square descent turns it into a square with the
prescribed four whole edges. Simply connected target axes have actual based
nullhomotopies. Their compatible four boundary traces extend by the genuine
finite cube-boundary homotopy extension property.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/CommutingSquareCapping.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, coordinates,
whole boundary traces and universe parameters are retained with native owners.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open HomotopyGroup TopCat
open scoped Topology unitInterval
universe u
namespace Topology.HomotopyFiber.CommutingSquareCapping

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {p : X} (A B : Path p p)
  (hc : @Commute (FundamentalGroup X p) inferInstance
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk A)) (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk B)))

/-- Commuting original loop classes give the actual based conjugacy homotopy. -/
def commutingBoundaryHomotopy : B.Homotopy ((A.trans B).trans A.symm) := by
  let a : FundamentalGroup X p := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk A)
  let b : FundamentalGroup X p := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk B)
  have hab : a * b = b * a := hc.eq
  have he : (Path.Homotopic.Quotient.mk B : Path.Homotopic.Quotient p p) =
      Path.Homotopic.Quotient.mk ((A.trans B).trans A.symm) := by
    exact congrArg CategoryTheory.End.asHom (show b = a⁻¹ * (b * a) by
      rw [← hab]
      exact (inv_mul_cancel_left a b).symm)
  exact (Quotient.exact he).some

/-- The actual descended source square, with first ordered axis A and second axis B. -/
def sourceSquare : C(unitInterval × unitInterval, X) :=
  (CarrierPathSquare.boundarySquare (commutingBoundaryHomotopy A B hc)).parameter

@[simp] theorem sourceSquare_zero_first (s : unitInterval) :
    sourceSquare A B hc (0, s) = B s :=
  (CarrierPathSquare.boundarySquare (commutingBoundaryHomotopy A B hc)).at_zero s

@[simp] theorem sourceSquare_one_first (s : unitInterval) :
    sourceSquare A B hc (1, s) = B s :=
  (CarrierPathSquare.boundarySquare (commutingBoundaryHomotopy A B hc)).at_one s

@[simp] theorem sourceSquare_zero_second (t : unitInterval) :
    sourceSquare A B hc (t, 0) = A t :=
  (CarrierPathSquare.boundarySquare (commutingBoundaryHomotopy A B hc)).left t

@[simp] theorem sourceSquare_one_second (t : unitInterval) :
    sourceSquare A B hc (t, 1) = A t :=
  (CarrierPathSquare.boundarySquare (commutingBoundaryHomotopy A B hc)).right t

theorem sourceSquare_vertex : sourceSquare A B hc (0, 0) = p := by simp

/-- The opposite source edges agree as whole paths. -/
theorem sourceSquare_periodic :
    (∀ s, sourceSquare A B hc (0, s) = sourceSquare A B hc (1, s)) ∧
      ∀ t, sourceSquare A B hc (t, 0) = sourceSquare A B hc (t, 1) := by
  constructor <;> intro t <;> simp

variable (f : C(X, Y)) [SimplyConnectedSpace Y]

/-- Simple connectedness gives an actual endpoint-fixed nullhomotopy of each original image axis. -/
def axisNullhomotopy (a : Path p p) :
    (basedLoopMap f rfl a).Homotopy (Path.refl (f p)) :=
  (SimplyConnectedSpace.paths_homotopic (basedLoopMap f rfl a) (Path.refl (f p))).some

/-- The selected nullhomotopy fixes either endpoint at every time. -/
theorem axisNullhomotopy_endpoint (a : Path p p) (r t : unitInterval) (ht : t = 0 ∨ t = 1) :
    axisNullhomotopy f a (r, t) = f p := by
  rcases ht with rfl | rfl
  · exact (axisNullhomotopy f a).source r
  · exact (axisNullhomotopy f a).target r

/-- The original nullhomotopy as a genuine path in the original based loop space. -/
def axisNullPath (a : Path p p) : Path (basedLoopMap f rfl a) (Path.refl (f p)) where
  toFun r := (axisNullhomotopy f a).eval r
  continuous_toFun := Path.continuous_uncurry_iff.mp (axisNullhomotopy f a).continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

/-- The genuine fiber loop retains the original source axis and the selected nullhomotopy time. -/
def axisFiberLoop (a : Path p p) : Path (basepoint f (f p) p rfl) (basepoint f (f p) p rfl) :=
  cappedLoop f rfl a (axisNullPath f a)

@[simp] theorem axisFiberLoop_source (a : Path p p) (t : unitInterval) :
    (axisFiberLoop f a t).val.1 = a t := rfl

@[simp] theorem axisFiberLoop_path (a : Path p p) (t r : unitInterval) :
    (axisFiberLoop f a t).val.2 r = axisNullhomotopy f a (r, t) := rfl

/-- Projection recovers the entire original based source path. -/
theorem axisFiberLoop_projection (a : Path p p) :
    (axisFiberLoop f a).map (projection f (f p)).continuous = a := by ext t; rfl

/-- Coordinates of the actual universe-lifted two-cube, in the original order. -/
def cubeToSquare : C(CubicalTests.cube.{u} 2, unitInterval × unitInterval) :=
  ⟨fun z => (z.down 0, z.down 1), by fun_prop⟩

/-- The literal ordered square coordinates, without an orientation change. -/
def squareToCube : C(unitInterval × unitInterval, CubicalTests.cube.{u} 2) where
  toFun z := ⟨![z.1, z.2]⟩
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

@[simp] theorem cubeToSquare_squareToCube (z : unitInterval × unitInterval) :
    cubeToSquare (squareToCube z) = z := rfl

/-- The actual two-cube boundary is the union of its two pairs of opposite faces. -/
theorem boundary_two_cases (z : CubicalTests.boundary.{u} 2) :
    (z.val.down 0 = 0 ∨ z.val.down 0 = 1) ∨
      (z.val.down 1 = 0 ∨ z.val.down 1 = 1) := by
  obtain ⟨i, hi⟩ := z.property
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi

/-- The prescribed boundary trace uses the same nullhomotopy on both corresponding edges. -/
def boundaryCapFun (z : unitInterval × CubicalTests.boundary.{u} 2) : Y := by
  classical
  exact if z.2.val.down 0 = 0 ∨ z.2.val.down 0 = 1 then
    axisNullhomotopy f B (z.1, z.2.val.down 1)
  else axisNullhomotopy f A (z.1, z.2.val.down 0)

/-- On the first pair of opposite edges, the trace is exactly the second-axis nullhomotopy. -/
theorem boundaryCapFun_first (r : unitInterval) (z : CubicalTests.boundary.{u} 2)
    (h : z.val.down 0 = 0 ∨ z.val.down 0 = 1) :
    boundaryCapFun A B f (r, z) = axisNullhomotopy f B (r, z.val.down 1) := by
  simp [boundaryCapFun, h]

/-- On the other pair, corner compatibility follows from endpoint-fixed nullhomotopies. -/
theorem boundaryCapFun_second (r : unitInterval) (z : CubicalTests.boundary.{u} 2)
    (h : z.val.down 1 = 0 ∨ z.val.down 1 = 1) :
    boundaryCapFun A B f (r, z) = axisNullhomotopy f A (r, z.val.down 0) := by
  classical
  by_cases hv : z.val.down 0 = 0 ∨ z.val.down 0 = 1
  · rw [boundaryCapFun_first A B f r z hv]
    exact (axisNullhomotopy_endpoint f B r _ h).trans
      (axisNullhomotopy_endpoint f A r _ hv).symm
  · simp [boundaryCapFun, hv]

/-- The four actual traces glue continuously on the literal boundary, including all corners. -/
theorem continuous_boundaryCapFun : Continuous (boundaryCapFun A B f) := by
  classical
  let V : Set (unitInterval × CubicalTests.boundary.{u} 2) :=
    {z | z.2.val.down 0 = 0 ∨ z.2.val.down 0 = 1}
  let W : Set (unitInterval × CubicalTests.boundary.{u} 2) :=
    {z | z.2.val.down 1 = 0 ∨ z.2.val.down 1 = 1}
  have hV : IsClosed V :=
    (isClosed_eq (by fun_prop) continuous_const).union
      (isClosed_eq (by fun_prop) continuous_const)
  have hW : IsClosed W :=
    (isClosed_eq (by fun_prop) continuous_const).union
      (isClosed_eq (by fun_prop) continuous_const)
  have hcover : V ∪ W = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact boundary_two_cases z.2
  rw [← continuousOn_univ, ← hcover]
  apply ContinuousOn.union_of_isClosed _ _ hV hW
  · rw [continuousOn_iff_continuous_domRestrict]
    have he : (fun z : V => boundaryCapFun A B f z.val) =
        fun z => axisNullhomotopy f B (z.val.1, z.val.2.val.down 1) := by
      funext z
      exact boundaryCapFun_first A B f _ _ z.property
    change Continuous (fun z : V => boundaryCapFun A B f z.val)
    rw [he]
    fun_prop
  · rw [continuousOn_iff_continuous_domRestrict]
    have he : (fun z : W => boundaryCapFun A B f z.val) =
        fun z => axisNullhomotopy f A (z.val.1, z.val.2.val.down 0) := by
      funext z
      exact boundaryCapFun_second A B f _ _ z.property
    change Continuous (fun z : W => boundaryCapFun A B f z.val)
    rw [he]
    fun_prop

/-- The bundled genuine boundary homotopy. -/
def boundaryCap : C(unitInterval × CubicalTests.boundary.{u} 2, Y) :=
  ⟨boundaryCapFun A B f, continuous_boundaryCapFun A B f⟩

/-- Initially the glued boundary is exactly the image of the constructed source square. -/
theorem boundaryCap_zero (z : CubicalTests.boundary.{u} 2) :
    boundaryCap A B f (0, z) = f (sourceSquare A B hc (cubeToSquare z.val)) := by
  rcases boundary_two_cases z with hv | hh
  · change boundaryCapFun A B f (0, z) = _
    rw [boundaryCapFun_first A B f 0 z hv]
    rcases hv with hz | hz
    · change axisNullhomotopy f B (0, z.val.down 1) =
        f (sourceSquare A B hc (z.val.down 0, z.val.down 1))
      rw [hz, sourceSquare_zero_first]
      exact (axisNullhomotopy f B).apply_zero _
    · change axisNullhomotopy f B (0, z.val.down 1) =
        f (sourceSquare A B hc (z.val.down 0, z.val.down 1))
      rw [hz, sourceSquare_one_first]
      exact (axisNullhomotopy f B).apply_zero _
  · change boundaryCapFun A B f (0, z) = _
    rw [boundaryCapFun_second A B f 0 z hh]
    rcases hh with hz | hz
    · change axisNullhomotopy f A (0, z.val.down 0) =
        f (sourceSquare A B hc (z.val.down 0, z.val.down 1))
      rw [hz, sourceSquare_zero_second]
      exact (axisNullhomotopy f A).apply_zero _
    · change axisNullhomotopy f A (0, z.val.down 0) =
        f (sourceSquare A B hc (z.val.down 0, z.val.down 1))
      rw [hz, sourceSquare_one_second]
      exact (axisNullhomotopy f A).apply_zero _

/-- The entire terminal boundary is literally the original target basepoint. -/
theorem boundaryCap_one (z : CubicalTests.boundary.{u} 2) : boundaryCap A B f (1, z) = f p := by
  classical
  change boundaryCapFun A B f (1, z) = f p
  unfold boundaryCapFun
  split_ifs
  · exact (axisNullhomotopy f B).apply_one _
  · exact (axisNullhomotopy f A).apply_one _

/-- Genuine cube-boundary HEP extends precisely these compatible traces and initial disk. -/
theorem exists_extension :
    ∃ K : C(unitInterval × CubicalTests.cube.{u} 2, Y),
      (∀ z, K (0, z) = f (sourceSquare A B hc (cubeToSquare z))) ∧
      ∀ r (z : CubicalTests.boundary.{u} 2), K (r, z.val) = boundaryCap A B f (r, z) := by
  exact homotopyExtensionProperty_continuous (CubicalTests.boundaryInclusion_hep 2)
    (TopCat.of Y) (f.comp ((sourceSquare A B hc).comp cubeToSquare)) (boundaryCap A B f)
    (boundaryCap_zero A B hc f)

/-- The chosen extension is an actual continuous map supplied by the proved HEP theorem. -/
def extension : C(unitInterval × CubicalTests.cube.{u} 2, Y) :=
  (exists_extension A B hc f).choose

@[simp] theorem extension_zero (z : CubicalTests.cube.{u} 2) :
    extension A B hc f (0, z) = f (sourceSquare A B hc (cubeToSquare z)) :=
  (exists_extension A B hc f).choose_spec.1 z

/-- Every original side trace, at every time and boundary point, is retained by the extension. -/
theorem extension_boundary (r : unitInterval) (z : CubicalTests.boundary.{u} 2) :
    extension A B hc f (r, z.val) = boundaryCap A B f (r, z) :=
  (exists_extension A B hc f).choose_spec.2 r z

/-- The terminal extension is the actual based target two-cube. -/
def targetCube : GenLoop (Fin 2) Y (f p) :=
  ⟨⟨fun z => extension A B hc f (1, ⟨z⟩), by fun_prop⟩, by
    intro z hz
    exact (extension_boundary A B hc f 1 ⟨⟨z⟩, hz⟩).trans
      (boundaryCap_one A B f ⟨⟨z⟩, hz⟩)⟩

/-- The based cube as the literal ordered square used by the periodic two-chain calibration. -/
def basedSquare {y : Y} (β : GenLoop (Fin 2) Y y) : C(unitInterval × unitInterval, Y) where
  toFun z := β ![z.1, z.2]
  continuous_toFun := by
    apply β.val.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

/-- The entire actual homotopy from the original image square to the terminal based square. -/
def wholeHomotopy : (f.comp (sourceSquare A B hc)).Homotopy
    (basedSquare (targetCube A B hc f)) where
  toFun z := extension A B hc f (z.1, squareToCube z.2)
  continuous_toFun := by fun_prop
  map_zero_left z := by rw [extension_zero, cubeToSquare_squareToCube]; rfl
  map_one_left _ := rfl

/-- The first opposite edge is exactly the selected second-axis nullhomotopy. -/
theorem wholeHomotopy_zero_first (r s : unitInterval) :
    wholeHomotopy A B hc f (r, (0, s)) = axisNullhomotopy f B (r, s) := by
  let z : CubicalTests.boundary.{u} 2 := ⟨⟨![0, s]⟩, ⟨0, Or.inl rfl⟩⟩
  exact (extension_boundary A B hc f r z).trans (boundaryCapFun_first A B f r z (Or.inl rfl))

/-- The other first-coordinate edge is the same whole second-axis nullhomotopy. -/
theorem wholeHomotopy_one_first (r s : unitInterval) :
    wholeHomotopy A B hc f (r, (1, s)) = axisNullhomotopy f B (r, s) := by
  let z : CubicalTests.boundary.{u} 2 := ⟨⟨![1, s]⟩, ⟨0, Or.inr rfl⟩⟩
  exact (extension_boundary A B hc f r z).trans (boundaryCapFun_first A B f r z (Or.inr rfl))

/-- The first second-coordinate edge retains the selected first-axis nullhomotopy. -/
theorem wholeHomotopy_zero_second (r t : unitInterval) :
    wholeHomotopy A B hc f (r, (t, 0)) = axisNullhomotopy f A (r, t) := by
  let z : CubicalTests.boundary.{u} 2 := ⟨⟨![t, 0]⟩, ⟨1, Or.inl rfl⟩⟩
  exact (extension_boundary A B hc f r z).trans (boundaryCapFun_second A B f r z (Or.inl rfl))

/-- The other second-coordinate edge retains the same whole first-axis nullhomotopy. -/
theorem wholeHomotopy_one_second (r t : unitInterval) :
    wholeHomotopy A B hc f (r, (t, 1)) = axisNullhomotopy f A (r, t) := by
  let z : CubicalTests.boundary.{u} 2 := ⟨⟨![t, 1]⟩, ⟨1, Or.inr rfl⟩⟩
  exact (extension_boundary A B hc f r z).trans (boundaryCapFun_second A B f r z (Or.inr rfl))

/-- Every intermediate square is genuinely periodic in both original coordinates. -/
theorem wholeHomotopy_periodic :
    (∀ r s, wholeHomotopy A B hc f (r, (0, s)) = wholeHomotopy A B hc f (r, (1, s))) ∧
      ∀ r t, wholeHomotopy A B hc f (r, (t, 0)) = wholeHomotopy A B hc f (r, (t, 1)) := by
  constructor
  · intro r s
    rw [wholeHomotopy_zero_first, wholeHomotopy_one_first]
  · intro r t
    rw [wholeHomotopy_zero_second, wholeHomotopy_one_second]

/-- The actual capping fixes the named target vertex at all times. -/
theorem wholeHomotopy_vertex (r : unitInterval) : wholeHomotopy A B hc f (r, (0, 0)) = f p := by
  rw [wholeHomotopy_zero_first]
  exact (axisNullhomotopy f B).source r

/-- The first actual fiber axis projects to the first whole source-square edge. -/
theorem firstFiberAxis_source (t : unitInterval) :
    (axisFiberLoop f A t).val.1 = sourceSquare A B hc (t, 0) :=
  (sourceSquare_zero_second A B hc t).symm

/-- Its complete stored path is exactly the corresponding whole homotopy edge. -/
theorem firstFiberAxis_path (t r : unitInterval) :
    (axisFiberLoop f A t).val.2 r = wholeHomotopy A B hc f (r, (t, 0)) :=
  (wholeHomotopy_zero_second A B hc f r t).symm

/-- The second actual fiber axis projects to the second whole source-square edge. -/
theorem secondFiberAxis_source (s : unitInterval) :
    (axisFiberLoop f B s).val.1 = sourceSquare A B hc (0, s) :=
  (sourceSquare_zero_first A B hc s).symm

/-- Its complete stored path is exactly the other whole homotopy edge. -/
theorem secondFiberAxis_path (s r : unitInterval) :
    (axisFiberLoop f B s).val.2 r = wholeHomotopy A B hc f (r, (0, s)) :=
  (wholeHomotopy_zero_first A B hc f r s).symm

/-- The constructed fiber loop as a class in the original cubical Pi one. -/
def axisFiberClass (a : Path p p) :
    HomotopyGroup.Pi 1 (HomotopyFiber f (f p)) (basepoint f (f p) p rfl) :=
  cappedLoopClass f rfl a (axisNullPath f a)

/-- Its actual projection class is the original source path class. -/
theorem axisFiberClass_projection (a : Path p p) :
    piMap 0 (projection f (f p)) (projection_basepoint f (f p) p rfl) (axisFiberClass f a) =
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk a) : FundamentalGroup X p) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (HomotopyGroup.map (projection f (f p)) rfl (axisFiberClass f a)) = _
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply]
  change FundamentalGroup.mapOfEq (projection f (f p)) rfl
    (HomotopyGroup.pi1MulEquivFundamentalGroup
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (axisFiberLoop f a))))) = _
  rw [MulEquiv.apply_symm_apply, FundamentalGroup.mapOfEq_apply]
  apply CategoryTheory.End.ext
  change Path.Homotopic.Quotient.mk ((axisFiberLoop f a).map (projection f (f p)).continuous) = _
  rw [axisFiberLoop_projection]

/-- Two commuting original Pi-one classes have actual based path representatives whose
commutativity is retained in the original fundamental-group model. -/
theorem exists_commuting_loop_representatives
    (g h : HomotopyGroup.Pi 1 X p) (hgh : Commute g h) :
    ∃ A B : Path p p,
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk A) : FundamentalGroup X p) = g ∧
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk B) : FundamentalGroup X p) = h ∧
      @Commute (FundamentalGroup X p) inferInstance
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk A)) (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk B)) := by
  let e := HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := p)
  obtain ⟨A, hA⟩ := Path.Homotopic.Quotient.mk_surjective (e g).asHom
  obtain ⟨B, hB⟩ := Path.Homotopic.Quotient.mk_surjective (e h).asHom
  have hA := congrArg FundamentalGroup.fromPath hA
  have hB := congrArg FundamentalGroup.fromPath hB
  refine ⟨A, B, ?_, ?_, ?_⟩
  · change e.symm (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk A)) = g
    rw [hA, MulEquiv.symm_apply_apply]
  · change e.symm (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk B)) = h
    rw [hB, MulEquiv.symm_apply_apply]
  · rw [hA, hB]
    change e g * e h = e h * e g
    simpa only [map_mul] using congrArg e hgh.eq

include hc in
/-- The capping existence statement contains only constructed geometric data and exact edge laws. -/
theorem exists_periodic_capping :
    ∃ τ : C(unitInterval × unitInterval, X), ∃ β : GenLoop (Fin 2) Y (f p),
      ∃ H : (f.comp τ).Homotopy (basedSquare β),
        τ (0, 0) = p ∧
        (∀ s, τ (0, s) = B s ∧ τ (1, s) = B s) ∧
        (∀ t, τ (t, 0) = A t ∧ τ (t, 1) = A t) ∧
        (∀ r s, H (r, (0, s)) = H (r, (1, s))) ∧
        (∀ r t, H (r, (t, 0)) = H (r, (t, 1))) ∧
        ∀ r, H (r, (0, 0)) = f p := by
  refine ⟨sourceSquare A B hc, targetCube A B hc f, wholeHomotopy A B hc f,
    sourceSquare_vertex A B hc, ?_, ?_, (wholeHomotopy_periodic A B hc f).1,
    (wholeHomotopy_periodic A B hc f).2, wholeHomotopy_vertex A B hc f⟩
  · intro s
    exact ⟨sourceSquare_zero_first A B hc s, sourceSquare_one_first A B hc s⟩
  · intro t
    exact ⟨sourceSquare_zero_second A B hc t, sourceSquare_one_second A B hc t⟩

end Topology.HomotopyFiber.CommutingSquareCapping
