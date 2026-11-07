/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Basic
public import Mathlib.CategoryTheory.Core
public import Colib.CategoryTheory.QConstruction.ObjectClass
public import Colib.Topology.ClassifyingSpace.Constant
public import Colib.Topology.ClassifyingSpace.ArrowPaths
public import Colib.Topology.ClassifyingSpace.Naturality
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift
public import Colib.CategoryTheory.ExactCategory.Functor.QIsomorphisms

/-!
# The actual Q automorphism cylinder

The zero-apex and full-apex Q-cones define a literal loop-valued map on the
core. An actual automorphism edge maps to a cylinder; explicit cancellation
caps turn it into an element of the original Q K₁ group. The Q-path coordinate
comes first. No comparison with the stable-completion class is asserted.

This construction retains the Q-spans, cone paths and cap of the R5
`AutomorphismClass` source at revision `1b7c3945394bcc27a94d1ebf86df702b0291ee18`.
Its geometric recipe is motivated by Weibel, The K-book, IV, Exercise 7.9;
identification with an externally oriented sphere is a separate statement.
-/
/-! Implementation source: `Quillen/KTheory/Automorphism/Class.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual cone paths,
composition triangles and categorical universes are preserved under native ownership. -/
@[expose] public section
open CategoryTheory.ExactCategory (ExactFunctor ExactStructure)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits Topology
open scoped ZeroObject Topology unitInterval

namespace CategoryTheory.ExactCategory.Automorphism
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Ordinary isomorphisms preserve the zero-apex Q-arrow. -/
theorem fromZero_iso {A B : C} (e : A ≅ B) :
    E.fromZero (QConstruction.of _ _ A) ≫ (E.qIsoOfIso e).hom =
      E.fromZero (QConstruction.of _ _ B) := by
  let s : Span E.deflation E.inflation (0 : C) A :=
    { apex := 0, l := 𝟙 _, r := 0, wl := E.deflation_id _, wr := E.inflation_zero A }
  let t := QConstruction.isoSpan E.deflation E.inflation e (E.inflation_of_iso e)
  let sq : IsPullback (𝟙 (0 : C)) (0 : (0 : C) ⟶ A) (0 : (0 : C) ⟶ A) (𝟙 A) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  let : HasPullback (0 : (0 : C) ⟶ A) (𝟙 A) := sq.hasPullback
  change QConstruction.mkHom _ _ (Span.comp s t) = _
  symm
  apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst _ _ ≫ 𝟙 _ = 𝟙 _
    simp
  · change sq.isoPullback.hom ≫ pullback.snd _ _ ≫ e.hom = 0
    simp

/-- Ordinary isomorphisms also preserve the full-apex Q-arrow. -/
theorem fullFromZero_iso {A B : C} (e : A ≅ B) :
    E.fromZeroTotal (QConstruction.of _ _ A) ≫ (E.qIsoOfIso e).hom =
      E.fromZeroTotal (QConstruction.of _ _ B) := by
  let s : Span E.deflation E.inflation (0 : C) A :=
    { apex := A, l := 0, r := 𝟙 A, wl := E.deflation_zero A, wr := E.inflation_id A }
  let t := QConstruction.isoSpan E.deflation E.inflation e (E.inflation_of_iso e)
  let sq : IsPullback (𝟙 A) (𝟙 A) (𝟙 A) (𝟙 A) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  let : HasPullback s.r t.l := sq.hasPullback
  change QConstruction.mkHom _ _ (Span.comp s t) = _
  symm
  apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ (e.symm ≪≫ sq.isoPullback)
  · change (e.inv ≫ sq.isoPullback.hom) ≫ pullback.fst _ _ ≫ 0 = 0
    simp
  · change (e.inv ≫ sq.isoPullback.hom) ≫ pullback.snd _ _ ≫ e.hom = 𝟙 B
    simp

/-- Inclusion of the original core into the actual Q-category. -/
def coreQ : Core C ⥤ E.QCategory where
  obj A := QConstruction.of E.deflation E.inflation A.of
  map f := (E.qIsoOfIso f.iso).hom
  map_id _A := rfl
  map_comp f g := congrArg Iso.hom (E.qIsoOfIso_trans f.iso g.iso)

/-- The zero-apex natural cone. -/
def zeroCone : (Functor.const (Core C)).obj E.qZero ⟶ coreQ E where
  app A := E.fromZero _
  naturality {_ _} f := by simpa [coreQ] using (fromZero_iso E f.iso).symm

/-- The full-apex natural cone. -/
def fullCone : (Functor.const (Core C)).obj E.qZero ⟶ coreQ E where
  app A := E.fromZeroTotal (QConstruction.of _ _ A.of)
  naturality {_ _} f := by simpa [coreQ] using (fullFromZero_iso E f.iso).symm

end CategoryTheory.ExactCategory.Automorphism

namespace CategoryTheory.ExactCategory.Automorphism
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- An actual continuous path from zero to the image of each core-space point. -/
def conePath (α : (Functor.const (Core C)).obj E.qZero ⟶ coreQ E)
    (x : ClassifyingSpace (Core C)) :
    Path E.kBasepoint (classifyingSpaceMap (coreQ E) x) where
  toFun t := classifyingSpaceNaturalTransformationHomotopy α (t, x)
  continuous_toFun := (classifyingSpaceNaturalTransformationHomotopy α).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := by
    rw [(classifyingSpaceNaturalTransformationHomotopy α).apply_zero]
    change classifyingSpaceMap ((Functor.const (Core C)).obj E.qZero) x = _
    rw [classifyingSpaceMap_const_direct]
    rfl
  target' := (classifyingSpaceNaturalTransformationHomotopy α).apply_one x

/-- The literal loop-valued map made from the two Q-zero cones. -/
def coreLoopMap : C(ClassifyingSpace (Core C), Path E.kBasepoint E.kBasepoint) where
  toFun x := (conePath E (zeroCone E) x).trans (conePath E (fullCone E) x).symm
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun p : ClassifyingSpace (Core C) × unitInterval =>
      ((conePath E (zeroCone E) p.1).trans (conePath E (fullCone E) p.1).symm) p.2)
    refine Path.trans_continuous_family (conePath E (zeroCone E)) ?_
      (fun x => (conePath E (fullCone E) x).symm) ?_
    · change Continuous (fun p : ClassifyingSpace (Core C) × unitInterval =>
        classifyingSpaceNaturalTransformationHomotopy (zeroCone E) (p.2, p.1))
      exact (classifyingSpaceNaturalTransformationHomotopy (zeroCone E)).continuous.comp
        continuous_swap
    · change Continuous (fun p : ClassifyingSpace (Core C) × unitInterval =>
        classifyingSpaceNaturalTransformationHomotopy (fullCone E) (unitInterval.symm p.2, p.1))
      exact (classifyingSpaceNaturalTransformationHomotopy (fullCone E)).continuous.comp
        ((unitInterval.continuous_symm.comp continuous_snd).prodMk continuous_fst)

/-- The canonical path in the loop space from the constant loop to a loop followed
by its inverse. This is the explicit cap needed to turn the cylinder into a based sphere. -/
def cancellationPath {X : Type*} [TopologicalSpace X] {x : X} (p : Path x x) :
    Path (Path.refl x) (p.trans p.symm) where
  toFun t := (Path.Homotopy.reflTransSymm p).eval t
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (Path.Homotopy.reflTransSymm p).continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

/-- Translate a loop-space component by the inverse of its chosen base loop. -/
def rightTranslate {X : Type*} [TopologicalSpace X] {x : X} (p : Path x x) :
    C(Path x x, Path x x) :=
  ⟨fun q => q.trans p.symm, continuous_id.path_trans continuous_const⟩

/-- A genuine group map from the fundamental group of any loop-space component
into pi_2(X,x), obtained by translation, the explicit cancellation cap, and currying. -/
def loopComponentToPiTwo {X : Type*} [TopologicalSpace X] {x : X} (p : Path x x) :
    FundamentalGroup (Path x x) p →* HomotopyGroup.Pi 2 X x :=
  (loopShiftMulEquiv (x := x) 0).symm.toMonoidHom.comp
    ((HomotopyGroup.pi1MulEquivFundamentalGroup
      (X := Path x x) (x := Path.refl x)).symm.toMonoidHom.comp
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath (cancellationPath p)).symm.toMonoidHom.comp
        (FundamentalGroup.map (rightTranslate p) p)))

/-- The ordinary automorphism group, as the endomorphism group in the core. -/
def automorphismCoreEnd (A : C) : Aut A →* End (Core.mk A) where
  toFun α := End.of (CoreHom.mk α.asIso)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Canonical automorphism class in the actual Q K1 group.
The realized two zero-cones and the original realized automorphism edge are used.
The only cap is explicit path cancellation; there is no chosen K1 equivalence. -/
def automorphismClass (A : C) : Aut A →* E.K 1 :=
  (loopComponentToPiTwo (coreLoopMap E (classifyingSpacePoint (Core.mk A)))).comp
    ((FundamentalGroup.map (coreLoopMap E) (classifyingSpacePoint (Core.mk A))).comp
      (((classifyingFundamentalGroupoidFunctor (Core C)).mapEnd (Core.mk A)).comp
        (automorphismCoreEnd A)))

/-- The actual two-row cylinder, as a loop in the loop space at the object loop. -/
def automorphismCylinder {A : C} (α : Aut A) :
    Path (coreLoopMap E (classifyingSpacePoint (Core.mk A)))
      (coreLoopMap E (classifyingSpacePoint (Core.mk A))) :=
  (classifyingSpacePath (CoreHom.mk α.asIso : Core.mk A ⟶ Core.mk A)).map
    (coreLoopMap E).continuous

/-- The class formula exposes exactly which geometric cylinder is fed to the cap. -/
theorem automorphismClass_eq {A : C} (α : Aut A) :
    automorphismClass E A α =
      loopComponentToPiTwo (coreLoopMap E (classifyingSpacePoint (Core.mk A)))
        (FundamentalGroup.fromPath ⟦automorphismCylinder E α⟧) := rfl

/-- At an object, the loop is exactly the two canonical Q-edges, with the
full-apex edge traversed backwards, as in Weibel IV Exercise 7.9. -/
theorem coreLoopMap_vertex (A : C) :
    coreLoopMap E (classifyingSpacePoint (Core.mk A)) =
      (classifyingSpacePath (E.fromZero (QConstruction.of _ _ A))).trans
        (classifyingSpacePath (E.fromZeroTotal (QConstruction.of _ _ A))).symm := by
  have hz (t) : conePath E (zeroCone E) (classifyingSpacePoint (Core.mk A)) t =
      classifyingSpacePath (E.fromZero (QConstruction.of _ _ A)) t :=
    classifyingSpaceNaturalTransformationHomotopy_vertex (zeroCone E) (Core.mk A) t
  have hf (t) : conePath E (fullCone E) (classifyingSpacePoint (Core.mk A)) t =
      classifyingSpacePath (E.fromZeroTotal (QConstruction.of _ _ A)) t :=
    classifyingSpaceNaturalTransformationHomotopy_vertex (fullCone E) (Core.mk A) t
  ext t
  change ((conePath E (zeroCone E) _).trans (conePath E (fullCone E) _).symm) t = _
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact hz _
  · exact hf _

section ExactFunctor
variable {D : Type u} [SmallCategory D] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- An exact functor preserves the zero-apex edge with the genuine zero-object
comparison displayed explicitly. -/
theorem mapQ_zeroCone (A : C) :
    F.mapQ.map (EC.fromZero (QConstruction.of _ _ A)) =
      (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom ≫
        ED.fromZero (QConstruction.of _ _ (F.toFunctor.obj A)) := by
  let e := F.toFunctor.mapZeroObject
  let sq : IsPullback (𝟙 (F.toFunctor.obj (0 : C))) e.hom e.hom (𝟙 (0 : D)) :=
    IsPullback.of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩
  let : HasPullback e.hom (𝟙 (0 : D)) := sq.hasPullback
  apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst _ _ ≫ 𝟙 _ = F.toFunctor.map (𝟙 (0 : C))
    calc
      _ = 𝟙 (F.toFunctor.obj (0 : C)) := by
        simp only [Category.comp_id, IsPullback.isoPullback_hom_fst]
      _ = _ := (F.toFunctor.map_id (0 : C)).symm
  · change sq.isoPullback.hom ≫ pullback.snd _ _ ≫ 0 = F.toFunctor.map (0 : (0 : C) ⟶ A)
    simp

/-- The same exact functor preserves the full-apex edge with the same zero
comparison. These are the two actual rows required for scalar-class naturality. -/
theorem mapQ_fullCone (A : C) :
    F.mapQ.map (EC.fromZeroTotal (QConstruction.of _ _ A)) =
      (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom ≫
        ED.fromZeroTotal (QConstruction.of _ _ (F.toFunctor.obj A)) := by
  let e := F.toFunctor.mapZeroObject
  let sq : IsPullback (0 : F.toFunctor.obj A ⟶ F.toFunctor.obj (0 : C))
      (𝟙 (F.toFunctor.obj A)) e.hom (0 : F.toFunctor.obj A ⟶ (0 : D)) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  let : HasPullback e.hom (0 : F.toFunctor.obj A ⟶ (0 : D)) := sq.hasPullback
  apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst _ _ ≫ 𝟙 _ = F.toFunctor.map (0 : A ⟶ (0 : C))
    simp
  · change sq.isoPullback.hom ≫ pullback.snd _ _ ≫ 𝟙 _ = F.toFunctor.map (𝟙 A)
    simp

/-- The ordinary core action and the genuine Q action of an exact functor
agree on every object and every automorphism. -/
def coreQMapIso : coreQ EC ⋙ F.mapQ ≅ F.toFunctor.core ⋙ coreQ ED :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    simp only [Functor.comp_map, Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact congrArg Iso.hom (F.mapQ_qIsoOfIso f.iso))

end ExactFunctor
end CategoryTheory.ExactCategory.Automorphism
