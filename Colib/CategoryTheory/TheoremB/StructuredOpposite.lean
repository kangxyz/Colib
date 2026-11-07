/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.StructuredComparison
public import Colib.Topology.ClassifyingSpace.OppositePoint
public import Colib.Topology.HomotopyFiber.Homeomorph

/-! Concrete transport of the structured comparison through opposite realization. -/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredOpposite.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, paths and identity
basepoints are retained under native namespace and dependency ownership. -/
@[expose] public section

noncomputable section
open SSet TopCat Topology CategoryTheory Opposite
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- Equality of the endpoint gives the identity-coordinate fiber homeomorphism. -/
def fiberEndpointHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {y y' : Y} (h : y = y') :
    HomotopyFiber f y ≃ₜ HomotopyFiber f y' where
  toFun a := ⟨a.1, a.2.1, a.2.2.trans h⟩
  invFun a := ⟨a.1, a.2.1, a.2.2.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp] theorem fiberEndpointHomeomorph_val {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {y y' : Y} (h : y = y')
    (a : HomotopyFiber f y) : (fiberEndpointHomeomorph f h a).1 = a.1 := rfl

private theorem squareHomeomorph_path {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, Y)) (g : C(X', Y')) (s : X ≃ₜ X') (t : Y ≃ₜ Y')
    (h : (t : C(Y, Y')).comp f = g.comp s) (y : Y) (a : HomotopyFiber f y)
    (r : unitInterval) :
    (HomotopyFiber.homeomorphOfSquare f g s t h y a).1.2 r = t (a.1.2 r) := rfl

/-- Opposite realization transports the entire genuine homotopy fiber,
using the source and target homeomorphisms and the exact object vertex. -/
def oppositeFiberHomeomorph (d : D) :
    HomotopyFiber (classifyingSpaceMap F.op).hom (classifyingSpacePoint (op d)) ≃ₜ
      HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d) :=
  (HomotopyFiber.homeomorphOfSquare (classifyingSpaceMap F.op).hom
    (classifyingSpaceMap F).hom (TopCat.homeoOfIso (classifyingOppositeIso C))
    (TopCat.homeoOfIso (classifyingOppositeIso D))
    (congrArg TopCat.Hom.hom (classifyingOppositeIso_naturality F))
    (classifyingSpacePoint (op d))).trans
    (fiberEndpointHomeomorph _ (classifyingOppositeIso_point d))

@[simp] theorem oppositeFiberHomeomorph_projection (d : D)
    (a : HomotopyFiber (classifyingSpaceMap F.op).hom (classifyingSpacePoint (op d))) :
    (oppositeFiberHomeomorph F d a).1.1 = (classifyingOppositeIso C).hom a.1.1 := rfl

@[simp] theorem oppositeFiberHomeomorph_path (d : D)
    (a : HomotopyFiber (classifyingSpaceMap F.op).hom (classifyingSpacePoint (op d)))
    (t : unitInterval) :
    (oppositeFiberHomeomorph F d a).1.2 t = (classifyingOppositeIso D).hom (a.1.2 t) := by
  unfold oppositeFiberHomeomorph
  rw [Homeomorph.trans_apply, fiberEndpointHomeomorph_val, squareHomeomorph_path]
  rfl

/-- The comparison obtained by transporting the costructured comparison of
`F.op` through the canonical comma and fiber equivalences. -/
def transportedStructuredFiberComparison (d : D) :
    C(ClassifyingSpace (StructuredArrow d F),
      HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  (oppositeFiberHomeomorph F d : C(_, _)).comp
    ((fiberComparison F.op (op d)).comp (structuredCommaOppositeEquiv F d).toFun)

/-- The opposite comma equivalence preserves the source projection exactly. -/
theorem structuredCommaOppositeEquiv_projection (d : D) :
    (classifyingOppositeIso C).hom.hom.comp
      ((classifyingSpaceMap (CostructuredArrow.proj F.op (op d))).hom.comp
        (structuredCommaOppositeEquiv F d).toFun) =
      (classifyingSpaceMap (StructuredArrow.proj d F)).hom := by
  have hc : (structuredArrowOpEquivalence F d).functor ⋙
      CostructuredArrow.proj F.op (op d) = (StructuredArrow.proj d F).op := rfl
  have hn := classifyingOppositeIso_naturality (StructuredArrow.proj d F)
  ext x
  change ((classifyingSpaceMap (structuredArrowOpEquivalence F d).functor ≫
      classifyingSpaceMap (CostructuredArrow.proj F.op (op d))) ≫
      (classifyingOppositeIso C).hom) ((classifyingOppositeIso (StructuredArrow d F)).inv x) = _
  rw [← classifyingSpaceMap_comp, hc, hn]
  change ((classifyingOppositeIso (StructuredArrow d F)).inv ≫
    (classifyingOppositeIso (StructuredArrow d F)).hom ≫
    classifyingSpaceMap (StructuredArrow.proj d F)) x = _
  simp

@[simp] theorem transportedStructuredFiberComparison_projection (d : D) :
    (HomotopyFiber.projection (classifyingSpaceMap F).hom (classifyingSpacePoint d)).comp
      (transportedStructuredFiberComparison F d) =
        (classifyingSpaceMap (StructuredArrow.proj d F)).hom :=
  structuredCommaOppositeEquiv_projection F d

end CategoryTheory.TheoremB
