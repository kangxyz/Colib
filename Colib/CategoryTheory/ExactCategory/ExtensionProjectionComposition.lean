/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionGeometry
public import Colib.CategoryTheory.ExactCategory.BaseChangeSquare

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionProjectionComposition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The genuine pullback apex of composite extension quotient spans -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C) {x y z : E.ExtensionTotal} (f : x ⟶ y) (g : y ⟶ z)

local notation "sf" => E.extensionProjectionSpan f
local notation "sg" => E.extensionProjectionSpan g
local notation "qf" => E.extensionProjectionCokernel f
local notation "qg" => E.extensionProjectionCokernel g

local instance spanHasPullback : HasPullback (sf).r (sg).l :=
  letI : HasPullback (sg).l (sf).r := E.deflation.hasPullback (sf).r (sg).wl
  hasPullback_symmetry _ _

/-- The actual map from the middle object to the original Q-composition pullback apex. -/
def extensionCompositeProjection : x.base.obj ⟶ (Span.comp sf sg).apex :=
  pullback.lift (qf).π (f.base.hom ≫ (qg).π) (by
    rw [(qf).right, Category.assoc, (qg).left])

/-- The upper square obtained by canceling the lower pullback square is a pullback. -/
theorem extensionCompositeProjection_isPullback :
    IsPullback f.base.hom (E.extensionCompositeProjection f g)
      (qg).π (pullback.snd (sf).r (sg).l) := by
  have outer : IsPullback f.base.hom
      (E.extensionCompositeProjection f g ≫ pullback.fst (sf).r (sg).l)
      ((qg).π ≫ (sg).l) (sf).r := by
    simpa only [extensionCompositeProjection, pullback.lift_fst, (qg).left] using
      E.extensionProjection_right_isPullback f
  exact outer.of_bot (by simp [extensionCompositeProjection])
    (IsPullback.of_hasPullback (sf).r (sg).l).flip

/-- The reversed-domain component composes in the reversed order. -/
theorem extensionDomainMap_comp :
    (Subdivision.domainMap (f ≫ g)).hom =
      (Subdivision.domainMap g).hom ≫ (Subdivision.domainMap f).hom := by
  simp [Subdivision.domainMap, Grothendieck.comp_fiber]

/-- The composite kernel inclusion maps to the second arrow's kernel inclusion. -/
theorem extensionCompositeKernel_map :
    ((Subdivision.domainMap (f ≫ g)).hom ≫ x.fiber.unop.hom.hom) ≫ f.base.hom =
      (Subdivision.domainMap g).hom ≫ y.fiber.unop.hom.hom := by
  have hw := congrArg (fun a => a.hom) (Subdivision.factorization f)
  simp only [WideSubcategory.comp_def] at hw
  rw [E.extensionDomainMap_comp f g]
  simp only [Category.assoc]
  rw [hw]

/-- The smaller subobject is killed by the genuine composite-apex quotient. -/
theorem extensionCompositeProjection_zero :
    ((Subdivision.domainMap (f ≫ g)).hom ≫ x.fiber.unop.hom.hom) ≫
      E.extensionCompositeProjection f g = 0 := by
  apply pullback.hom_ext
  · simp only [Category.assoc, extensionCompositeProjection, pullback.lift_fst, zero_comp]
    rw [E.extensionDomainMap_comp f g]
    simpa only [Category.assoc, comp_zero] using congrArg
      (fun a => (Subdivision.domainMap g).hom ≫ a) (qf).zero
  · simp only [Category.assoc, extensionCompositeProjection, pullback.lift_snd, zero_comp]
    simpa only [Category.assoc] using
      (congrArg (fun a => a ≫ (qg).π) (E.extensionCompositeKernel_map f g)).trans (qg).zero

/-- The original composition pullback apex has the required quotient conflation. -/
theorem extensionCompositeProjection_conflation :
    E.conflation (ShortComplex.mk
      ((Subdivision.domainMap (f ≫ g)).hom ≫ x.fiber.unop.hom.hom)
      (E.extensionCompositeProjection f g) (E.extensionCompositeProjection_zero f g)) := by
  have cG : E.conflation (ShortComplex.mk _ (qg).π (qg).zero) :=
    E.conflation_of_inflation_of_isCokernel
    (E.inflation_comp _ _ (Subdivision.domainMap g).property y.fiber.unop.hom.property)
    (qg).isColimit
  exact E.conflation_of_isPullback cG (E.extensionCompositeProjection_isPullback f g) _
    (E.extensionCompositeKernel_map f g) (E.extensionCompositeProjection_zero f g)

/-- The quotient assignment preserves composition in the original Q category,
using the genuine pullback composite and a commuting cokernel apex isomorphism. -/
theorem extensionProjectionQMap_comp :
    E.extensionProjectionQMap (f ≫ g) =
      E.extensionProjectionQMap f ≫ E.extensionProjectionQMap g := by
  let q := E.extensionProjectionCokernel (f ≫ g)
  let p := E.extensionCompositeProjection f g
  let hc := E.cokernel _ (E.extensionCompositeProjection_conflation f g)
  let e := q.isColimit.coconePointUniqueUpToIso hc
  have he : q.π ≫ e.hom = p :=
    q.isColimit.comp_coconePointUniqueUpToIso_hom hc WalkingParallelPair.one
  let : Epi q.π := Cofork.IsColimit.epi q.isColimit
  change QConstruction.mkHom E.deflation E.inflation (E.extensionProjectionSpan (f ≫ g)) =
    QConstruction.mkHom E.deflation E.inflation (Span.comp sf sg)
  apply QConstruction.mkHom_eq_of_apexIso E.deflation E.inflation _ _ e
  · apply (cancel_epi q.π).1
    rw [← Category.assoc, he, q.left]
    change p ≫ (pullback.fst (sf).r (sg).l ≫ (sf).l) = _
    simpa only [p, extensionCompositeProjection, pullback.lift_fst_assoc] using (qf).left
  · apply (cancel_epi q.π).1
    rw [← Category.assoc, he, q.right]
    change p ≫ (pullback.snd (sf).r (sg).l ≫ (sg).r) =
      (f.base.hom ≫ g.base.hom) ≫ (E.extensionQuotientData z).π
    simp only [p, extensionCompositeProjection, pullback.lift_snd_assoc, Category.assoc,
      (qg).right]

end CategoryTheory.ExactCategory.ExactStructure
