/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionFunctor
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionGeometry
public import Colib.CategoryTheory.QConstruction.Core
public import Colib.CategoryTheory.Subdivision.Action

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionProjectionConservative.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The original extension projection reflects isomorphisms -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- An invertible projected Q-arrow forces the middle-object map to be invertible. -/
theorem extensionProjection_isIso_base {x y : E.ExtensionTotal} (f : x ⟶ y)
    [hf : IsIso (E.extensionProjectionQMap f)] : IsIso f.base.hom := by
  let : IsIso (QConstruction.mkHom _ _ (E.extensionProjectionSpan f)) := hf
  have hr := (E.qSpan_isIso_legs (E.extensionProjectionSpan f)).2
  let := hr
  exact (E.extensionProjection_right_isPullback f).isIso_fst_of_isIso

/-- An invertible projected Q-arrow also forces the reversed kernel map to be invertible. -/
theorem extensionProjection_isIso_domainMap {x y : E.ExtensionTotal} (f : x ⟶ y)
    [hf : IsIso (E.extensionProjectionQMap f)] : IsIso (Subdivision.domainMap f).hom := by
  let : IsIso (QConstruction.mkHom _ _ (E.extensionProjectionSpan f)) := hf
  have hl := (E.qSpan_isIso_legs (E.extensionProjectionSpan f)).1
  let := hl
  let q := E.extensionProjectionCokernel f
  let h := (Subdivision.domainMap f).hom
  let i := x.fiber.unop.hom.hom
  have hi : E.inflation (h ≫ i) := E.inflation_comp _ _
    (Subdivision.domainMap f).property x.fiber.unop.hom.property
  have hc := E.conflation_of_inflation_of_isCokernel
    (S := ShortComplex.mk (h ≫ i) q.π q.zero) hi q.isColimit
  let hk := isKernelCompMono (E.kernel _ hc) (E.extensionProjectionSpan f).l q.left.symm
  let qx := E.extensionQuotientData x
  let e := hk.conePointUniqueUpToIso (E.kernel _ qx.conflation)
  have he : e.hom ≫ i = h ≫ i :=
    hk.conePointUniqueUpToIso_hom_comp (E.kernel _ qx.conflation) WalkingParallelPair.zero
  let : Mono i := E.mono_of_inflation x.fiber.unop.hom.property
  have heq : e.hom = h := (cancel_mono i).1 he
  change IsIso h
  rw [← heq]
  infer_instance

/-- The actual subdivision arrow is invertible whenever its original Q projection is. -/
theorem extensionProjection_isIso {x y : E.ExtensionTotal} (f : x ⟶ y)
    [hf : IsIso (E.extensionProjectionQMap f)] : IsIso f := by
  let := E.extensionProjection_isIso_base f
  let := E.extensionProjection_isIso_domainMap f
  let a : x.fiber.unop.left ≅ y.fiber.unop.left :=
    WideSubcategory.isoMk (asIso (Subdivision.domainMap f).hom).symm
      (E.inflation_of_iso (asIso (Subdivision.domainMap f).hom).symm)
      (E.inflation_of_iso (asIso (Subdivision.domainMap f).hom))
  let b : x.base ≅ y.base := WideSubcategory.isoMk (asIso f.base.hom)
    (E.inflation_of_iso (asIso f.base.hom))
    (E.inflation_of_iso (asIso f.base.hom).symm)
  let e : x ≅ y := Subdivision.isoMk a b (by
    apply WideSubcategory.hom_ext
    change x.fiber.unop.hom.hom ≫ f.base.hom =
      inv (Subdivision.domainMap f).hom ≫ y.fiber.unop.hom.hom
    apply (cancel_epi (Subdivision.domainMap f).hom).1
    simp only [IsIso.hom_inv_id_assoc]
    exact congrArg (fun k => k.hom) (Subdivision.factorization f))
  have he : e.hom = f := Subdivision.hom_ext _ _ rfl rfl
  rw [← he]
  infer_instance

/-- Conservativity concerns the unchanged original Q target. -/
instance extensionProjection_reflectsIsomorphisms : E.extensionProjection.ReflectsIsomorphisms where
  reflects {x y} f _ := by
    let : IsIso (E.extensionProjectionQMap f) :=
      inferInstanceAs (IsIso (E.extensionProjection.map f))
    exact E.extensionProjection_isIso f

end CategoryTheory.ExactCategory.ExactStructure
