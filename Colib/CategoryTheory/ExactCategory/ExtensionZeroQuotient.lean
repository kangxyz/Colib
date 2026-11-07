/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionIdentityFunctor

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionZeroQuotient.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Recovering identity extensions from a zero quotient -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- A Q-arrow to the original zero vertex forces its source object to be zero
in the original exact category. This does not assert existence of such arrows. -/
theorem isZero_of_qHom_to_zero (X : E.QCategory) (f : X ⟶ E.qZero) : IsZero X.obj.of := by
  induction f using Quotient.inductionOn with
  | _ s =>
    let : Mono s.r := E.mono_of_inflation s.wr
    have hs : IsZero s.apex := (IsZero.iff_id_eq_zero _).2 (by
      apply (cancel_mono s.r).1
      exact (isZero_zero C).eq_of_tgt _ _)
    let : Epi s.l := E.epi_of_deflation s.wl
    apply (IsZero.iff_id_eq_zero _).2
    apply (cancel_epi s.l).1
    exact hs.eq_of_src _ _

/-- An admissible kernel with zero quotient is an actual isomorphism. -/
theorem extensionInflation_isIso_of_isZero (x : E.ExtensionTotal)
    (hx : IsZero (E.extensionQuotientData x).obj) : IsIso x.fiber.unop.hom.hom := by
  let q := E.extensionQuotientData x
  have hq : q.π = 0 := hx.eq_of_tgt _ _
  let hk := E.kernel _ q.conflation
  let r := KernelFork.IsLimit.lift' hk (𝟙 x.base.obj) (by simp [hq])
  let : Mono x.fiber.unop.hom.hom := E.mono_of_inflation x.fiber.unop.hom.property
  have hr : r.1 ≫ x.fiber.unop.hom.hom = 𝟙 x.base.obj := r.2
  exact ⟨⟨r.1, (cancel_mono x.fiber.unop.hom.hom).1 (by simp [Category.assoc, hr]),
    hr⟩⟩

/-- A zero quotient supplies an actual isomorphism from an identity extension,
with unchanged kernel and the original inflation as middle-object map. -/
def identityExtensionIsoOfZeroQuotient (x : E.ExtensionTotal)
    (hx : IsZero (E.extensionQuotientData x).obj) :
    E.identityExtension x.fiber.unop.left.obj ≅ x := by
  let : IsIso x.fiber.unop.hom.hom := E.extensionInflation_isIso_of_isZero x hx
  let e : x.fiber.unop.left ≅ x.base := WideSubcategory.isoMk
    (asIso x.fiber.unop.hom.hom) x.fiber.unop.hom.property
    (E.inflation_of_iso (asIso x.fiber.unop.hom.hom).symm)
  exact Subdivision.isoMk (Iso.refl _) e (by
    apply WideSubcategory.hom_ext
    change 𝟙 _ ≫ x.fiber.unop.hom.hom = 𝟙 _ ≫ x.fiber.unop.hom.hom
    rfl)

end CategoryTheory.ExactCategory.ExactStructure
