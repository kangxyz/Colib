/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionIsomorphism
public import Colib.CategoryTheory.Subdivision.Action

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionTotalIsomorphism.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Extension isomorphisms from actual middle and quotient squares -/
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

/-- Middle-object maps determine total-extension morphisms, since all represented
kernel inclusions and middle maps are monomorphisms. -/
instance extensionTotalMiddle_faithful : E.extensionTotalMiddle.Faithful where
  map_injective {x y} f g h := by
    change f.base.hom = g.base.hom at h
    apply Subdivision.hom_ext
    · apply WideSubcategory.hom_ext
      let : Mono x.fiber.unop.hom.hom := E.mono_of_inflation x.fiber.unop.hom.property
      let : Mono f.base.hom := E.mono_of_inflation f.base.property
      apply (cancel_mono (x.fiber.unop.hom.hom ≫ f.base.hom)).1
      have hf := congrArg (fun k => k.hom) (Subdivision.factorization f)
      have hg := congrArg (fun k => k.hom) (Subdivision.factorization g)
      simpa only [WideSubcategory.comp_def, h] using hf.trans hg.symm
    · apply WideSubcategory.hom_ext
      exact h

/-- Every actual total-extension arrow is monic, as its middle map is an inflation. -/
instance extensionHom_mono {x y : E.ExtensionTotal} (f : x ⟶ y) : Mono f where
  right_cancellation {z} g h w := by
    apply E.extensionTotalMiddle.map_injective
    change g.base.hom = h.base.hom
    let : Mono f.base.hom := E.mono_of_inflation f.base.property
    apply (cancel_mono f.base.hom).1
    exact congrArg (fun k => k.base.hom) w

/-- Compatible isomorphisms of the middle and quotient induce the actual
kernel isomorphism, retaining the chosen kernel objects. -/
def extensionKernelIsoOfQuotientSquare {x y : E.ExtensionTotal}
    (b : x.base.obj ≅ y.base.obj)
    (e : (E.extensionQuotientData x).obj ≅ (E.extensionQuotientData y).obj)
    (w : (E.extensionQuotientData x).π ≫ e.hom = b.hom ≫ (E.extensionQuotientData y).π) :
    x.fiber.unop.left.obj ≅ y.fiber.unop.left.obj := by
  let qx := E.extensionQuotientData x
  let qy := E.extensionQuotientData y
  let ix := x.fiber.unop.hom.hom
  let iy := y.fiber.unop.hom.hom
  let hx := E.kernel _ qx.conflation
  let hy := E.kernel _ qy.conflation
  have w' : qy.π ≫ e.inv = b.inv ≫ qx.π := by
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [w]
    simp
    rfl
  have zx : (ix ≫ b.hom) ≫ qy.π = 0 := by
    rw [Category.assoc, ← w, ← Category.assoc, qx.zero, zero_comp]
  have zy : (iy ≫ b.inv) ≫ qx.π = 0 := by
    rw [Category.assoc, ← w', ← Category.assoc, qy.zero, zero_comp]
  let f := hy.lift (KernelFork.ofι (ix ≫ b.hom) zx)
  let g := hx.lift (KernelFork.ofι (iy ≫ b.inv) zy)
  have hf : f ≫ iy = ix ≫ b.hom := hy.fac _ WalkingParallelPair.zero
  have hg : g ≫ ix = iy ≫ b.inv := hx.fac _ WalkingParallelPair.zero
  let : Mono ix := E.mono_of_inflation x.fiber.unop.hom.property
  let : Mono iy := E.mono_of_inflation y.fiber.unop.hom.property
  refine ⟨f, g, ?_, ?_⟩
  · apply (cancel_mono ix).1
    rw [Category.assoc, hg, ← Category.assoc, hf]
    simp
  · apply (cancel_mono iy).1
    rw [Category.assoc, hf, ← Category.assoc, hg]
    simp

@[reassoc (attr := simp)]
theorem extensionKernelIsoOfQuotientSquare_hom_ι {x y : E.ExtensionTotal}
    (b : x.base.obj ≅ y.base.obj)
    (e : (E.extensionQuotientData x).obj ≅ (E.extensionQuotientData y).obj)
    (w : (E.extensionQuotientData x).π ≫ e.hom = b.hom ≫ (E.extensionQuotientData y).π) :
    (E.extensionKernelIsoOfQuotientSquare b e w).hom ≫ y.fiber.unop.hom.hom =
      x.fiber.unop.hom.hom ≫ b.hom :=
  (E.kernel _ (E.extensionQuotientData y).conflation).fac _ WalkingParallelPair.zero

/-- An actual extension isomorphism obtained from the compatible square. -/
def extensionIsoOfQuotientSquare {x y : E.ExtensionTotal}
    (b : x.base.obj ≅ y.base.obj)
    (e : (E.extensionQuotientData x).obj ≅ (E.extensionQuotientData y).obj)
    (w : (E.extensionQuotientData x).π ≫ e.hom = b.hom ≫ (E.extensionQuotientData y).π) :
    x ≅ y :=
  Subdivision.isoMk
    (WideSubcategory.isoMk (E.extensionKernelIsoOfQuotientSquare b e w)
      (E.inflation_of_iso _) (E.inflation_of_iso
        (E.extensionKernelIsoOfQuotientSquare b e w).symm))
    (WideSubcategory.isoMk b (E.inflation_of_iso b) (E.inflation_of_iso b.symm))
    (by apply WideSubcategory.hom_ext
        exact (E.extensionKernelIsoOfQuotientSquare_hom_ι b e w).symm)

@[simp]
theorem extensionIsoOfQuotientSquare_hom_base {x y : E.ExtensionTotal}
    (b : x.base.obj ≅ y.base.obj)
    (e : (E.extensionQuotientData x).obj ≅ (E.extensionQuotientData y).obj)
    (w : (E.extensionQuotientData x).π ≫ e.hom = b.hom ≫ (E.extensionQuotientData y).π) :
    (E.extensionIsoOfQuotientSquare b e w).hom.base.hom = b.hom := rfl

/-- This extension isomorphism projects to precisely the supplied quotient isomorphism. -/
theorem extensionIsoOfQuotientSquare_projection {x y : E.ExtensionTotal}
    (b : x.base.obj ≅ y.base.obj)
    (e : (E.extensionQuotientData x).obj ≅ (E.extensionQuotientData y).obj)
    (w : (E.extensionQuotientData x).π ≫ e.hom = b.hom ≫ (E.extensionQuotientData y).π) :
    E.extensionProjectionQMap (E.extensionIsoOfQuotientSquare b e w).hom =
      (E.qIsoOfIso e).hom := by
  let : Epi (Subdivision.domainMap
      (E.extensionIsoOfQuotientSquare b e w).hom).hom := by
    change Epi (E.extensionKernelIsoOfQuotientSquare b e w).inv
    infer_instance
  exact E.extensionProjectionQMap_eq_qIsoOfIso _ e w

end CategoryTheory.ExactCategory.ExactStructure
