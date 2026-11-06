/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Exact


/-! # Faithfulness of the exact-row Q comparison

A natural transformation of exact quotient diagrams is determined by its
component on the whole interval. Monic inclusions determine the initial
subobjects, and epic quotient maps determine all remaining components.
The central-interval Q comparison therefore detects every row isomorphism.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuotientRows

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)
variable {n : SimplexCategory}

/-- A map of exact quotient rows is determined by its whole-interval component. -/
theorem rowNatTrans_ext_top {F G : Obj (ofExactCategory E) n} (e f : F.obj ⟶ G.obj)
    (h : e.app (interval 0 (Fin.last n.len) (Fin.zero_le _)) =
      f.app (interval 0 (Fin.last n.len) (Fin.zero_le _))) : e = f := by
  have h₀ (j : Fin (n.len + 1)) :
      e.app (interval 0 j (Fin.zero_le _)) = f.app (interval 0 j (Fin.zero_le _)) := by
    let g : interval 0 j (Fin.zero_le _) ⟶ interval 0 (Fin.last n.len) (Fin.zero_le _) :=
      homOfLE ⟨le_rfl, Fin.le_last j⟩
    let : Mono (G.obj.map g) := E.mono_of_inflation
      (G.property.cofibration 0 j (Fin.last n.len) (Fin.zero_le _) (Fin.le_last j))
    apply (cancel_mono (G.obj.map g)).1
    rw [← e.naturality, ← f.naturality, h]
  apply NatTrans.ext
  funext p
  rcases p with ⟨⟨i, j⟩, hij⟩
  let g : interval 0 j (Fin.zero_le _) ⟶ interval i j hij := homOfLE ⟨Fin.zero_le _, le_rfl⟩
  let : Epi (F.obj.map g) := E.epi_of_deflation
    (row_deflation E F 0 i j (Fin.zero_le _) hij)
  apply (cancel_epi (F.obj.map g)).1
  change F.obj.map g ≫ e.app (interval i j hij) =
    F.obj.map g ≫ f.app (interval i j hij)
  rw [e.naturality g, f.naturality g, h₀]


end CategoryTheory.Waldhausen.QuotientRows
