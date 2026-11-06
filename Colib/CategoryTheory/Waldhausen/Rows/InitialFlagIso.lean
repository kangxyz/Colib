/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.InitialFlag
public import Colib.CategoryTheory.Waldhausen.Rows.Faithful


/-! # Exact row isomorphisms from compatible initial subobjects -/
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

@[simp]
theorem initialQuotient_initial (F : Obj (ofExactCategory E) n) (i : Fin (n.len + 1)) :
    initialQuotient (ofExactCategory E) F (interval 0 i (Fin.zero_le _)) = 𝟙 _ := F.obj.map_id _

/-- Cokernel extension agrees with the originally prescribed initial-flag components. -/
@[simp]
theorem extendFlagIso_initial {F G : Obj (ofExactCategory E) n} (e : initialFlag E F ≅ initialFlag
  E G)
    (i : Fin (n.len + 1)) :
    (extendFlagIso E e).hom.app (interval 0 i (Fin.zero_le _)) = e.hom.app i := by
  have h := initialQuotient_flagIsoAt E e (interval 0 i (Fin.zero_le _))
  change F.obj.map (𝟙 _) ≫ _ = e.hom.app i ≫ G.obj.map (𝟙 _) at h
  erw [Functor.map_id, Functor.map_id, Category.id_comp, Category.comp_id] at h
  exact h

/-- Cokernel extension is the unique row isomorphism agreeing on the initial flag. -/
theorem extendFlagIso_unique {F G : Obj (ofExactCategory E) n} (e : initialFlag E F ≅ initialFlag E
  G)
    (f : F.obj ≅ G.obj) (hf : ∀ i, f.hom.app (interval 0 i (Fin.zero_le _)) = e.hom.app i) :
    f = extendFlagIso E e := by
  apply Iso.ext
  apply rowNatTrans_ext_top E (F := F) (G := G)
  rw [extendFlagIso_initial, hf]

/-- Compatible isomorphisms of all initial subobjects are automatically natural:
the map into the top initial object is monic. -/
def initialFlagIsoOfTop {F G : Obj (ofExactCategory E) n}
    (e : ∀ i, (initialFlag E F).obj i ≅ (initialFlag E G).obj i)
    (h : ∀ i, (initialFlag E F).map (homOfLE (Fin.le_last i)) ≫ (e (Fin.last n.len)).hom =
      (e i).hom ≫ (initialFlag E G).map (homOfLE (Fin.le_last i))) :
    initialFlag E F ≅ initialFlag E G :=
  NatIso.ofComponents e (by
    intro i j f
    let : Mono ((initialFlag E G).map (homOfLE (Fin.le_last j))) :=
      E.mono_of_inflation (G.property.cofibration 0 j (Fin.last n.len) (Fin.zero_le _)
        (Fin.le_last j))
    apply (cancel_mono ((initialFlag E G).map (homOfLE (Fin.le_last j)))).1
    rw [Category.assoc, ← h j, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
    exact h i)

/-- Existence of compatible initial-subobject isomorphisms suffices to recover
a whole-row isomorphism, using actual monicity and cokernel universal properties. -/
def rowIsoOfInitialSubobjects {F G : Obj (ofExactCategory E) n}
    (e : ∀ i, (initialFlag E F).obj i ≅ (initialFlag E G).obj i)
    (h : ∀ i, (initialFlag E F).map (homOfLE (Fin.le_last i)) ≫ (e (Fin.last n.len)).hom =
      (e i).hom ≫ (initialFlag E G).map (homOfLE (Fin.le_last i))) : F.obj ≅ G.obj :=
  extendFlagIso E (initialFlagIsoOfTop E e h)

end CategoryTheory.Waldhausen.QuotientRows
