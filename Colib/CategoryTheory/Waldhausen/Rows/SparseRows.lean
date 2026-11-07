/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.RecoverSubobjects


/-! # Reconstructing row isomorphisms from a covering family of Q-spans

A family of intervals whose endpoints cover the original ordinal suffices.
Q-naturality to the whole object recovers every initial subobject, and the
cokernel universal properties recover all quotient components.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u w

namespace CategoryTheory.Waldhausen.QuotientRows

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)
variable {n : SimplexCategory}

/-- Isomorphisms of initial subobjects commuting with one fixed top isomorphism
extend to an isomorphism of the whole quotient row. -/
theorem exists_rowIso_of_initial_top {F G : Obj (ofExactCategory E) n}
    (b : (initialFlag E F).obj (Fin.last n.len) ≅ (initialFlag E G).obj (Fin.last n.len))
    (h : ∀ i, ∃ e : (initialFlag E F).obj i ≅ (initialFlag E G).obj i,
      (initialFlag E F).map (homOfLE (Fin.le_last i)) ≫ b.hom =
        e.hom ≫ (initialFlag E G).map (homOfLE (Fin.le_last i))) :
    ∃ e : F.obj ≅ G.obj, ∀ i,
      (initialFlag E F).map (homOfLE (Fin.le_last i)) ≫ b.hom =
        e.hom.app (interval 0 i (Fin.zero_le _)) ≫
          (initialFlag E G).map (homOfLE (Fin.le_last i)) := by
  choose es hes using h
  have htop : es (Fin.last n.len) = b := by
    apply Iso.ext
    have ht := hes (Fin.last n.len)
    change (initialFlag E F).map (𝟙 _) ≫ b.hom =
      (es (Fin.last n.len)).hom ≫ (initialFlag E G).map (𝟙 _) at ht
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using ht.symm
  let e := initialFlagIsoOfTop E es (by intro i; rw [htop]; exact hes i)
  refine ⟨extendFlagIso E e, ?_⟩
  intro i
  rw [extendFlagIso_initial]
  exact hes i

/-- Two upper-endpoint isomorphisms commuting with the fixed top map agree. -/
theorem initialIso_ext_top {F G : Obj (ofExactCategory E) n}
    (i : Fin (n.len + 1)) (e f : (initialFlag E F).obj i ≅ (initialFlag E G).obj i)
    (h : e.hom ≫ (initialFlag E G).map (homOfLE (Fin.le_last i)) =
      f.hom ≫ (initialFlag E G).map (homOfLE (Fin.le_last i))) : e = f := by
  let : Mono ((initialFlag E G).map (homOfLE (Fin.le_last i))) := E.mono_of_inflation
    (G.property.cofibration 0 i (Fin.last n.len) (Fin.zero_le _) (Fin.le_last _))
  exact Iso.ext ((cancel_mono _).mp h)

/-- Sparse Q-data whose interval endpoints cover the ordinal determine a
whole-row isomorphism with exactly the prescribed quotient components. -/
theorem exists_rowIso_of_covering_spans {I : Type w} {F G : Obj (ofExactCategory E) n}
    (p : I → NestedInterval n)
    (cover : ∀ k : Fin (n.len + 1), (∃ i, (p i).left = k) ∨ ∃ i, (p i).right = k)
    (a : ∀ i, F.obj.obj (nestedToInterval (p i)) ≅ G.obj.obj (nestedToInterval (p i)))
    (b : (initialFlag E F).obj (Fin.last n.len) ≅ (initialFlag E G).obj (Fin.last n.len))
    (h : ∀ i, QConstruction.mkHom E.deflation E.inflation (wholeSpan E F (p i)) ≫ (E.qIsoOfIso
      b).hom =
      (E.qIsoOfIso (a i)).hom ≫ QConstruction.mkHom E.deflation E.inflation (wholeSpan E G (p i))) :
    ∃ e : F.obj ≅ G.obj, ∀ i, e.hom.app (nestedToInterval (p i)) = (a i).hom := by
  have hs (i : I) := recover_initial_subobjects E (p i) (a i) b (h i)
  have hi : ∀ k, ∃ e : (initialFlag E F).obj k ≅ (initialFlag E G).obj k,
      (initialFlag E F).map (homOfLE (Fin.le_last k)) ≫ b.hom =
        e.hom ≫ (initialFlag E G).map (homOfLE (Fin.le_last k)) := by
    intro k
    rcases cover k with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact (hs i).2
    · exact (hs i).1
  obtain ⟨e, he⟩ := exists_rowIso_of_initial_top E b hi
  refine ⟨e, ?_⟩
  intro i
  obtain ⟨c, hl, hr⟩ := E.exists_apexIso_of_q_naturality
    (wholeSpan E F (p i)) (wholeSpan E G (p i)) (a i) b (h i)
  dsimp only [wholeSpan] at c hl hr
  have hc : e.app (interval 0 (p i).right (Fin.zero_le _)) = c := by
    apply initialIso_ext_top E (p i).right
    exact (he (p i).right).symm.trans hr
  let q := initialQuotient (ofExactCategory E) F (nestedToInterval (p i))
  let : Epi q := Cofork.IsColimit.epi (initialCokernel E F (nestedToInterval (p i)))
  apply (cancel_epi q).1
  have hn := e.hom.naturality
    (homOfLE (show interval 0 (p i).right (Fin.zero_le _) ≤ nestedToInterval (p i) from
      ⟨Fin.zero_le _, le_rfl⟩))
  change q ≫ e.hom.app (nestedToInterval (p i)) =
    (e.app (interval 0 (p i).right (Fin.zero_le _))).hom ≫
      initialQuotient (ofExactCategory E) G (nestedToInterval (p i)) at hn
  rw [hc] at hn
  exact hn.trans hl.symm

end CategoryTheory.Waldhausen.QuotientRows
