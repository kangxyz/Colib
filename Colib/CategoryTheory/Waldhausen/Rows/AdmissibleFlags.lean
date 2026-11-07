/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.HasCokernel
public import Colib.CategoryTheory.Limits.Shapes.CompositeCokernel
public import Colib.CategoryTheory.Waldhausen.Rows.Exact


/-! # Completing admissible flags by their actual cokernels

An admissible finite flag has a canonical quotient diagram, formed from
actual categorical cokernels. Every required S-pushout is proved by its
universal property. The completion does not assume a pre-existing S-row.
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

variable (A : Fin (n.len + 1) ⥤ C)
variable (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))


/-- The canonical quotient diagram of an arbitrary admissible flag. -/
def quotientDiagram : Interval n ⥤ C := by
  letI {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
    E.hasCokernel_of_inflation (A.map f) (hA f)
  exact {
    obj p := cokernel (A.map (homOfLE p.2))
    map {p q} f := cokernel.map (A.map (homOfLE p.2)) (A.map (homOfLE q.2))
      (A.map (homOfLE (leOfHom f).1)) (A.map (homOfLE (leOfHom f).2)) (by
        simp only [← A.map_comp]
        congr 1)
    map_id p := by
      apply (cancel_epi (cokernel.π (A.map (homOfLE p.2)))).1
      simp only [cokernel.map, cokernel.π_desc, Category.comp_id]
      change A.map (𝟙 _) ≫ _ = _
      rw [A.map_id, Category.id_comp]
    map_comp {p q r} f g := by
      apply (cancel_epi (cokernel.π (A.map (homOfLE p.2)))).1
      simp only [cokernel.map, cokernel.π_desc, cokernel.π_desc_assoc, Category.assoc]
      rw [← Category.assoc, ← A.map_comp]
      rfl
  }
/-- The specified quotient map onto an interval in the completed flag. -/
def flagQuotient (p : Interval n) : A.obj p.1.2 ⟶ (quotientDiagram E A hA).obj p :=
  by
    letI {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
      E.hasCokernel_of_inflation (A.map f) (hA f)
    exact cokernel.π (A.map (homOfLE p.2))

instance flagQuotient_epi (p : Interval n) : Epi (flagQuotient E A hA p) := by
  let {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
    E.hasCokernel_of_inflation (A.map f) (hA f)
  change Epi (cokernel.π (A.map (homOfLE p.2)))
  infer_instance

@[reassoc (attr := simp)]
theorem flagQuotient_naturality {p q : Interval n} (f : p ⟶ q) :
    flagQuotient E A hA p ≫ (quotientDiagram E A hA).map f =
      A.map (homOfLE (leOfHom f).2) ≫ flagQuotient E A hA q :=
  by
    let {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
      E.hasCokernel_of_inflation (A.map f) (hA f)
    exact cokernel.π_desc _ _ _

/-- Completion has zero diagonal because the diagonal cokernels are those of identities. -/
theorem quotientDiagram_zero (i : Fin (n.len + 1)) :
    IsZero ((quotientDiagram E A hA).obj (interval i i le_rfl)) := by
  let {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
    E.hasCokernel_of_inflation (A.map f) (hA f)
  change IsZero (cokernel (A.map (𝟙 i)))
  apply isZero_cokernel_of_epi

/-- Every horizontal map in the completed row is a cobase change of an
admissible flag inclusion, hence is an inflation. -/
theorem quotientDiagram_inflation (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    E.inflation ((quotientDiagram E A hA).map
      (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl, hjk⟩))) := by
  let {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
    E.hasCokernel_of_inflation (A.map f) (hA f)
  have sq := quotient_isPushout (A.map (homOfLE hij)) (A.map (homOfLE hjk))
    (A.map (homOfLE (hij.trans hjk))) (by rw [← A.map_comp]; rfl)
  have hi := E.inflation.of_isPushout sq.flip (hA (homOfLE hjk))
  change E.inflation (cokernel.map (A.map (homOfLE hij))
    (A.map (homOfLE (hij.trans hjk))) (A.map (𝟙 i)) (A.map (homOfLE hjk)) (by
      simp only [← A.map_comp]; congr 1))
  simpa only [A.map_id, quotientInclusion] using hi

/-- The completed row's quotient squares are genuine pushouts. -/
theorem quotientDiagram_pushout (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout
      ((quotientDiagram E A hA).map (homOfLE (show interval i j hij ≤ interval i k (hij.trans
        hjk) from ⟨le_rfl, hjk⟩)))
      ((quotientDiagram E A hA).map (homOfLE (show interval i j hij ≤ interval j j le_rfl from
        ⟨hij, le_rfl⟩)))
      ((quotientDiagram E A hA).map (homOfLE (show interval i k (hij.trans hjk) ≤ interval j k
        hjk from ⟨hij, le_rfl⟩)))
      ((quotientDiagram E A hA).map (homOfLE (show interval j j le_rfl ≤ interval j k hjk from
        ⟨le_rfl, hjk⟩))) := by
  let {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
    E.hasCokernel_of_inflation (A.map f) (hA f)
  have hh := quotientIsCokernel (A.map (homOfLE hij)) (A.map (homOfLE hjk))
    (A.map (homOfLE (hij.trans hjk))) (by rw [← A.map_comp]; rfl)
  have hs := CategoryTheory.Limits.isPushout_of_isColimit_cokernel _ hh (quotientDiagram_zero E A hA
    j)
    ((quotientDiagram E A hA).map (homOfLE (show interval i j hij ≤ interval j j le_rfl from
      ⟨hij, le_rfl⟩)))
    ((quotientDiagram E A hA).map (homOfLE (show interval j j le_rfl ≤ interval j k hjk from
      ⟨le_rfl, hjk⟩)))
  change IsPushout
    (cokernel.map (A.map (homOfLE hij)) (A.map (homOfLE (hij.trans hjk)))
      (A.map (𝟙 i)) (A.map (homOfLE hjk)) (by simp only [← A.map_comp]; congr 1)) _
    (cokernel.map (A.map (homOfLE (hij.trans hjk))) (A.map (homOfLE hjk))
      (A.map (homOfLE hij)) (A.map (𝟙 k)) (by simp only [← A.map_comp]; congr 1)) _
  simpa only [A.map_id, quotientInclusion, quotientProjection] using hs

/-- The actual exact S-row obtained by completing an admissible finite flag. -/
def flagRow : Obj (ofExactCategory E) n :=
  ⟨quotientDiagram E A hA, {
    zero := quotientDiagram_zero E A hA
    cofibration := quotientDiagram_inflation E A hA
    quotient := quotientDiagram_pushout E A hA }⟩

end CategoryTheory.Waldhausen.QuotientRows
