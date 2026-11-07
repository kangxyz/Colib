/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.TwoSidedBar.Evaluation
public import Colib.Topology.ClassifyingSpace.Contraction

/-!
# Resolution categories and columns of the two-sided bar

The resolution category has an evaluation functor, section and contraction. Its classifying
    space identifies the corresponding bar column.


Implementation provenance:
`Quillen/Topology/Realization/TwoSidedBar/Resolution.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA



noncomputable section
open Topology TopCat SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u

namespace SSet.TwoSidedBar
variable (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (q : SimplexCategoryᵒᵖ)

/-- An actual simplex with an arrow to the evaluation ordinal. -/
structure Resolution where
  /-- A universe-raised opposite simplex indexing an outer stage of the bisimplicial diagram. -/
  index : Index.{u}
  /-- A simplex in inner degree `q` at the chosen outer stage. -/
  value : (H.obj (indexProjection.obj index)).obj q
  /-- The outer restriction from the chosen index to `q`, used to evaluate the stage simplex in
  diagonal degree `q`. -/
  arrow : indexProjection.obj index ⟶ q

namespace Resolution
variable {H q}

@[ext] theorem ext {a b : Resolution H q} (h : a.index = b.index)
    (hv : HEq a.value b.value) (ha : HEq a.arrow b.arrow) : a = b := by
  cases a; cases b; cases h; cases hv; cases ha; rfl

/-- A genuine transport map respecting both the simplex and the terminal arrow. -/
structure Hom (a b : Resolution H q) where
  /-- The arrow between outer indices underlying a resolution morphism. -/
  map : a.index ⟶ b.index
  /-- Transport along the outer-index arrow carries the source simplex to the target simplex. -/
  value : (H.map (indexProjection.map map)).app q a.value = b.value
  /-- The index arrow commutes with the two specified restrictions to `q`. -/
  arrow : indexProjection.map map ≫ b.arrow = a.arrow

@[ext] theorem Hom.ext {a b : Resolution H q} {f g : Hom a b} (h : f.map = g.map) : f = g := by
  cases f; cases g; cases h; rfl

instance : SmallCategory (Resolution H q) where
  Hom := Hom
  id a := {
    map := 𝟙 a.index
    value := by
      change (H.map (𝟙 _)).app q a.value = a.value
      rw [H.map_id]
      rfl
    arrow := by
      change (𝟙 _) ≫ a.arrow = a.arrow
      exact Category.id_comp _ }
  comp f g := {
    map := f.map ≫ g.map
    value := by
      simp only [Functor.map_comp, NatTrans.comp_app, types_comp_apply]
      rw [f.value, g.value]
    arrow := by rw [Functor.map_comp, Category.assoc, g.arrow, f.arrow] }
  id_comp f := by apply Hom.ext; exact Category.id_comp _
  comp_id f := by apply Hom.ext; exact Category.comp_id _
  assoc f g h := by apply Hom.ext; exact Category.assoc _ _ _

variable (H q)

/-- Forgetting the coefficient and augmentation arrow. -/
def forget : Resolution H q ⥤ Index.{u} where
  obj a := a.index
  map f := f.map

/-- Evaluation lands in the discrete set of original diagonal simplices. -/
def evaluate : Resolution H q ⥤ Discrete ((H.obj q).obj q) where
  obj a := ⟨(H.map a.arrow).app q a.value⟩
  map {a b} f := Discrete.eqToHom (by
    change (H.map a.arrow).app q a.value = (H.map b.arrow).app q b.value
    rw [← f.arrow, H.map_comp]
    change (H.map b.arrow).app q ((H.map (indexProjection.map f.map)).app q a.value) = _
    rw [f.value])

/-- The actual terminal object in each evaluation fiber. -/
def sectionFunctor : Discrete ((H.obj q).obj q) ⥤ Resolution H q where
  obj a := ⟨AsSmall.up.obj q, a.as, 𝟙 q⟩
  map {a b} f := {
    map := 𝟙 _
    value := by
      change (H.map (𝟙 q)).app q a.as = b.as
      rw [H.map_id]
      exact Discrete.eq_of_hom f
    arrow := by
      change (𝟙 q) ≫ (𝟙 q) = 𝟙 q
      exact Category.id_comp _ }
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by
    apply Hom.ext
    change (𝟙 (AsSmall.up.obj q)) = 𝟙 _ ≫ 𝟙 _
    simp

/-- The literal augmentation arrow contracts each evaluation fiber to its
terminal object, with no choice of paths or inverse families. -/
def contraction : 𝟭 (Resolution H q) ⟶ evaluate H q ⋙ sectionFunctor H q where
  app a := {
    map := AsSmall.up.map a.arrow
    value := rfl
    arrow := Category.comp_id _ }
  naturality a b f := by
    apply Hom.ext
    change f.map ≫ AsSmall.up.map b.arrow = AsSmall.up.map a.arrow ≫ 𝟙 _
    apply ULift.ext
    change indexProjection.map f.map ≫ b.arrow = a.arrow ≫ 𝟙 q
    simpa using f.arrow

/-- Evaluation followed by the terminal section is exactly identity on the
discrete original simplex set. -/
def sectionEvaluationIso : sectionFunctor H q ⋙ evaluate H q ≅ 𝟭 _ :=
  NatIso.ofComponents (fun a ↦ eqToIso (by
    apply Discrete.ext
    change (H.map (𝟙 q)).app q a.as = a.as
    rw [H.map_id]
    rfl))

end Resolution
end SSet.TwoSidedBar

end

noncomputable section
open Topology TopCat SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u

namespace SSet.TwoSidedBar
open TheoremA
variable (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (q : SimplexCategoryᵒᵖ)

@[simp] theorem Resolution.eqToHom_map {a b : Resolution H q} (h : a = b) :
    (eqToHom h : a ⟶ b).map = eqToHom (congrArg Resolution.index h) := by
  cases h
  rfl

instance Resolution.forget_faithful : (Resolution.forget H q).Faithful where
  map_injective h := Resolution.Hom.ext h

/-- Reconstruct the full augmented coefficient chain from the literal bar
coordinates. -/
def resolutionChain {p : SimplexCategoryᵒᵖ} (z : ((bar H).obj p).obj q) :
    ComposableArrows (Resolution H q) p.unop.len where
  obj i := {
    index := z.1.obj i
    value := (H.map (indexProjection.map (z.1.map (homOfLE (Fin.zero_le i))))).app q z.2.1
    arrow := indexProjection.map (z.1.map (homOfLE (Fin.le_last i))) ≫ z.2.2.down.op }
  map {i j} f := {
    map := z.1.map f
    value := by
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← H.map_comp,
        ← indexProjection.map_comp, ← z.1.map_comp]
      rfl
    arrow := by
      rw [← Category.assoc, ← indexProjection.map_comp, ← z.1.map_comp]
      rfl }
  map_id i := by apply Resolution.Hom.ext; exact z.1.map_id i
  map_comp f g := by apply Resolution.Hom.ext; exact z.1.map_comp f g

/-- Recover the original indexing chain, first coefficient, and final arrow. -/
def resolutionCoordinates {p : SimplexCategoryᵒᵖ}
    (F : ComposableArrows (Resolution H q) p.unop.len) : ((bar H).obj p).obj q :=
  ⟨F ⋙ Resolution.forget H q, (F.obj 0).value,
    ULift.up (F.obj (Fin.last p.unop.len)).arrow.unop⟩

/-- Recovering the bar coordinates after reconstruction changes no coordinate. -/
theorem resolutionCoordinates_chain {p : SimplexCategoryᵒᵖ}
    (z : ((bar H).obj p).obj q) :
    resolutionCoordinates H q (resolutionChain H q z) = z := by
  cases z with
  | mk s z =>
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply Prod.ext
    · change (H.map (indexProjection.map (s.map (𝟙 (0 : Fin (p.unop.len + 1)))))).app q z.1 = z.1
      rw [s.map_id, indexProjection.map_id, H.map_id]
      rfl
    · apply ULift.ext
      change (indexProjection.map (s.map (𝟙 (Fin.last p.unop.len))) ≫ z.2.down.op).unop = z.2.down
      rw [s.map_id, indexProjection.map_id, Category.id_comp]
      rfl

/-- Every resolution chain is recovered, using its genuine coefficient and
augmentation compatibility equations. -/
theorem resolutionChain_coordinates {p : SimplexCategoryᵒᵖ}
    (F : ComposableArrows (Resolution H q) p.unop.len) :
    resolutionChain H q (resolutionCoordinates H q F) = F := by
  have hobj (i : Fin (p.unop.len + 1)) :
      (resolutionChain H q (resolutionCoordinates H q F)).obj i = F.obj i := by
    refine Resolution.ext (by rfl) ?_ ?_
    · exact heq_of_eq (F.map (homOfLE (Fin.zero_le i))).value
    · exact heq_of_eq (F.map (homOfLE (Fin.le_last i))).arrow
  refine CategoryTheory.Functor.ext hobj ?_
  intro i j f
  apply Resolution.Hom.ext
  change (F.map f).map = (eqToHom (hobj i)).map ≫ (F.map f).map ≫
    (eqToHom (hobj j).symm).map
  simp only [Resolution.eqToHom_map, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The literal coordinate equivalence in each outer degree. -/
def columnEquiv (p : SimplexCategoryᵒᵖ) :
    (nerve (Resolution H q)).obj p ≃ ((bar H).flip.obj q).obj p where
  toFun := resolutionCoordinates H q
  invFun := resolutionChain H q
  left_inv := resolutionChain_coordinates H q
  right_inv := resolutionCoordinates_chain H q

/-- This coordinate identification commutes with every outer ordinal map. -/
def columnIso : nerve (Resolution H q) ≅ (bar H).flip.obj q :=
  NatIso.ofComponents (fun p ↦ (columnEquiv H q p).toIso) (by
    intro p r α
    ext F : 3
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply Prod.ext
    · exact (F.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0)))).value.symm
    · apply ULift.ext
      exact congrArg Quiver.Hom.unop
        (F.map (homOfLE (Fin.le_last (α.unop.toOrderHom (Fin.last r.unop.len))))).arrow.symm)

end SSet.TwoSidedBar

end
