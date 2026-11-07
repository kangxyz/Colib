/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ConnectedComponents
public import Colib.Topology.Realization.Coproduct
public import Colib.Topology.ClassifyingSpace.Connectivity
public import Mathlib.Topology.Connected.TotallyDisconnected

/-! # The original classifying-space inclusions of categorical connected components -/
/-! Implementation source: `Quillen/Topology/ClassifyingSpace/ConnectedComponents.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual component inclusion,
realization coproduct and literal path-component subtype are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial
universe u
namespace CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (C : Type u) [Category.{u} C]

/-- The original nerve inclusions of all categorical components, combined degreewise. -/
def componentNerveMap :
    SSet.simplicialSigma (fun c : CategoryTheory.ConnectedComponents C ↦ nerve c.Component) ⟶
      nerve C where
  app n := ↾fun x ↦ (nerveMap (CategoryTheory.ConnectedComponents.ι x.1)).app n x.2
  naturality n m f := by
    ext ⟨c, s⟩ : 3
    exact ConcreteCategory.congr_hom
      ((nerveMap (CategoryTheory.ConnectedComponents.ι c)).naturality f) s

/-- Every chain lies in the categorical component of its first object. -/
def componentNerveLift {n : ℕ} (s : ComposableArrows C n) :
    ComposableArrows (CategoryTheory.ConnectedComponents.mk (s.obj 0)).Component n :=
  (CategoryTheory.ConnectedComponents.mk (s.obj 0)).objectProperty.lift s (fun i ↦ by
    apply Quotient.sound'
    exact Relation.ReflTransGen.single (Or.inr ⟨s.map (homOfLE (Fin.zero_le i))⟩))

/-- The original component nerve map is onto in every degree. -/
theorem componentNerveMap_surjective (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((componentNerveMap C).app n) := by
  intro s
  exact ⟨⟨CategoryTheory.ConnectedComponents.mk (s.obj 0), componentNerveLift C s⟩, rfl⟩

/-- A chain in a fixed categorical component is determined by its underlying chain. -/
theorem componentNerveMap_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((componentNerveMap C).app n) := by
  rintro ⟨c, s⟩ ⟨d, t⟩ h
  have h0 := congrArg (fun s : ComposableArrows C n.unop.len ↦ s.obj 0) h
  have hcd : c = d := by
    rw [← (s.obj 0).property, ← (t.obj 0).property]
    exact congrArg CategoryTheory.ConnectedComponents.mk h0
  subst d
  congr 1
  refine CategoryTheory.Functor.ext (F := s) (G := t)
    (fun i ↦ ObjectProperty.FullSubcategory.ext
      (congrArg (fun s : ComposableArrows C n.unop.len ↦ s.obj i) h)) ?_
  intro i j f
  apply (CategoryTheory.ConnectedComponents.ι c).map_injective
  have hh := Functor.congr_hom h f
  simp only [Functor.map_comp, eqToHom_map]
  exact hh

/-- The nerve is the genuine simplicial coproduct of its categorical components. -/
instance componentNerveMap_isIso : IsIso (componentNerveMap C) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  exact (isIso_iff_bijective _).mpr
    ⟨componentNerveMap_injective C n, componentNerveMap_surjective C n⟩

/-- The classifying space is homeomorphic to the disjoint union of its actual components. -/
def classifyingSpaceComponentSigmaHomeomorph :
    (Σ c : CategoryTheory.ConnectedComponents C, ClassifyingSpace c.Component) ≃ₜ
      ClassifyingSpace C :=
  (TopCat.homeoOfIso (SSet.realizationSigmaIso
    (fun c : CategoryTheory.ConnectedComponents C ↦ nerve c.Component))).symm.trans
      (TopCat.homeoOfIso (SSet.toTop.mapIso (asIso (componentNerveMap C))))

/-- On each summand, the homeomorphism is exactly the original inclusion functor. -/
@[simp]
theorem classifyingSpaceComponentSigmaHomeomorph_apply
    (c : CategoryTheory.ConnectedComponents C) (x : ClassifyingSpace c.Component) :
    classifyingSpaceComponentSigmaHomeomorph C ⟨c, x⟩ =
      classifyingSpaceMap (CategoryTheory.ConnectedComponents.ι c) x := by
  change SSet.toTop.map (componentNerveMap C)
    ((SSet.realizationSigmaIso _).inv ⟨c, x⟩) = _
  have hinv : (SSet.realizationSigmaIso
      (fun c : ConnectedComponents C => nerve c.Component)).inv ⟨c, x⟩ =
        SSet.toTop.map (SSet.simplicialSigmaι
          (fun c : ConnectedComponents C => nerve c.Component) c) x := by
    have hι : (SSet.realizationSigmaIso
        (fun c : ConnectedComponents C => nerve c.Component)).hom
          (SSet.toTop.map (SSet.simplicialSigmaι
            (fun c : ConnectedComponents C => nerve c.Component) c) x) = ⟨c, x⟩ :=
      ConcreteCategory.congr_hom (SSet.realizationSigmaIso_ι
        (fun c : ConnectedComponents C => nerve c.Component) c) x
    rw [← hι]
    exact ConcreteCategory.congr_hom (SSet.realizationSigmaIso _).hom_inv_id _
  rw [hinv]
  change (SSet.toTop.map (SSet.simplicialSigmaι _ c) ≫
    SSet.toTop.map (componentNerveMap C)) x = _
  rw [← Functor.map_comp]
  rfl

/-- A path in a topological disjoint union cannot change its component index. -/
theorem classifyingSpace_sigma_joined_index
    (x y : Σ c : CategoryTheory.ConnectedComponents C, ClassifyingSpace c.Component)
    (h : Joined x y) : x.1 = y.1 := by
  let : TopologicalSpace (CategoryTheory.ConnectedComponents C) := ⊥
  let : DiscreteTopology (CategoryTheory.ConnectedComponents C) := ⟨rfl⟩
  let p := h.somePath
  have hc : Continuous (fun t : unitInterval ↦ (p t).1) :=
    (continuous_sigma (fun _ ↦ continuous_const)).comp p.continuous
  have hs := (isPreconnected_range hc).subsingleton
  have he := hs (show (p 0).1 ∈ Set.range (fun t : unitInterval ↦ (p t).1) from ⟨0, rfl⟩)
    (show (p 1).1 ∈ Set.range (fun t : unitInterval ↦ (p t).1) from ⟨1, rfl⟩)
  simpa only [Path.source, Path.target] using he

/-- The range of an original component inclusion is precisely its topological path component. -/
theorem classifyingSpace_component_range (b : C) :
    Set.range (classifyingSpaceMap
      (CategoryTheory.ConnectedComponents.ι (CategoryTheory.ConnectedComponents.mk b))) =
        pathComponent (classifyingSpacePoint b) := by
  let c := CategoryTheory.ConnectedComponents.mk b
  let v : c.Component := ⟨b, rfl⟩
  let e := classifyingSpaceComponentSigmaHomeomorph C
  have hb : e ⟨c, classifyingSpacePoint v⟩ = classifyingSpacePoint b := by simp [e, v]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have h := (PathConnectedSpace.joined (classifyingSpacePoint v) y).map
      (classifyingSpaceMap (CategoryTheory.ConnectedComponents.ι c)).hom.continuous
    change Joined (classifyingSpacePoint b) _
    simpa only [classifyingSpaceMap_point, c, v, ObjectProperty.ι_obj] using h
  · intro hx
    have h : Joined (e.symm (classifyingSpacePoint b)) (e.symm x) := hx.map e.symm.continuous
    rw [← hb, e.symm_apply_apply] at h
    have hi := classifyingSpace_sigma_joined_index C _ _ h
    rcases hz : e.symm x with ⟨d, y⟩
    rw [hz] at hi
    dsimp only at hi
    subst d
    refine ⟨y, ?_⟩
    have he := congrArg e hz
    rw [e.apply_symm_apply] at he
    simpa only [e, classifyingSpaceComponentSigmaHomeomorph_apply] using he.symm

/-- Each original classifying-space component inclusion is a topological embedding. -/
theorem classifyingSpace_component_isEmbedding
    (c : CategoryTheory.ConnectedComponents C) :
    Topology.IsEmbedding (classifyingSpaceMap (CategoryTheory.ConnectedComponents.ι c)) := by
  have h := (classifyingSpaceComponentSigmaHomeomorph C).isEmbedding.comp
    (Topology.IsEmbedding.sigmaMk (i := c))
  simpa only [Function.comp_def, classifyingSpaceComponentSigmaHomeomorph_apply] using h

/-- The categorical component realizes to its actual path-component subspace,
with the original inclusion as forward map. -/
def classifyingSpaceComponentHomeomorph (b : C) :
    ClassifyingSpace (CategoryTheory.ConnectedComponents.mk b).Component ≃ₜ
      pathComponent (classifyingSpacePoint b) :=
  (classifyingSpace_component_isEmbedding C _).toHomeomorph.trans
    (Homeomorph.setCongr (classifyingSpace_component_range C b))

/-- Forgetting the component restriction recovers the original functorial map. -/
@[simp]
theorem classifyingSpaceComponentHomeomorph_val (b : C)
    (x : ClassifyingSpace (CategoryTheory.ConnectedComponents.mk b).Component) :
    (classifyingSpaceComponentHomeomorph C b x).val =
      classifyingSpaceMap (CategoryTheory.ConnectedComponents.ι _) x := rfl

end CategoryTheory
