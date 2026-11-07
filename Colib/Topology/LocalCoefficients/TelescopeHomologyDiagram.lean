/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.TelescopeHomologyDetection

/-!
Adapted from `Quillen/Topology/LocalCoefficients/TelescopeHomologyDiagram.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining original transition maps.

 # The original transported stage maps form the actual homology colimit diagram -/

@[expose] public section

open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory Limits
universe u
namespace CategoryTheory.Grothendieck.Telescope
open FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (F : ℕ ⥤ Cat.{u, u})
  (A : System.{u, u} (ClassifyingSpace (Model F))) (d : ℕ)

/-- Identity prefixes give the original identity homology map. -/
theorem prefixHomologyTransition_refl (n : ℕ) :
    prefixHomologyTransition F (le_refl n) A d = 𝟙 _ := by
  have h := (filteredHomologyDiagram (prefixDiagram F ⋙ nerveFunctor)
    (nerveFunctor.mapCocone (prefixCocone F)) A d).map_id (AsSmall.up.obj n)
  rw [filteredHomology_prefix_map] at h
  exact h

/-- Prefix composition retains its original spatial maps. -/
theorem prefixHomologyTransition_comp {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    prefixHomologyTransition F (h.trans h') A d =
      prefixHomologyTransition F h A d ≫ prefixHomologyTransition F h' A d := by
  have hc := (filteredHomologyDiagram (prefixDiagram F ⋙ nerveFunctor)
    (nerveFunctor.mapCocone (prefixCocone F)) A d).map_comp
      (AsSmall.up.map (homOfLE h)) (AsSmall.up.map (homOfLE h'))
  simp only [filteredHomology_prefix_map] at hc
  exact hc

/-- The specified original stage transport is the identity on a repeated stage. -/
theorem stageHomologyTransition_refl (n : ℕ) :
    stageHomologyTransition F (le_refl n) A d = 𝟙 _ := by
  let := stageToPrefixHomology_isIso F n A d
  apply (cancel_mono (stageToPrefixHomology F n A d)).mp
  rw [← stageToPrefixHomology_transition, prefixHomologyTransition_refl,
    Category.id_comp, Category.comp_id]

/-- The actual stabilization tracks compose on homology, including coefficient transport. -/
theorem stageHomologyTransition_comp {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    stageHomologyTransition F (h.trans h') A d =
      stageHomologyTransition F h A d ≫ stageHomologyTransition F h' A d := by
  let := stageToPrefixHomology_isIso F k A d
  apply (cancel_mono (stageToPrefixHomology F k A d)).mp
  rw [← stageToPrefixHomology_transition F (h.trans h') A d,
    prefixHomologyTransition_comp F A d h h', ← Category.assoc,
    stageToPrefixHomology_transition F h A d, Category.assoc,
    stageToPrefixHomology_transition F h' A d, ← Category.assoc]

/-- The genuine original-stage local homology diagram. -/
def stageHomologyDiagram : PrefixIndex.{u} ⥤ ModuleCat.{u} ℤ where
  obj n := homology (pullback
    (classifyingSpaceMap (Grothendieck.ι F (AsSmall.down.obj n))).hom A) d
  map a := stageHomologyTransition F (leOfHom (AsSmall.down.map a)) A d
  map_id n := stageHomologyTransition_refl F A d (AsSmall.down.obj n)
  map_comp a b := stageHomologyTransition_comp F A d
    (leOfHom (AsSmall.down.map a)) (leOfHom (AsSmall.down.map b))

/-- The actual last-stage inclusion isomorphisms compare the two genuine diagrams. -/
def stageHomologyDiagramIsoPrefix : stageHomologyDiagram F A d ≅
    filteredHomologyDiagram (prefixDiagram F ⋙ nerveFunctor)
      (nerveFunctor.mapCocone (prefixCocone F)) A d := by
  let (n : ℕ) := stageToPrefixHomology_isIso F n A d
  refine NatIso.ofComponents (fun n ↦ asIso (stageToPrefixHomology F (AsSmall.down.obj n) A d)) ?_
  intro n m a
  change stageHomologyTransition F (leOfHom (AsSmall.down.map a)) A d ≫
    stageToPrefixHomology F (AsSmall.down.obj m) A d = _
  rw [filteredHomology_prefix_map]
  exact (stageToPrefixHomology_transition F _ A d).symm

/-- The original maps from every stage form the actual comparison cocone. -/
def stageHomologyCocone : Cocone (stageHomologyDiagram F A d) where
  pt := homology A d
  ι :=
    { app n := pushforwardHomologyMap
        (classifyingSpaceMap (Grothendieck.ι F (AsSmall.down.obj n))).hom A d
      naturality {n m} a := by
        change stageHomologyTransition F (leOfHom (AsSmall.down.map a)) A d ≫ _ = _ ≫ 𝟙 _
        rw [stageHomologyTransition_to_infinite, Category.comp_id] }

/-- Original-stage homology, with its original transition maps and unit leg, is colimiting. -/
def stageHomologyIsColimit : IsColimit (stageHomologyCocone F A d) := by
  let hc := (IsColimit.precomposeHomEquiv (stageHomologyDiagramIsoPrefix F A d)
    (filteredHomologyCocone (prefixDiagram F ⋙ nerveFunctor)
      (nerveFunctor.mapCocone (prefixCocone F)) A d)).symm
        (filteredHomologyIsColimit _ _ (nerveCoconeIsColimit F) A d)
  apply IsColimit.ofIsoColimit hc
  refine Cocone.ext (Iso.refl _) ?_
  intro n
  change stageToPrefixHomology F (AsSmall.down.obj n) A d ≫
    pushforwardHomologyMap (classifyingSpaceMap (prefixInclusion F (AsSmall.down.obj n))).hom A d ≫
      𝟙 _ = _
  rw [Category.comp_id, stageToPrefixHomology, triangleHomologyMap_to_target]
  rfl

end CategoryTheory.Grothendieck.Telescope
