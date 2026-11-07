/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.GrothendieckTelescope
public import Colib.Topology.FilteredRealization.PathComponents

/-!
Adapted from `Quillen/Topology/ClassifyingSpace/TelescopeComponents.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining original transition maps.

 # Finite component detection by the original categorical stage transitions -/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v
namespace CategoryTheory.Grothendieck.Telescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (F : ℕ ⥤ Cat.{u, u})

/-- The last-stage fiber, a prefix transition, and the terminal projection
compose to the original sequence transition. -/
theorem last_prefixTransition_projection {n m : ℕ} (h : n ≤ m) :
    CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n (Fin.last n) ⋙ prefixTransition F h ⋙
      CategoryTheory.Grothendieck.FiniteTelescope.projection F m
        = (F.map (homOfLE h)).toFunctor := by
  change CategoryTheory.Grothendieck.FiniteTelescope.inclusion F m ⟨n, Nat.lt_succ_of_le h⟩ ⋙
    CategoryTheory.Grothendieck.FiniteTelescope.projection F m = _
  exact CategoryTheory.Grothendieck.FiniteTelescope.inclusion_projection F m _

/-- Finitely many paths in the telescope are detected by one original stage map. -/
theorem stage_joined_finite_eventually (n : ℕ) {ι : Type v} [Finite ι]
    (a b : ι → ClassifyingSpace (F.obj n))
    (h : ∀ i, Joined (classifyingSpaceMap (Grothendieck.ι F n) (a i))
      (classifyingSpaceMap (Grothendieck.ι F n) (b i))) :
    ∃ (m : ℕ) (hnm : n ≤ m), ∀ i,
      Joined (classifyingSpaceMap (F.map (homOfLE hnm)).toFunctor (a i))
        (classifyingSpaceMap (F.map (homOfLE hnm)).toFunctor (b i)) := by
  let j : PrefixIndex.{u} := AsSmall.up.obj n
  let f := classifyingSpaceMap
    (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n (Fin.last n))
  have hp (i : ι) :
      Joined (classifyingSpaceMap (prefixInclusion F n) (f (a i)))
        (classifyingSpaceMap (prefixInclusion F n) (f (b i))) := by
    change Joined ((f ≫ classifyingSpaceMap (prefixInclusion F n)) (a i))
      ((f ≫ classifyingSpaceMap (prefixInclusion F n)) (b i))
    dsimp only [f]
    rw [fiber_prefix_classifying]
    exact h i
  obtain ⟨k, t, ht⟩ := Topology.FilteredRealization.joined_finite_eventually
    (prefixDiagram F ⋙ nerveFunctor) (nerveFunctor.mapCocone (prefixCocone F))
    (nerveCoconeIsColimit F) j (fun i ↦ f (a i)) (fun i ↦ f (b i)) hp
  let m := AsSmall.down.obj k
  let hnm : n ≤ m := leOfHom (AsSmall.down.map t)
  refine ⟨m, hnm, fun i ↦ ?_⟩
  have hi := (ht i).map
    (classifyingSpaceMap
      (CategoryTheory.Grothendieck.FiniteTelescope.projection F m)).hom.continuous
  change Joined
    ((f ≫ classifyingSpaceMap (prefixTransition F hnm) ≫
      classifyingSpaceMap (CategoryTheory.Grothendieck.FiniteTelescope.projection F m)) (a i))
    ((f ≫ classifyingSpaceMap (prefixTransition F hnm) ≫
      classifyingSpaceMap (CategoryTheory.Grothendieck.FiniteTelescope.projection F m)) (b i)) at hi
  have he : f ≫ classifyingSpaceMap (prefixTransition F hnm) ≫
      classifyingSpaceMap (CategoryTheory.Grothendieck.FiniteTelescope.projection F m) =
      classifyingSpaceMap (F.map (homOfLE hnm)).toFunctor := by
    rw [← classifyingSpaceMap_comp, ← classifyingSpaceMap_comp]
    exact congrArg classifyingSpaceMap (last_prefixTransition_projection F hnm)
  rw [he] at hi
  exact hi

/-- One original transition makes all component relations on a finite support
agree with their component relations in the actual infinite telescope. -/
theorem stage_finite_component_relations_stabilize (n : ℕ)
    (s : Finset (ClassifyingSpace (F.obj n))) :
    ∃ (m : ℕ) (hnm : n ≤ m), ∀ x ∈ s, ∀ y ∈ s,
      Joined (classifyingSpaceMap (F.map (homOfLE hnm)).toFunctor x)
        (classifyingSpaceMap (F.map (homOfLE hnm)).toFunctor y) ↔
      Joined (classifyingSpaceMap (Grothendieck.ι F n) x)
        (classifyingSpaceMap (Grothendieck.ι F n) y) := by
  classical
  let Pairs := {p : s × s // Joined (classifyingSpaceMap (Grothendieck.ι F n) p.1.1)
    (classifyingSpaceMap (Grothendieck.ι F n) p.2.1)}
  obtain ⟨m, hnm, hm⟩ := stage_joined_finite_eventually F n
    (fun p : Pairs ↦ p.1.1.1) (fun p : Pairs ↦ p.1.2.1) (fun p ↦ p.2)
  refine ⟨m, hnm, fun x hx y hy ↦ ⟨fun h ↦ ?_, fun h ↦ hm ⟨(⟨x, hx⟩, ⟨y, hy⟩), h⟩⟩⟩
  exact (show Joined _ _ from ⟨(stageTransitionClassifyingHomotopy F hnm).evalAt x⟩).trans
    ((h.map (classifyingSpaceMap (Grothendieck.ι F m)).hom.continuous).trans
      ⟨((stageTransitionClassifyingHomotopy F hnm).evalAt y).symm⟩)

end CategoryTheory.Grothendieck.Telescope
