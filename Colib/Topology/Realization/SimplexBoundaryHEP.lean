/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Analysis.Convex.StdSimplex.BoundaryHomotopyExtension
public import Colib.Topology.Realization.SimplexAttachmentCollar
public import Colib.Topology.Homotopy.Extension

/-! # Homotopy extension from the explicit simplex-boundary retraction

Closed-set gluing on the side-bottom union, followed by the explicit radial
retraction, gives homotopy extension with an arbitrary parameter space.
-/
/-! Implementation provenance: adapted from the matching Quillen file at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The closed gluing, radial retraction, dimension-
zero case and arbitrary parameter spaces are retained. The existing parameterized boundary
inclusion is reused. Its HEP proof uses the categorical cylinder directly, without
a separate coordinate-conversion entry point.
-/
@[expose] public section


noncomputable section

open scoped unitInterval

namespace TopCat
universe u

section ParameterizedBoundary

open CategoryTheory Limits MonoidalCategory stdSimplex
open scoped Topology unitInterval

/-- A parametrized simplex-boundary inclusion has the actual homotopy
extension property, including the zero-dimensional empty-boundary case. -/
theorem homotopyExtensionProperty_simplexBoundary (X : TopCat.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.parameterizedSimplexBoundaryInclusion X n) := by
  intro Z f H hzero
  let H' : C((X × boundary n) × unitInterval, Z) :=
    ⟨fun p ↦ H (p.1, ULift.up p.2), H.hom.continuous.comp
      (continuous_fst.prodMk (continuous_uliftUp.comp continuous_snd))⟩
  have hzero' : ∀ x b, H' ((x, b), 0) = f.hom (x, b.1) := fun x b ↦
    ConcreteCategory.congr_hom hzero (x, b)
  obtain ⟨K, hK₀, hK⟩ := simplexBoundary_homotopy_extension n f.hom H' hzero'
  let K' : (TopCat.of (X × _root_.stdSimplex ℝ (Fin (n + 1)))) ⊗ TopCat.I ⟶ Z :=
    TopCat.ofHom ⟨fun p ↦ K (p.1, p.2.down), K.continuous.comp
      (continuous_fst.prodMk (continuous_uliftDown.comp continuous_snd))⟩
  refine ⟨K', ?_, ?_⟩
  · ext ⟨x, b⟩
    exact hK₀ x b
  · ext ⟨⟨x, b⟩, t⟩
    exact hK x b t.down


/-- Attaching a parametrized topological simplex along its actual boundary
produces a map with HEP. -/
theorem homotopyExtensionProperty_simplexAttachment
    (X : TopCat.{u}) (n : ℕ) {C D : TopCat.{u}}
    {f : TopCat.of (X × boundary n) ⟶ C}
    {g : TopCat.of (X × _root_.stdSimplex ℝ (Fin (n + 1))) ⟶ D}
    {j : C ⟶ D}
    (sq : IsPushout (TopCat.parameterizedSimplexBoundaryInclusion X n) f g j) :
    TopCat.HomotopyExtensionProperty j :=
  TopCat.homotopyExtensionProperty_pushout sq (TopCat.homotopyExtensionProperty_simplexBoundary X
    n)


end ParameterizedBoundary

end TopCat
