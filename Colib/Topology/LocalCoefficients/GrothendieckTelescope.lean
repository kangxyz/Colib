/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.GrothendieckTelescope
public import Colib.Topology.LocalCoefficients.FilteredHomology

/-!
Adapted from `Quillen/Topology/LocalCoefficients/GrothendieckTelescope.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original categorical maps.


# Actual local homology of the infinite Grothendieck model

The original finite-prefix maps give the local-homology colimit comparison.
All coefficients are pulled back from the infinite model and the canonical
isomorphism retains every original spatial arrow.
-/

@[expose] public section

open FundamentalGroupoid.LocalCoefficients


open CategoryTheory Limits
noncomputable section
universe u
namespace CategoryTheory.Grothendieck.Telescope
variable (F : ℕ ⥤ Cat.{u, u})

open FundamentalGroupoid.LocalCoefficients

/-- Actual finite-prefix local homology with the infinite target system pulled back. -/
def localHomologyDiagram (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ) :
    PrefixIndex.{u} ⥤ ModuleCat.{u} ℤ :=
  filteredHomologyDiagram (prefixDiagram F ⋙ nerveFunctor)
    (nerveFunctor.mapCocone (prefixCocone F)) A k

/-- The canonical comparison is an isomorphism for every target local system. -/
def localHomologyColimitIso (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ) :
    colimit (localHomologyDiagram F A k) ≅ homology A k :=
  filteredHomologyColimitIso (prefixDiagram F ⋙ nerveFunctor)
    (nerveFunctor.mapCocone (prefixCocone F)) (nerveCoconeIsColimit F) A k

@[reassoc]
theorem localHomologyColimitIso_ι_hom
    (A : System.{u, u} (ClassifyingSpace (Model F))) (k n : ℕ) :
    colimit.ι (localHomologyDiagram F A k) (AsSmall.up.obj n) ≫
        (localHomologyColimitIso F A k).hom =
      pushforwardHomologyMap (classifyingSpaceMap (prefixInclusion F n)).hom A k :=
  filteredHomologyColimitIso_ι_hom (prefixDiagram F ⋙ nerveFunctor)
    (nerveFunctor.mapCocone (prefixCocone F)) (nerveCoconeIsColimit F) A k
    (AsSmall.up.obj n)

end CategoryTheory.Grothendieck.Telescope
