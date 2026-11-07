/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FilteredColimit
public import Colib.Topology.LocalCoefficients.Homology
public import Colib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Final

/-!
Adapted from `Quillen/Topology/LocalCoefficients/FilteredHomology.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the native singular
chain complex, actual transition maps, and coefficient transports.

# Local homology of actual filtered realization colimits

The geometric chain-colimit theorem and exactness of filtered colimits of
modules identify local homology with the colimit of the original stage homology
maps. The comparison retains the pulled-back target coefficient system and the
actual spatial map at every stage. This does not assert a comparison with an
unspecified topological telescope model.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {J : Type u} [SmallCategory J] (F : J ⥤ SSet.{u}) (c : Cocone F)

/-- Actual local homology of each stage with the target system pulled back. -/
def filteredHomologyDiagram (A : System.{u, u} |c.pt|) (n : ℕ) : J ⥤ ModuleCat.{u} ℤ :=
  filteredChainDiagram F c A ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- The cocone consists of the original induced local homology maps. -/
def filteredHomologyCocone (A : System.{u, u} |c.pt|) (n : ℕ) :
    Cocone (filteredHomologyDiagram F c A n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapCocone (filteredChainCocone F c A)

theorem filteredHomologyCocone_ι (A : System.{u, u} |c.pt|) (n : ℕ) (j : J) :
    (filteredHomologyCocone F c A n).ι.app j =
      pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom A n := rfl

/-- Filtered local homology is colimiting for the original stage maps. -/
def filteredHomologyIsColimit [IsFiltered J] (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) (n : ℕ) : IsColimit (filteredHomologyCocone F c A n) := by
  letI := ModuleCat.homologyFunctor_preservesFilteredColimits.{u}
    ℤ J (ComplexShape.down ℕ) n
  exact isColimitOfPreserves (HomologicalComplex.homologyFunctor _ _ n)
    (filteredChainIsColimit F c hc A)

/-- The canonical filtered comparison is an isomorphism of actual homology modules. -/
def filteredHomologyColimitIso [IsFiltered J] (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) (n : ℕ) :
    colimit (filteredHomologyDiagram F c A n) ≅ homology A n :=
  colimit.isoColimitCocone ⟨_, filteredHomologyIsColimit F c hc A n⟩

/-- The canonical homology comparison carries every leg to its original spatial map. -/
@[reassoc]
theorem filteredHomologyColimitIso_ι_hom [IsFiltered J] (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) (n : ℕ) (j : J) :
    colimit.ι (filteredHomologyDiagram F c A n) j ≫
        (filteredHomologyColimitIso F c hc A n).hom =
      pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom A n :=
  colimit.isoColimitCocone_ι_hom _ _

/-- Passing to any final subdiagram preserves the actual local-homology cocone. -/
def filteredHomologyIsColimitWhisker [IsFiltered J] (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) (n : ℕ) {I : Type u} [SmallCategory I]
    (G : I ⥤ J) [G.Final] :
    IsColimit ((filteredHomologyCocone F c A n).whisker G) :=
  (Functor.Final.isColimitWhiskerEquiv G _).symm (filteredHomologyIsColimit F c hc A n)

/-- The canonical homology isomorphism for any cofinal restriction of the original stages. -/
def cofinalFilteredHomologyIso [IsFiltered J] (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) (n : ℕ) {I : Type u} [SmallCategory I]
    (G : I ⥤ J) [G.Final] :
    colimit (G ⋙ filteredHomologyDiagram F c A n) ≅ homology A n :=
  colimit.isoColimitCocone ⟨_, filteredHomologyIsColimitWhisker F c hc A n G⟩

/-- Cofinal restriction still retains the original stage homology arrows. -/
@[reassoc]
theorem cofinalFilteredHomologyIso_ι_hom [IsFiltered J] (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) (n : ℕ) {I : Type u} [SmallCategory I]
    (G : I ⥤ J) [G.Final] (i : I) :
    colimit.ι (G ⋙ filteredHomologyDiagram F c A n) i ≫
        (cofinalFilteredHomologyIso F c hc A n G).hom =
      pushforwardHomologyMap (SSet.toTop.map (c.ι.app (G.obj i))).hom A n :=
  colimit.isoColimitCocone_ι_hom _ _

end FundamentalGroupoid.LocalCoefficients
