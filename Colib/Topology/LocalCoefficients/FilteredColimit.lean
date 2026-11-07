/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FilteredChains
public import Colib.Topology.LocalCoefficients.TriangleChains
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Colib.CategoryTheory.Limits.ReindexedCoproduct
/-!
Adapted from `Quillen/Topology/LocalCoefficients/FilteredColimit.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the native singular
chain complex, actual transition maps, and coefficient transports.

# The actual filtered colimit of local-coefficient singular chains

For a filtered simplicial-set colimit, compact factorization and eventual
compact equality identify the singular simplex sets with their stage colimits.
Dependent coproduct descent then identifies every chain module. The transitions
are genuine spatial chain maps with their necessary coefficient identifications,
and the cocone legs are the original spatial pushforwards. Degreewise colimit
universal properties assemble to the actual chain-complex colimit isomorphism.
-/

@[expose] public section

open CategoryTheory Limits
open scoped Simplicial
noncomputable section
universe u
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {J : Type u} [SmallCategory J] (F : J ⥤ SSet.{u}) (c : Cocone F)

/-- The diagram of actual singular simplices in the stage realizations. -/
def singularSimplexDiagram (n : SimplexCategory) : J ⥤ Type u where
  obj j := SingularSimplex |F.obj j| n
  map a := ↾fun σ ↦ (SSet.toTop.map (F.map a)).hom.comp σ
  map_id j := by
    apply ConcreteCategory.hom_ext
    intro σ
    change (SSet.toTop.map (F.map (𝟙 j))).hom.comp σ = σ
    rw [F.map_id, SSet.toTop.map_id]
    rfl
  map_comp {j k l} a b := by
    apply ConcreteCategory.hom_ext
    intro σ
    change (SSet.toTop.map (F.map (a ≫ b))).hom.comp σ =
      (SSet.toTop.map (F.map b)).hom.comp ((SSet.toTop.map (F.map a)).hom.comp σ)
    rw [F.map_comp, Functor.map_comp]
    rfl

/-- The original realization maps on singular simplices. -/
def singularSimplexCocone (n : SimplexCategory) : Cocone (singularSimplexDiagram F n) where
  pt := SingularSimplex |c.pt| n
  ι :=
    { app j := ↾fun σ ↦ (SSet.toTop.map (c.ι.app j)).hom.comp σ
      naturality {j k} a := by
        apply ConcreteCategory.hom_ext
        intro σ
        change (SSet.toTop.map (c.ι.app k)).hom.comp
          ((SSet.toTop.map (F.map a)).hom.comp σ) =
            (SSet.toTop.map (c.ι.app j)).hom.comp σ
        change (SSet.toTop.map (F.map a) ≫ SSet.toTop.map (c.ι.app k)).hom.comp σ = _
        rw [← Functor.map_comp, c.w] }

/-- Compact simplex factorization and eventual equality give the actual type colimit. -/
def singularSimplexIsColimit [IsFiltered J] (hc : IsColimit c) (n : SimplexCategory) :
    IsColimit (singularSimplexCocone F c n) :=
  Types.FilteredColimit.isColimitOf' _ _
    (fun σ ↦ by
      obtain ⟨j, τ, hτ⟩ := filtered_simplex_factors F c hc n σ
      exact ⟨j, τ, hτ.symm⟩)
    (fun j σ τ h ↦ filtered_simplex_eq_eventually F c hc n j σ τ h)

/-- The degreewise local-chain diagram with coefficient equality transports. -/
def filteredModuleDiagram (A : System.{u, u} |c.pt|) (n : SimplexCategory) :
    J ⥤ ModuleCat.{u} ℤ :=
  ReindexedCoproduct.diagram (singularSimplexDiagram F n) (singularSimplexCocone F c n)
    (simplexFiber A)

/-- The original stage pushforwards form the degreewise cocone. -/
def filteredModuleCocone (A : System.{u, u} |c.pt|) (n : SimplexCategory) :
    Cocone (filteredModuleDiagram F c A n) :=
  ReindexedCoproduct.cocone (singularSimplexDiagram F n) (singularSimplexCocone F c n)
    (simplexFiber A)

/-- The actual local-chain module is the colimit of its stage modules. -/
def filteredModuleIsColimit [IsFiltered J] (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) (n : SimplexCategory) :
    IsColimit (filteredModuleCocone F c A n) :=
  ReindexedCoproduct.isColimit (singularSimplexDiagram F n) (singularSimplexCocone F c n)
    (simplexFiber A) (singularSimplexIsColimit F c hc n)

theorem filteredModuleCocone_ι (A : System.{u, u} |c.pt|) (n : SimplexCategory) (j : J) :
    (filteredModuleCocone F c A n).ι.app j =
      pushforwardModuleMap (SSet.toTop.map (c.ι.app j)).hom A n := rfl


theorem stage_triangle (j k : J) (a : j ⟶ k) :
    (SSet.toTop.map (c.ι.app j)).hom =
      (SSet.toTop.map (c.ι.app k)).hom.comp (SSet.toTop.map (F.map a)).hom := by
  change (SSet.toTop.map (c.ι.app j)).hom =
    (SSet.toTop.map (F.map a) ≫ SSet.toTop.map (c.ι.app k)).hom
  rw [← Functor.map_comp, c.w]

/-- The actual stage simplicial map with coefficients pulled back from the target. -/
def stageSimplicialMap (A : System.{u, u} |c.pt|) {j k : J} (a : j ⟶ k) :=
  triangleSimplicialMap (SSet.toTop.map (F.map a)).hom
    (SSet.toTop.map (c.ι.app j)).hom (SSet.toTop.map (c.ι.app k)).hom
    (stage_triangle F c j k a) A

theorem stageSimplicialMap_app (A : System.{u, u} |c.pt|)
    {j k : J} (a : j ⟶ k) (n : SimplexCategory) :
    (stageSimplicialMap F c A a).app (Opposite.op n) =
      (filteredModuleDiagram F c A n).map a := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion (pullback (SSet.toTop.map (c.ι.app j)).hom A) σ ≫
      (stageSimplicialMap F c A a).app (Opposite.op n) = _
  rw [stageSimplicialMap, triangleSimplicialMap_inclusion]
  simp only [filteredModuleDiagram, ReindexedCoproduct.diagram, Sigma.ι_desc]
  rfl


/-- The actual spatial chain map along a transition, retaining coefficient conversion. -/
def stageChainMap (A : System.{u, u} |c.pt|) {j k : J} (a : j ⟶ k) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (stageSimplicialMap F c A a)

theorem stageChainMap_f (A : System.{u, u} |c.pt|) {j k : J} (a : j ⟶ k) (n : ℕ) :
    (stageChainMap F c A a).f n = (filteredModuleDiagram F c A ⦋n⦌).map a :=
  stageSimplicialMap_app F c A a ⦋n⦌

/-- The genuine diagram of singular chain complexes with pulled-back local coefficients. -/
def filteredChainDiagram (A : System.{u, u} |c.pt|) :
    J ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ where
  obj j := singularChainComplex (pullback (SSet.toTop.map (c.ι.app j)).hom A)
  map a := stageChainMap F c A a
  map_id j := by
    ext n : 1
    rw [stageChainMap_f]
    exact (filteredModuleDiagram F c A ⦋n⦌).map_id j
  map_comp a b := by
    ext n : 1
    change (stageChainMap F c A (a ≫ b)).f n =
      (stageChainMap F c A a).f n ≫ (stageChainMap F c A b).f n
    simp only [stageChainMap_f, Functor.map_comp]

/-- The original stage pushforward chain maps form the colimit comparison cocone. -/
def filteredChainCocone (A : System.{u, u} |c.pt|) :
    Cocone (filteredChainDiagram F c A) where
  pt := singularChainComplex A
  ι :=
    { app j := pushforwardChainMap (SSet.toTop.map (c.ι.app j)).hom A
      naturality {j k} a := by
        ext n : 1
        change (stageChainMap F c A a).f n ≫
          pushforwardModuleMap (SSet.toTop.map (c.ι.app k)).hom A ⦋n⦌ =
            pushforwardModuleMap (SSet.toTop.map (c.ι.app j)).hom A ⦋n⦌ ≫ 𝟙 _
        rw [stageChainMap_f, Category.comp_id]
        exact (filteredModuleCocone F c A ⦋n⦌).w a }

/-- Degree evaluation agrees with the dependent-coproduct module diagram. -/
def filteredChainEvalIso (A : System.{u, u} |c.pt|) (n : ℕ) :
    filteredChainDiagram F c A ⋙ HomologicalComplex.eval _ _ n ≅
      filteredModuleDiagram F c A ⦋n⦌ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro j k a
    change (stageChainMap F c A a).f n ≫ 𝟙 _ =
      𝟙 _ ≫ (filteredModuleDiagram F c A ⦋n⦌).map a
    simp only [Category.comp_id, Category.id_comp, stageChainMap_f])

/-- The original local-coefficient chain cocone is colimiting. -/
def filteredChainIsColimit [IsFiltered J] (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) : IsColimit (filteredChainCocone F c A) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  exact (IsColimit.equivOfNatIsoOfIso (filteredChainEvalIso F c A n)
    ((HomologicalComplex.eval _ _ n).mapCocone (filteredChainCocone F c A))
    (filteredModuleCocone F c A ⦋n⦌)
    (Cocone.ext (Iso.refl _) (by
      intro j
      change 𝟙 _ ≫ pushforwardModuleMap (SSet.toTop.map (c.ι.app j)).hom A ⦋n⦌ ≫
        𝟙 _ = pushforwardModuleMap (SSet.toTop.map (c.ι.app j)).hom A ⦋n⦌
      simp))).symm
      (filteredModuleIsColimit F c hc A ⦋n⦌)


/-- The canonical comparison from the actual chain colimit is an isomorphism. -/
def filteredChainColimitIso [IsFiltered J] (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) :
    colimit (filteredChainDiagram F c A) ≅ singularChainComplex A :=
  colimit.isoColimitCocone ⟨_, filteredChainIsColimit F c hc A⟩

/-- The comparison isomorphism carries each colimit leg to the original spatial chain map. -/
@[reassoc]
theorem filteredChainColimitIso_ι_hom [IsFiltered J] (hc : IsColimit c)
    (A : System.{u, u} |c.pt|) (j : J) :
    colimit.ι (filteredChainDiagram F c A) j ≫ (filteredChainColimitIso F c hc A).hom =
      pushforwardChainMap (SSet.toTop.map (c.ι.app j)).hom A :=
  colimit.isoColimitCocone_ι_hom _ _

end FundamentalGroupoid.LocalCoefficients
