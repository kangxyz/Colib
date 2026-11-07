/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Quillen.Field.SymbolMarking.RankThree
public import Colib.Topology.Homotopy.HomotopyGroup.PeriodicLoopFamilies
public import Colib.KTheory.Quillen.LowDegreeScalarAction.BiproductLoopFamilies
public import Colib.KTheory.Quillen.LowDegreeScalarAction.ExactNaturality
public import Colib.KTheory.Quillen.Automorphism.Universal
public import Colib.Topology.Realization.DoubleHomotopy
public import Colib.Topology.Homotopy.HomotopyGroup.SelfTrackLoopShift
public import Colib.Topology.ClassifyingSpace.UniversalComposition

/-!
# The rank-three periodic torus compared with the original positive scalar cube

The rank-three periodic torus compared with the original positive scalar cube.

All comparisons retain the original maps and require only the stated hypotheses.
-/
/-! Adapted from `Quillen/KTheory/Field/SymbolMarking/ScalarCube.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. All actual scalar tracks,
axis orders, retained object loops and both inversions remain unchanged.
Categorical interchange and identity-Q automorphisms have unique lower owners. -/
@[expose] public section
noncomputable section

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup
open scoped Topology unitInterval

universe u

namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective

variable (F : Type u) [Field F]

/-- The source endomorphism inverting both unit coordinates. -/
def sourceInverse : (Fˣ × Fˣ) →* (Fˣ × Fˣ) := (MonoidHom.id (Fˣ × Fˣ))⁻¹

theorem inverseCharacter_edge (χ : (Fˣ × Fˣ) →* Fˣ) (g : Fˣ × Fˣ) (t : unitInterval) :
    rowLoop F (scalarRow F χ⁻¹) (sourceEdge F g t) =
      rowLoop F (scalarRow F χ) (sourceEdge F g⁻¹ t) := by
  have h := scalarRow_loop_precomp F (sourceInverse F) χ (sourceEdge F g t)
  have hc : χ.comp (sourceInverse F) = χ⁻¹ := by
    apply MonoidHom.ext
    intro g
    exact map_inv χ g
  rw [hc, sourceEdge_map] at h
  exact h.symm

/-- The actual inverse edge is homotopic to the reversed original edge, through
the original group classifying-space equivalence. -/
def sourceInverseEdgeHomotopy (g : Fˣ × Fˣ) :
    (sourceEdge F g⁻¹).Homotopy (sourceEdge F g).symm := by
  have h := map_inv (GroupoidClassifying.singleObjFundamentalGroupEquiv (Fˣ × Fˣ)) g
  change (Path.Homotopic.Quotient.mk (sourceEdge F g⁻¹)) =
    Path.Homotopic.Quotient.mk (sourceEdge F g).symm at h
  exact (Quotient.exact h).some

/-- Original rank-one edge, with the actual shared object-loop endpoint retained. -/
def rowEdge (χ : (Fˣ × Fˣ) →* Fˣ) (g : Fˣ × Fˣ) :
    Path (sourceObjectLoop F) (sourceObjectLoop F) :=
  ((sourceEdge F g).map (rowLoop F (scalarRow F χ)).continuous).cast
    (scalarRow_loop_vertex F χ).symm (scalarRow_loop_vertex F χ).symm

@[simp] theorem rowEdge_apply (χ : (Fˣ × Fˣ) →* Fˣ) (g : Fˣ × Fˣ) (t : unitInterval) :
    rowEdge F χ g t = rowLoop F (scalarRow F χ) (sourceEdge F g t) := rfl

/-- This is the actual inverse-character path homotopy used by both axis caps. -/
def inverseRowEdgeHomotopy (χ : (Fˣ × Fˣ) →* Fˣ) (g : Fˣ × Fˣ) :
    (rowEdge F χ⁻¹ g).Homotopy (rowEdge F χ g).symm := by
  let K := ((sourceInverseEdgeHomotopy F g).map (rowLoop F (scalarRow F χ))).pathCast
    (scalarRow_loop_vertex F χ).symm (scalarRow_loop_vertex F χ).symm
  refine K.cast ?_ ?_
  · apply Path.ext
    funext t
    exact (inverseCharacter_edge F χ g t).symm
  · apply Path.ext
    funext t
    rfl

/-- The first unit-coordinate character. -/
def firstCharacter : (Fˣ × Fˣ) →* Fˣ := MonoidHom.fst Fˣ Fˣ
/-- The second unit-coordinate character. -/
def secondCharacter : (Fˣ × Fˣ) →* Fˣ := MonoidHom.snd Fˣ Fˣ

theorem firstCharacter_torus (a b : Fˣ) (t s : unitInterval) :
    rowLoop F (scalarRow F (firstCharacter F)) (rawTorus F a b (t,s)) =
      rowEdge F (firstCharacter F) (a,1) t := by
  have hc : (firstCharacter F).comp (firstProjection F) = firstCharacter F := by ext g; rfl
  have h := scalarRow_loop_precomp F (firstProjection F) (firstCharacter F)
    (rawTorus F a b (t,s))
  rw [hc, firstProjection_torus] at h
  exact h.symm

theorem secondCharacter_torus (a b : Fˣ) (t s : unitInterval) :
    rowLoop F (scalarRow F (secondCharacter F)) (rawTorus F a b (t,s)) =
      rowEdge F (secondCharacter F) (1,b) s := by
  have hc : (secondCharacter F).comp (secondProjection F) = secondCharacter F := by ext g; rfl
  have h := scalarRow_loop_precomp F (secondProjection F) (secondCharacter F)
    (rawTorus F a b (t,s))
  rw [hc, secondProjection_torus] at h
  exact h.symm

theorem firstFamily_eq_axis (a b : Fˣ) :
    sourceLoopFamily F a b (rowLoop F (scalarRow F (firstCharacter F))) =
      axisFamily true (rowEdge F (firstCharacter F) (a,1)) := by
  apply Subtype.ext
  ext z q
  exact congrArg (fun p => p q) (firstCharacter_torus F a b z.1 z.2)

theorem secondFamily_eq_axis (a b : Fˣ) :
    sourceLoopFamily F a b (rowLoop F (scalarRow F (secondCharacter F))) =
      axisFamily false (rowEdge F (secondCharacter F) (1,b)) := by
  apply Subtype.ext
  ext z q
  exact congrArg (fun p => p q) (secondCharacter_torus F a b z.1 z.2)

theorem firstInverseFamily_eq_axis (a b : Fˣ) :
    sourceLoopFamily F a b (rowLoop F (row1 F)) =
      axisFamily true (rowEdge F (firstCharacter F)⁻¹ (a,1)) := by
  apply Subtype.ext
  ext z q
  exact congrArg (fun p => p q) (row1_torus F a b z.1 z.2)

theorem secondInverseFamily_eq_axis (a b : Fˣ) :
    sourceLoopFamily F a b (rowLoop F (row2 F)) =
      axisFamily false (rowEdge F (secondCharacter F)⁻¹ (1,b)) := by
  apply Subtype.ext
  ext z q
  exact congrArg (fun p => p q) (row2_torus F a b z.1 z.2)

/-- The original constant row and scalar row give the genuine family commutation.
The braiding's vertex track is retained; its object loop is not assumed null. -/
def scalarRowLoopCommutation (χ : (Fˣ × Fˣ) →* Fˣ) :
    (⟨fun z => (rowLoop F (scalarRow F χ)
      (classifyingSpacePoint (SingleObj.star _))).trans (rowLoop F (scalarRow F χ) z),
      by fun_prop⟩ : C(ClassifyingSpace (TorusSource F),
        Path (exactStructure Fᵐᵒᵖ).kBasepoint (exactStructure Fᵐᵒᵖ).kBasepoint)).Homotopy
    ⟨fun z => (rowLoop F (scalarRow F χ) z).trans
      (rowLoop F (scalarRow F χ) (classifyingSpacePoint (SingleObj.star _))), by fun_prop⟩ := by
  refine (coreLoopCommutation (exactStructure Fᵐᵒᵖ)
    (constantRow F) (scalarRow F χ)).cast ?_ ?_
  · ext z q
    change ((rowLoop F (constantRow F) z).trans (rowLoop F (scalarRow F χ) z)) q =
      ((rowLoop F (scalarRow F χ) (classifyingSpacePoint (SingleObj.star _))).trans
        (rowLoop F (scalarRow F χ) z)) q
    rw [constantRow_loop, scalarRow_loop_vertex]
    rfl
  · ext z q
    change ((rowLoop F (scalarRow F χ) z).trans (rowLoop F (constantRow F) z)) q =
      ((rowLoop F (scalarRow F χ) z).trans
        (rowLoop F (scalarRow F χ) (classifyingSpacePoint (SingleObj.star _)))) q
    rw [constantRow_loop, scalarRow_loop_vertex]
    rfl

/-- First-axis cancellation keeps the double original object-loop factor. -/
theorem first_inverse_class (a b : Fˣ) :
    sourceLoopClass F a b (rowLoop F (scalarRow F (firstCharacter F))) *
      sourceLoopClass F a b (rowLoop F (row1 F)) =
    sourceLoopClass F a b (ContinuousMap.const _ (sourceObjectLoop F)) *
      sourceLoopClass F a b (ContinuousMap.const _ (sourceObjectLoop F)) := by
  have h := periodicClass_of_path
    (axisHomotopy true (inverseRowEdgeHomotopy F (firstCharacter F) (a,1)))
  change periodicClass (sourceLoopFamily F a b (rowLoop F (scalarRow F (firstCharacter F)))) *
    periodicClass (sourceLoopFamily F a b (rowLoop F (row1 F))) = _
  rw [firstFamily_eq_axis, firstInverseFamily_eq_axis, h]
  exact inverseAxis_periodic_class (rowLoop F (scalarRow F (firstCharacter F)))
    (classifyingSpacePoint (SingleObj.star _)) (scalarRowLoopCommutation F (firstCharacter F))
    true (sourceObjectLoop F) (scalarRow_loop_vertex F (firstCharacter F)) (sourceEdge F (a,1))

/-- Second-axis cancellation uses the same actual construction, on the other axis. -/
theorem second_inverse_class (a b : Fˣ) :
    sourceLoopClass F a b (rowLoop F (scalarRow F (secondCharacter F))) *
      sourceLoopClass F a b (rowLoop F (row2 F)) =
    sourceLoopClass F a b (ContinuousMap.const _ (sourceObjectLoop F)) *
      sourceLoopClass F a b (ContinuousMap.const _ (sourceObjectLoop F)) := by
  have h := periodicClass_of_path
    (axisHomotopy false (inverseRowEdgeHomotopy F (secondCharacter F) (1,b)))
  change periodicClass (sourceLoopFamily F a b (rowLoop F (scalarRow F (secondCharacter F)))) *
    periodicClass (sourceLoopFamily F a b (rowLoop F (row2 F))) = _
  rw [secondFamily_eq_axis, secondInverseFamily_eq_axis, h]
  exact inverseAxis_periodic_class (rowLoop F (scalarRow F (secondCharacter F)))
    (classifyingSpacePoint (SingleObj.star _)) (scalarRowLoopCommutation F (secondCharacter F))
    false (sourceObjectLoop F) (scalarRow_loop_vertex F (secondCharacter F)) (sourceEdge F (1,b))

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open Topology HomotopyGroup
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open MonoidalCategory CartesianMonoidalCategory
open scoped ZeroObject Simplicial Topology unitInterval

universe u v w
namespace FGModuleCat.SymbolMarking.Trace
open CategoryTheory.ExactCategory.IdentityAutomorphism
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies.Equivariance
universe k
open ModuleCat.FiniteProjective
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
  FGModuleCat.SymbolMarking
variable (F : Type k) [Field F]

/-- The scalar natural automorphism using the forward opposite unit. -/
def scalarAut (a : Fˣ) := CategoryTheory.Linear.scalarNatAut Fᵐᵒᵖ
  (ModuleCat.FiniteProjective.Category.{k, k} Fᵐᵒᵖ) (FGModuleCat.SymbolMarking.opUnit F a)

/-- The literal common-source cone cylinder intertwines the source a edge with
the ORIGINAL scalar identity-natural-automorphism homotopy. -/
theorem rowConeScalar (a : Fˣ)
    (η : (Functor.const (TorusSource F)).obj (exactStructure.{k, k} Fᵐᵒᵖ).qZero ⟶
      row0 F ⋙ Automorphism.coreQ (exactStructure.{k, k} Fᵐᵒᵖ))
    (z : ClassifyingSpace (TorusSource F)) (q t : unitInterval) :
    classifyingSpaceUniversalHomotopy η (q,sourceHomotopy F (a,1) (t,z)) =
      IdentityAutomorphism.homotopy (exactStructure.{k, k} Fᵐᵒᵖ) (scalarAut F a)
        (t,classifyingSpaceUniversalHomotopy η (q,z)) := by
  let α := sourceTransformation F (a,1)
  let β := (identityQAut.{k + 1, k} (exactStructure.{k, k} Fᵐᵒᵖ) (scalarAut F a)).hom
  have hF (d : TorusSource F) :
      ((Functor.const (TorusSource F)).obj (exactStructure.{k, k} Fᵐᵒᵖ).qZero).map (α.app d) =
        β.app (exactStructure.{k, k} Fᵐᵒᵖ).qZero := by
    apply @Subsingleton.elim _
      ((exactStructure.{k, k} Fᵐᵒᵖ).qHom_subsingleton_of_isZero _ _
        (isZero_zero (ModuleCat.FiniteProjective.Category.{k, k} Fᵐᵒᵖ)))
  have hG (d : TorusSource F) :
      (row0 F ⋙ Automorphism.coreQ (exactStructure.{k, k} Fᵐᵒᵖ)).map (α.app d) =
        β.app ((row0 F ⋙ Automorphism.coreQ (exactStructure.{k, k} Fᵐᵒᵖ)).obj d) := by
    cases d
    change ((exactStructure.{k, k} Fᵐᵒᵖ).qIsoOfIso
      (((row0 F).map (SingleObj.toEnd (Fˣ × Fˣ) (a,1))).iso)).hom =
        ((exactStructure.{k, k} Fᵐᵒᵖ).qIsoOfIso ((scalarAut F a).app (free (R := Fᵐᵒᵖ) 1))).hom
    rw [row0_first_component]
    rfl
  have h := universalInterchange.{0, k, k + 1} η α β hF hG q t z
  rw [Promotion.universal_eq] at h
  exact h.trans (identityQAut_homotopy.{k + 1, k} (exactStructure.{k, k} Fᵐᵒᵖ) (scalarAut F a) t _)

/-- All three parameters of the mixed rank-one row are exactly the original
scalar track on the original b-edge Q-loop. -/
theorem row0ScalarTrace (a b : Fˣ) (t s q : unitInterval) :
    rowLoop F (row0 F) (rawTorus F a b (t,s)) q =
      IdentityAutomorphism.homotopy (exactStructure.{k, k} Fᵐᵒᵖ) (scalarAut F a)
        (t,rowLoop F (row0 F) (sourceEdge F (1,b) s) q) := by
  change ((ConePair.realizedCone (zeroCone (exactStructure.{k, k} Fᵐᵒᵖ) (row0 F))).evalAt
      (sourceHomotopy F (a,1) (t,sourceEdge F (1,b) s))).trans
      ((ConePair.realizedCone (fullCone (exactStructure.{k, k} Fᵐᵒᵖ) (row0 F))).evalAt
        (sourceHomotopy F (a,1) (t,sourceEdge F (1,b) s))).symm q =
    IdentityAutomorphism.homotopy (exactStructure.{k, k} Fᵐᵒᵖ) (scalarAut F a)
      (t,((ConePair.realizedCone (zeroCone (exactStructure.{k, k} Fᵐᵒᵖ) (row0 F))).evalAt
        (sourceEdge F (1,b) s)).trans
        ((ConePair.realizedCone (fullCone (exactStructure.{k, k} Fᵐᵒᵖ) (row0 F))).evalAt
          (sourceEdge F (1,b) s)).symm q)
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact rowConeScalar F a (zeroCone (exactStructure.{k, k} Fᵐᵒᵖ) (row0 F))
      (sourceEdge F (1,b) s) _ t
  · exact rowConeScalar F a (fullCone (exactStructure.{k, k} Fᵐᵒᵖ) (row0 F))
      (sourceEdge F (1,b) s) _ t

end FGModuleCat.SymbolMarking.Trace

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup
open scoped Topology unitInterval IsMulCommutative

universe u

namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective

variable (F : Type u) [Field F] (a b : Fˣ)

/-- Only the actual core-row classes generate this subgroup. Its commutativity
comes from the constructed braiding homotopy, not from a target-wide assertion. -/
def rowClassSubgroup : Subgroup (PeriodicLoopClass (x := (exactStructure Fᵐᵒᵖ).kBasepoint)) :=
  Subgroup.closure (Set.range (fun L : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ =>
    sourceLoopClass F a b (rowLoop F L)))

instance rowClassSubgroup_commutative : IsMulCommutative (rowClassSubgroup F a b) :=
  Subgroup.isMulCommutative_closure (by
    rintro x ⟨L, rfl⟩ y ⟨R, rfl⟩
    exact (sourceRows_commute F a b L R).eq)

/-- A row loop class in the subgroup generated by all row classes. -/
def rowClass (L : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ) : rowClassSubgroup F a b :=
  ⟨sourceLoopClass F a b (rowLoop F L), Subgroup.subset_closure ⟨L, rfl⟩⟩

private theorem normalForm_algebra {G : Type*} [CommGroup G]
    (r A B T n₁ n₂ : G) (h₁ : A * n₁ = r * r) (h₂ : B * n₂ = r * r) :
    (n₂ * (n₁ * T))⁻¹ * (r * (r * r)) = (B⁻¹ * r)⁻¹ * (T⁻¹ * A) := by
  have hn₁ : n₁ = A⁻¹ * (r * r) := by rw [← h₁]; simp
  have hn₂ : n₂ = B⁻¹ * (r * r) := by rw [← h₂]; simp
  rw [hn₁, hn₂]
  simp [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

/-- The original native torus family is the scalar difference word in the group
of genuine periodic homotopy classes. All inverse-axis relations are discharged. -/
theorem native_periodic_normalForm :
    sourceLoopClass F a b (nativeRankThreeLoopMap F) =
      ((sourceLoopClass F a b (rowLoop F (scalarRow F (secondCharacter F))))⁻¹ *
        sourceLoopClass F a b (ContinuousMap.const _ (sourceObjectLoop F)))⁻¹ *
      ((sourceLoopClass F a b (rowLoop F (row0 F)))⁻¹ *
        sourceLoopClass F a b (rowLoop F (scalarRow F (firstCharacter F)))) := by
  let r := rowClass F a b (constantRow F)
  let A := rowClass F a b (scalarRow F (firstCharacter F))
  let B := rowClass F a b (scalarRow F (secondCharacter F))
  let T := rowClass F a b (row0 F)
  let n₁ := rowClass F a b (row1 F)
  let n₂ := rowClass F a b (row2 F)
  have h₁ : A * n₁ = r * r := by
    apply Subtype.ext
    change _ = sourceLoopClass F a b (rowLoop F (constantRow F)) *
      sourceLoopClass F a b (rowLoop F (constantRow F))
    rw [constantRow_loop]
    exact first_inverse_class F a b
  have h₂ : B * n₂ = r * r := by
    apply Subtype.ext
    change _ = sourceLoopClass F a b (rowLoop F (constantRow F)) *
      sourceLoopClass F a b (rowLoop F (constantRow F))
    rw [constantRow_loop]
    exact second_inverse_class F a b
  have h := congrArg Subtype.val (normalForm_algebra r A B T n₁ n₂ h₁ h₂)
  change (sourceLoopClass F a b (rowLoop F (row2 F)) *
      (sourceLoopClass F a b (rowLoop F (row1 F)) *
        sourceLoopClass F a b (rowLoop F (row0 F))))⁻¹ *
      (sourceLoopClass F a b (rowLoop F (constantRow F)) *
        (sourceLoopClass F a b (rowLoop F (constantRow F)) *
          sourceLoopClass F a b (rowLoop F (constantRow F)))) =
    ((sourceLoopClass F a b (rowLoop F (scalarRow F (secondCharacter F))))⁻¹ *
      sourceLoopClass F a b (rowLoop F (constantRow F)))⁻¹ *
      ((sourceLoopClass F a b (rowLoop F (row0 F)))⁻¹ *
        sourceLoopClass F a b (rowLoop F (scalarRow F (firstCharacter F)))) at h
  rw [constantRow_loop] at h
  exact (native_periodic_word F a b).trans h

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup
open scoped Topology unitInterval

universe u

namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective CategoryTheory.ExactCategory

variable (F : Type u) [Field F]

theorem mixed_first_face (a b : Fˣ) (t s : unitInterval) :
    rowLoop F (scalarRow F (firstCharacter F)) (rawTorus F a b (t,s)) =
      rowLoop F (row0 F) (sourceEdge F (a,1) t) := by
  have hc : (mixedCharacter F).comp (firstProjection F) = firstCharacter F := by
    apply MonoidHom.ext
    intro g
    simp [mixedCharacter, firstProjection, firstCharacter]
  have h := scalarRow_loop_precomp F (firstProjection F) (mixedCharacter F)
    (rawTorus F a b (t,s))
  rw [hc, firstProjection_torus] at h
  exact h.symm

theorem mixed_second_face (a b : Fˣ) (t s : unitInterval) :
    rowLoop F (scalarRow F (secondCharacter F)) (rawTorus F a b (t,s)) =
      rowLoop F (row0 F) (sourceEdge F (1,b) s) := by
  have hc : (mixedCharacter F).comp (secondProjection F) = secondCharacter F := by
    apply MonoidHom.ext
    intro g
    simp [mixedCharacter, secondProjection, secondCharacter]
  have h := scalarRow_loop_precomp F (secondProjection F) (mixedCharacter F)
    (rawTorus F a b (t,s))
  rw [hc, secondProjection_torus] at h
  exact h.symm

theorem objectLoopScalarTrace (a : Fˣ) (t q : unitInterval) :
    rowLoop F (row0 F) (sourceEdge F (a,1) t) q =
      IdentityAutomorphism.homotopy (exactStructure Fᵐᵒᵖ) (Trace.scalarAut F a)
        (t,sourceObjectLoop F q) := by
  have h := Trace.row0ScalarTrace F a 1 t 0 q
  rw [rawTorus_zero_second, Path.source] at h
  change _ = IdentityAutomorphism.homotopy (exactStructure Fᵐᵒᵖ) (Trace.scalarAut F a)
    (t,rowLoop F (scalarRow F (mixedCharacter F)) (classifyingSpacePoint (SingleObj.star _)) q) at h
  rw [scalarRow_loop_vertex] at h
  exact h

/-- The periodic family obtained by applying the scalar trace. -/
def scalarTraceFamily (a : Fˣ)
    (p : PeriodicSquare (Path (exactStructure Fᵐᵒᵖ).kBasepoint
      (exactStructure Fᵐᵒᵖ).kBasepoint)) :
    PeriodicSquare (Path (exactStructure Fᵐᵒᵖ).kBasepoint
      (exactStructure Fᵐᵒᵖ).kBasepoint) :=
  ⟨⟨fun z =>
    { toFun q := IdentityAutomorphism.homotopy (exactStructure Fᵐᵒᵖ) (Trace.scalarAut F a)
        (z.1,p.val z q)
      continuous_toFun := by fun_prop
      source' := by rw [(p.val z).source]; exact IdentityAutomorphism.homotopy_fixed _ _ _
      target' := by rw [(p.val z).target]; exact IdentityAutomorphism.homotopy_fixed _ _ _ }, by
      apply Path.continuous_uncurry_iff.mp
      change Continuous (fun z : (unitInterval × unitInterval) × unitInterval =>
        IdentityAutomorphism.homotopy (exactStructure Fᵐᵒᵖ) (Trace.scalarAut F a)
          (z.1.1,p.val z.1 z.2))
      fun_prop⟩, by
    constructor
    · intro s
      apply Path.ext
      funext q
      change IdentityAutomorphism.homotopy _ _ (0,p.val (0,s) q) =
        IdentityAutomorphism.homotopy _ _ (1,p.val (1,s) q)
      exact ((IdentityAutomorphism.homotopy _ _).toHomotopy.apply_zero _).trans
        ((congrArg (fun p => p q) (p.property.1 s)).trans
          ((IdentityAutomorphism.homotopy _ _).toHomotopy.apply_one _).symm)
    · intro t
      apply Path.ext
      funext q
      change IdentityAutomorphism.homotopy _ _ (t,p.val (t,0) q) =
        IdentityAutomorphism.homotopy _ _ (t,p.val (t,1) q)
      rw [p.property.2]⟩

/-- The original full-first b-row, right-normalized by its actual object loop. -/
def normalizedSecondFamily (a b : Fˣ) :=
  periodicConcat
    (periodicReverse (sourceLoopFamily F a b
      (rowLoop F (scalarRow F (secondCharacter F)))))
    (periodicConstant _ (sourceObjectLoop F))

/-- The entire scalar trace of this actual normalization is the literal mixed
row followed by the literal first-axis row, with the original reversal. -/
theorem scalarTrace_normalizedSecond (a b : Fˣ) :
    scalarTraceFamily F a (normalizedSecondFamily F a b) =
      periodicConcat (periodicReverse (sourceLoopFamily F a b (rowLoop F (row0 F))))
        (sourceLoopFamily F a b (rowLoop F (scalarRow F (firstCharacter F)))) := by
  apply Subtype.ext
  ext z q
  change IdentityAutomorphism.homotopy (exactStructure Fᵐᵒᵖ) (Trace.scalarAut F a)
    (z.1,((rowLoop F (scalarRow F (secondCharacter F)) (rawTorus F a b z)).symm.trans
      (sourceObjectLoop F)) q) =
    ((rowLoop F (row0 F) (rawTorus F a b z)).symm.trans
      (rowLoop F (scalarRow F (firstCharacter F)) (rawTorus F a b z))) q
  rw [mixed_second_face, mixed_first_face]
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact (Trace.row0ScalarTrace F a b z.1 z.2 _).symm
  · exact (objectLoopScalarTrace F a z.1 _).symm

/-- The concatenation of the reversed input family and its scalar trace. -/
def rawScalarDifference (a b : Fˣ) :=
  periodicConcat (periodicReverse (normalizedSecondFamily F a b))
    (scalarTraceFamily F a (normalizedSecondFamily F a b))

theorem rawScalarDifference_class (a b : Fˣ) :
    periodicClass (rawScalarDifference F a b) =
      ((sourceLoopClass F a b (rowLoop F (scalarRow F (secondCharacter F))))⁻¹ *
        sourceLoopClass F a b (ContinuousMap.const _ (sourceObjectLoop F)))⁻¹ *
      ((sourceLoopClass F a b (rowLoop F (row0 F)))⁻¹ *
        sourceLoopClass F a b (rowLoop F (scalarRow F (firstCharacter F)))) := by
  unfold rawScalarDifference
  rw [scalarTrace_normalizedSecond]
  simp only [normalizedSecondFamily, periodicClass_concat, periodicClass_reverse]
  rfl

/-- A genuine periodic homotopy from the original native torus to the original
scalar difference word. Its vertex track is retained and will supply both caps. -/
def nativeToScalarDifference (a b : Fˣ) :
    Path (sourceLoopFamily F a b (nativeRankThreeLoopMap F)) (rawScalarDifference F a b) :=
  periodicPathOfClassEq ((native_periodic_normalForm F a b).trans
    (rawScalarDifference_class F a b).symm)

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup
open scoped Topology unitInterval

universe u v

namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective CategoryTheory.ExactCategory

/-- The continuous interchange of the two periodic-square coordinates. -/
def periodicSwap {Y : Type v} [TopologicalSpace Y] : C(PeriodicSquare Y, PeriodicSquare Y) where
  toFun P := ⟨⟨fun z => P.val (z.2, z.1), by fun_prop⟩, P.property.2, P.property.1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : PeriodicSquare Y × (unitInterval × unitInterval) =>
      z.1.val (z.2.2, z.2.1))
    fun_prop

variable (F : Type u) [Field F]

/-- The second source edge after right normalization. -/
def normalizedBEdge (b : Fˣ) :
    Path ((sourceObjectLoop F).symm.trans (sourceObjectLoop F))
      ((sourceObjectLoop F).symm.trans (sourceObjectLoop F)) :=
  (rowEdge F (secondCharacter F) (1, b)).map
    (f := fun q => q.symm.trans (sourceObjectLoop F))
    (show Continuous (fun q : Path (exactStructure Fᵐᵒᵖ).kBasepoint
      (exactStructure Fᵐᵒᵖ).kBasepoint => q.symm.trans (sourceObjectLoop F)) from
      Path.continuous_symm.path_trans continuous_const)

/-- The inverse-prefix cancellation cap of the original rank-one object loop. -/
def rankOneCap := loopInversePrefixCancellation (sourceObjectLoop F)

/-- The actual right-normalized full-first input, with its original cancellation cap. -/
def basedBEdge (b : Fˣ) :
    Path (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)
      (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint) :=
  ((rankOneCap F).symm.trans (normalizedBEdge F b)).trans (rankOneCap F)

theorem normalizedSecondFamily_axis (a b : Fˣ) :
    normalizedSecondFamily F a b = axisFamily false (normalizedBEdge F b) := by
  apply Subtype.ext
  ext z q
  change ((rowLoop F (scalarRow F (secondCharacter F)) (rawTorus F a b z)).symm.trans
    (sourceObjectLoop F)) q = _
  rw [secondCharacter_torus]
  rfl

/-- Rebase the entire b-circle by the actual cap; its whole moving vertex survives. -/
def normalizedSecondToBased (a b : Fˣ) :
    Path (normalizedSecondFamily F a b) (axisFamily false (basedBEdge F b)) := by
  let P := axisFamily true (normalizedBEdge F b)
  let C : C(unitInterval × unitInterval,
      Path (exactStructure Fᵐᵒᵖ).kBasepoint (exactStructure Fᵐᵒᵖ).kBasepoint) :=
    ⟨fun z => rankOneCap F z.1, by fun_prop⟩
  have h₀ (s : unitInterval) : C (0, s) = P.val (0, s) :=
    (rankOneCap F).source.trans (normalizedBEdge F b).source.symm
  have hper (r : unitInterval) : C (r, 0) = C (r, 1) := rfl
  let J := insertPeriodicCaps P C h₀ hper
  have hend : capConjugatedSquare P C h₀ hper 1 = axisFamily true (basedBEdge F b) := by
    apply Subtype.ext
    ext z q
    change ((((capPrefix P C h₀ 1 z.2).symm.trans (periodicSlice P z.2)).trans
      (capPrefix P C h₀ 1 z.2)) z.1) q = (basedBEdge F b z.1) q
    have hp (s t : unitInterval) : capPrefix P C h₀ 1 s t = rankOneCap F t := by
      change rankOneCap F (1 * t) = _
      rw [one_mul]
    simp only [basedBEdge, Path.trans_apply, Path.symm_apply]
    split_ifs <;> first | exact congrArg (fun p => p q) (hp _ _) | rfl
  have J' : Path (axisFamily true (normalizedBEdge F b))
      (axisFamily true (basedBEdge F b)) := J.cast rfl hend.symm
  exact (J'.map periodicSwap.continuous).cast (normalizedSecondFamily_axis F a b)
    (by apply Subtype.ext; ext z q; rfl)

/-- The scalar difference family associated with a periodic loop family. -/
def scalarDifferenceOf (a : Fˣ)
    (p : PeriodicSquare (Path (exactStructure Fᵐᵒᵖ).kBasepoint
      (exactStructure Fᵐᵒᵖ).kBasepoint)) :=
  periodicConcat (periodicReverse p) (scalarTraceFamily F a p)

/-- A genuine moving-input homotopy transports the ENTIRE scalar difference family. -/
def scalarDifferencePath (a : Fˣ)
    {p q : PeriodicSquare (Path (exactStructure Fᵐᵒᵖ).kBasepoint
      (exactStructure Fᵐᵒᵖ).kBasepoint)} (P : Path p q) :
    Path (scalarDifferenceOf F a p) (scalarDifferenceOf F a q) where
  toFun r := scalarDifferenceOf F a (P r)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    let H := IdentityTrack.loopedHomotopy
      (IdentityAutomorphism.homotopy (exactStructure Fᵐᵒᵖ) (Trace.scalarAut F a)).toHomotopy
      (IdentityAutomorphism.homotopy_fixed (exactStructure Fᵐᵒᵖ) (Trace.scalarAut F a))
    change Continuous (fun z : unitInterval × (unitInterval × unitInterval) =>
      ((P z.1).val z.2).symm.trans (H (z.2.1, (P z.1).val z.2)))
    have hp : Continuous (fun z : unitInterval × (unitInterval × unitInterval) =>
        (P z.1).val z.2) := by fun_prop
    exact (Path.continuous_symm.comp hp).path_trans
      (H.continuous.comp ((continuous_fst.comp continuous_snd).prodMk hp))
  source' := by rw [P.source]
  target' := by rw [P.target]

/-- The scalar difference of the based second-axis family. -/
def basedScalarDifference (a b : Fˣ) :=
  scalarDifferenceOf F a (axisFamily false (basedBEdge F b))

/-- The first whole cap is attached before any representative quotient. -/
def nativeToBasedScalarDifference (a b : Fˣ) :
    Path (sourceLoopFamily F a b (nativeRankThreeLoopMap F)) (basedScalarDifference F a b) :=
  (nativeToScalarDifference F a b).trans
    (scalarDifferencePath F a (normalizedSecondToBased F a b))

/-- The original inverse-prefix cancellation, continuously in the b-circle. -/
def selfTrackCapFamily (b : Fˣ) :
    C(unitInterval × unitInterval,
      Path (exactStructure Fᵐᵒᵖ).kBasepoint (exactStructure Fᵐᵒᵖ).kBasepoint) where
  toFun z := loopInversePrefixCancellation (basedBEdge F b z.2) z.1
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval × unitInterval) × unitInterval =>
      (basedBEdge F b z.1.2).symm
        ⟨Path.Homotopy.reflTransSymmAux (unitInterval.symm z.1.1, z.2),
          Path.Homotopy.reflTransSymmAux_mem_I _⟩)
    exact (Path.continuous_symm.comp ((basedBEdge F b).continuous.comp
      (continuous_snd.comp continuous_fst))).eval (by fun_prop)

theorem selfTrackCapFamily_start (a b : Fˣ) (s : unitInterval) :
    selfTrackCapFamily F b (0, s) = (basedScalarDifference F a b).val (0, s) := by
  change loopInversePrefixCancellation (basedBEdge F b s) 0 = _
  rw [Path.source]
  apply Path.ext
  funext q
  change ((basedBEdge F b s).symm.trans (basedBEdge F b s)) q =
    ((basedBEdge F b s).symm.trans
      (IdentityTrack.loopedHomotopy
        (IdentityAutomorphism.homotopy (exactStructure Fᵐᵒᵖ) (Trace.scalarAut F a)).toHomotopy
        (IdentityAutomorphism.homotopy_fixed (exactStructure Fᵐᵒᵖ) (Trace.scalarAut F a))
        (0, basedBEdge F b s))) q
  rw [ContinuousMap.Homotopy.apply_zero]
  rfl

theorem selfTrackCapFamily_periodic (b : Fˣ) (t : unitInterval) :
    selfTrackCapFamily F b (t, 0) = selfTrackCapFamily F b (t, 1) := by
  change loopInversePrefixCancellation (basedBEdge F b 0) t =
    loopInversePrefixCancellation (basedBEdge F b 1) t
  rw [Path.source, Path.target]

/-- The second whole cap is the literal cancellation already used by the scalar
self-track normalizer; its entire family is retained. -/
def nativeToCappedScalarDifference (a b : Fˣ) :
    Path (sourceLoopFamily F a b (nativeRankThreeLoopMap F))
      (capConjugatedSquare (basedScalarDifference F a b) (selfTrackCapFamily F b)
        (selfTrackCapFamily_start F a b) (selfTrackCapFamily_periodic F b) 1) :=
  (nativeToBasedScalarDifference F a b).trans
    (insertPeriodicCaps (basedScalarDifference F a b) (selfTrackCapFamily F b)
      (selfTrackCapFamily_start F a b) (selfTrackCapFamily_periodic F b))

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup
open scoped Topology unitInterval
universe u
namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking ModuleCat.FiniteProjective CategoryTheory.ExactCategory
variable (F : Type u) [Field F]

/-- The original scalar natural-automorphism homotopy. -/
abbrev originalScalarHomotopy (a : Fˣ) :=
  (IdentityAutomorphism.homotopy (exactStructure Fᵐᵒᵖ) (Trace.scalarAut F a)).toHomotopy

/-- The fixed-basepoint witness for the original scalar homotopy. -/
abbrev originalScalarHomotopyFixed (a : Fˣ) :=
  IdentityAutomorphism.homotopy_fixed (exactStructure Fᵐᵒᵖ) (Trace.scalarAut F a)

theorem cappedScalarDifference_eq_left (a b : Fˣ) :
    capConjugatedSquare (basedScalarDifference F a b) (selfTrackCapFamily F b)
      (selfTrackCapFamily_start F a b) (selfTrackCapFamily_periodic F b) 1 =
    trackPeriodic (basedBEdge F b)
      (leftCappedTrackMap (originalScalarHomotopy F a) (originalScalarHomotopyFixed F a)) := by
  apply Subtype.ext
  ext z q
  have hp (s t : unitInterval) :
      capPrefix (basedScalarDifference F a b) (selfTrackCapFamily F b)
        (selfTrackCapFamily_start F a b) 1 s t =
      loopInversePrefixCancellation (basedBEdge F b s) t := by
    change loopInversePrefixCancellation (basedBEdge F b s) (1 * t) = _
    rw [one_mul]
  change ((((capPrefix (basedScalarDifference F a b) (selfTrackCapFamily F b)
    (selfTrackCapFamily_start F a b) 1 z.2).symm.trans
      (periodicSlice (basedScalarDifference F a b) z.2)).trans
        (capPrefix (basedScalarDifference F a b) (selfTrackCapFamily F b)
          (selfTrackCapFamily_start F a b) 1 z.2)) z.1) q = _
  change _ = (((loopInversePrefixCancellation (basedBEdge F b z.2)).symm.trans
    ((prefixTrackHomotopy (originalScalarHomotopy F a)
      (originalScalarHomotopyFixed F a)).evalAt (basedBEdge F b z.2))).trans
      (loopInversePrefixCancellation (basedBEdge F b z.2))) z.1 q
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs <;> first | exact congrArg (fun p => p q) (hp _ _) | rfl

/-- The actual original scalar cube, including its original normalization axis. -/
def scalarLoopCube (a b : Fˣ) :=
  originalTrackLoopCube (originalScalarHomotopy F a) (originalScalarHomotopyFixed F a)
    (basedBEdge F b)

/-- The whole native rank-three torus is deformed to the literal scalar cube.
Both pairs of opposite edges remain equal throughout; the vertex track is kept. -/
def nativeToScalarCube (a b : Fˣ) :
    Path (sourceLoopFamily F a b (nativeRankThreeLoopMap F))
      (periodicOfCube (scalarLoopCube F a b)) :=
  ((nativeToCappedScalarDifference F a b).cast rfl
    (cappedScalarDifference_eq_left F a b).symm).trans
      ((trackPeriodicHomotopy (basedBEdge F b)
        (cappedTrackAssociator (originalScalarHomotopy F a)
          (originalScalarHomotopyFixed F a))).cast rfl
            (trackPeriodic_originalCube (originalScalarHomotopy F a)
              (originalScalarHomotopyFixed F a) (basedBEdge F b)).symm)

/-- The original coordinates give one transposition, hence the inverse operation. -/
theorem scalarLoopCube_class (a b : Fˣ) :
    (loopShiftMulEquiv (x := (exactStructure Fᵐᵒᵖ).kBasepoint) 1).symm
        (Quotient.mk' (scalarLoopCube F a b)) =
      (IdentityTrack.operation (originalScalarHomotopy F a) (originalScalarHomotopyFixed F a)
        1 (Quotient.mk' (inputCube (basedBEdge F b))) : (exactStructure Fᵐᵒᵖ).K 2)⁻¹ :=
  originalTrackLoopCube_class _ _ _

end FGModuleCat.SymbolMarking

end

section

open Topology.PeriodicFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.ExactCategory Topology HomotopyGroup
open scoped Topology unitInterval
universe u v
namespace FGModuleCat.SymbolMarking
open FGModuleCat.SymbolMarking
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
  ModuleCat.FiniteProjective

/-- Original path transport is represented by the displayed, left-associated caps. -/
theorem cappedPath_class {Y : Type v} [TopologicalSpace Y] {y z : Y}
    (p : Path y y) (c : Path y z) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
      (pathTransport c 1 (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (Path.Homotopic.Quotient.mk p))) =
      Path.Homotopic.Quotient.mk ((c.symm.trans p).trans c) := by
  rw [piOneEquivFundamentalGroup_pathTransport, MulEquiv.apply_symm_apply]
  change Path.Homotopic.Quotient.mk (c.symm.trans (p.trans c)) = _
  exact Quotient.sound ⟨(Path.Homotopy.transAssoc c.symm p c).symm⟩

variable (F : Type u) [Field F]

/-- The fundamental-group class of a unit-pair source edge. -/
def sourcePiOne (g : Fˣ × Fˣ) :
    HomotopyGroup.Pi 1 (ClassifyingSpace (TorusSource F))
      (classifyingSpacePoint (SingleObj.star _)) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm (Path.Homotopic.Quotient.mk (sourceEdge F g))

/-- The scalar matrix row of the second character at stage one. -/
def secondMatrixStageRow : TorusSource F ⥤ StableGeneralLinear.finiteCategory F 1 :=
  ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (secondCharacter F)).toFunctor ⋙ AsSmall.up

/-- The second scalar character viewed as a free rank-one power row. -/
def secondPowerRow : TorusSource F ⥤ IsoCategory Fᵐᵒᵖ :=
  ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (secondCharacter F)).toFunctor ⋙
    StableFree.powerFunctor F 1

/-- The same original power/free conjugacy, for the varying rank-one scalar row. -/
def secondPowerNatIso : scalarRow F (secondCharacter F) ≅ secondPowerRow F :=
  NatIso.ofComponents (fun _ => (rankOnePowerIsoFree Fᵐᵒᵖ 1).symm) (by
    intro X Y g
    cases X
    cases Y
    change (StableFree.freeEndEquiv F 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) g.2)) ≫
        (rankOnePowerIsoFree Fᵐᵒᵖ 1).inv =
      (rankOnePowerIsoFree Fᵐᵒᵖ 1).inv ≫
        ((rankOnePowerIsoFree Fᵐᵒᵖ 1).hom ≫
          StableFree.freeEndEquiv F 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) g.2) ≫
            (rankOnePowerIsoFree Fᵐᵒᵖ 1).inv)
    simp)

/-- The right-normalized loop map of the second scalar row. -/
def secondNormalizedMap :=
  Automorphism.rightNormalizedLoopMap
    (loopReversal.comp (rowLoop F (scalarRow F (secondCharacter F))))
      (classifyingSpacePoint (SingleObj.star _))

theorem secondNormalizedMap_apply (z : ClassifyingSpace (TorusSource F)) :
    secondNormalizedMap F z =
      (rowLoop F (scalarRow F (secondCharacter F)) z).symm.trans (sourceObjectLoop F) := by
  simp only [secondNormalizedMap, Automorphism.rightNormalizedLoopMap,
    ContinuousMap.comp_apply, Automorphism.rightTranslate,
    loopReversal_apply, Path.symm_symm, scalarRow_loop_vertex]
  rfl

/-- The existing whole-source cone isomorphism is applied before loop normalization. -/
def secondPowerNormalizedHomotopy :
    (secondNormalizedMap F).Homotopy
      (Automorphism.rightNormalizedLoopMap
        (loopReversal.comp (rowLoop F (secondPowerRow F)))
          (classifyingSpacePoint (SingleObj.star _))) :=
  Automorphism.rightNormalizedHomotopy
    ((ContinuousMap.Homotopy.refl loopReversal).comp
      (coreIsoLoopHomotopy (exactStructure Fᵐᵒᵖ) (scalarRow F (secondCharacter F))
        (secondPowerRow F) (secondPowerNatIso F)))
    (classifyingSpacePoint (SingleObj.star _))

theorem secondPowerRow_stage :
    rowLoop F (secondPowerRow F) =
      (stageCoreLoopMap F 1).comp (classifyingSpaceMapUniversal (secondMatrixStageRow F)) := by
  rw [rowLoop_eq]
  unfold stageCoreLoopMap
  rw [ContinuousMap.comp_assoc, ← classifyingSpaceMapUniversal_comp]
  rfl

theorem secondMatrixStageRow_piOne (b : Fˣ) :
    piMap 0 (classifyingSpaceMapUniversal (secondMatrixStageRow F))
      (classifyingSpaceMapUniversal_point (secondMatrixStageRow F) (SingleObj.star _))
        (sourcePiOne F (1,b)) =
      finiteMatrixPiOne F 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) b) := by
  apply (HomotopyGroup.pi1MulEquivFundamentalGroup
    (x := classifyingSpacePoint (stageVertex F 1))).injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (HomotopyGroup.map (classifyingSpaceMapUniversal (secondMatrixStageRow F))
      (classifyingSpaceMapUniversal_point (secondMatrixStageRow F) (SingleObj.star _))
      (sourcePiOne F (1, b))) = _
  erw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply]
  rw [FundamentalGroup.mapOfEq_apply]
  exact congrArg Path.Homotopic.Quotient.mk
    (classifyingSpaceMapUniversal_path_cast (secondMatrixStageRow F)
      (SingleObj.toEnd _ (1,b)))

/-- This is the actual cancellation cap used in the scalar input. -/
def secondNormalizedCap :
    Path (secondNormalizedMap F (classifyingSpacePoint (SingleObj.star _)))
      (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint) :=
  (rankOneCap F).cast
    (by rw [secondNormalizedMap_apply, scalarRow_loop_vertex]) rfl

/-- An explicitly capped mapped edge represents the original corrected map, then loop shift. -/
theorem mappedCappedInput_class {X : Type u} [TopologicalSpace X] {x : X}
    {Z : Type v} [TopologicalSpace Z] {z : Z} (f : C(Z, Path x x))
    (α : Path z z) (c : Path (f z) (Path.refl x)) :
    (Quotient.mk' (inputCube ((c.symm.trans (α.map f.continuous)).trans c)) :
      HomotopyGroup.Pi 2 X x) =
      (loopShiftMulEquiv 0).symm (pathTransportMulEquiv c 0
        (piMap 0 f rfl (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
          (Path.Homotopic.Quotient.mk α)))) := by
  apply (loopShiftMulEquiv 0).injective
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [MulEquiv.apply_symm_apply]
  change Path.Homotopic.Quotient.mk ((c.symm.trans (α.map f.continuous)).trans c) =
    HomotopyGroup.pi1MulEquivFundamentalGroup (pathTransport c 1 (piMap 0 f rfl
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm (Path.Homotopic.Quotient.mk α))))
  have hm : piMap 0 f rfl (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (Path.Homotopic.Quotient.mk α)) =
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (Path.Homotopic.Quotient.mk (α.map f.continuous)) := by
    apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
    change HomotopyGroup.pi1MulEquivFundamentalGroup
      (HomotopyGroup.map f rfl (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (Path.Homotopic.Quotient.mk α))) = _
    rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, FundamentalGroup.mapOfEq_apply]
    rfl
  rw [hm]
  exact (cappedPath_class _ _).symm

/-- The attached input caps are the actual corrected original scalar row map. -/
theorem basedBEdge_class (b : Fˣ) :
    (Quotient.mk' (inputCube (basedBEdge F b)) : (exactStructure Fᵐᵒᵖ).K 1) =
      (loopShiftMulEquiv 0).symm (pathTransportMulEquiv (secondNormalizedCap F) 0
        (piMap 0 (secondNormalizedMap F) rfl (sourcePiOne F (1,b)))) := by
  have hv : secondNormalizedMap F (classifyingSpacePoint (SingleObj.star _)) =
      (sourceObjectLoop F).symm.trans (sourceObjectLoop F) := by
    rw [secondNormalizedMap_apply, scalarRow_loop_vertex]
  have he : normalizedBEdge F b =
      (((sourceEdge F (1,b)).map (f := secondNormalizedMap F)
        (secondNormalizedMap F).continuous).cast hv.symm hv.symm) := by
    apply Path.ext
    funext t
    exact (secondNormalizedMap_apply F _).symm
  have hp : basedBEdge F b =
      (((secondNormalizedCap F).symm.trans
        ((sourceEdge F (1,b)).map (f := secondNormalizedMap F)
          (secondNormalizedMap F).continuous)).trans
          (secondNormalizedCap F)) := by
    unfold basedBEdge
    rw [he]
    rfl
  rw [hp]
  exact mappedCappedInput_class _ _ _

/-- Whole right normalization is natural under an actual based precomposition. -/
theorem rightNormalized_precomp {X A B : Type*}
    [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B] {x : X}
    (f : C(B, Path x x)) (g : C(A, B)) (a : A) (b : B) (h : g a = b) :
    Automorphism.rightNormalizedLoopMap (f.comp g) a =
      (Automorphism.rightNormalizedLoopMap f b).comp g := by
  ext z t
  change ((f (g z)).trans (f (g a)).symm) t = ((f (g z)).trans (f b).symm) t
  rw [h]

/-- The original corrected composite retains the supplied source endpoint equality. -/
theorem corrected_precomp {A B Y : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Y]
    (f : C(B, Y)) (g : C(A, B)) (a : A) (b : B) (h : g a = b)
    {y : Y} (c : Path (f b) y) (α : HomotopyGroup.Pi 1 A a) :
    pathTransportMulEquiv (c.cast (congrArg f h) rfl) 0
      (piMap 0 (f.comp g) rfl α) =
    pathTransportMulEquiv c 0 (piMap 0 f rfl (piMap 0 g h α)) := by
  subst b
  exact congrArg (pathTransport c 1) (HomotopyGroup.map_comp g rfl f rfl α)

/-- The right-normalized loop map of the original first matrix stage. -/
def secondStageNormalizedMap :=
  Automorphism.rightNormalizedLoopMap (loopReversal.comp (stageCoreLoopMap F 1))
    (classifyingSpacePoint (stageVertex F 1))

/-- The comparison of the second row with its normalized stage map. -/
def secondStageNormalizedHomotopy :
    (secondNormalizedMap F).Homotopy
      ((secondStageNormalizedMap F).comp (classifyingSpaceMapUniversal (secondMatrixStageRow F))) :=
  (secondPowerNormalizedHomotopy F).cast rfl (by
    rw [secondPowerRow_stage]
    exact rightNormalized_precomp (loopReversal.comp (stageCoreLoopMap F 1))
      (classifyingSpaceMapUniversal (secondMatrixStageRow F)) _ _
      (classifyingSpaceMapUniversal_point (secondMatrixStageRow F) (SingleObj.star _)))

/-- The basepoint cap for the normalized second matrix-stage row. -/
def secondStageCap :
    Path ((secondStageNormalizedMap F).comp
      (classifyingSpaceMapUniversal (secondMatrixStageRow F))
        (classifyingSpacePoint (SingleObj.star _)))
      (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint) :=
  (Automorphism.rightNormalizationPath (loopReversal.comp (stageCoreLoopMap F 1))
    (classifyingSpacePoint (stageVertex F 1))).cast
      (congrArg (secondStageNormalizedMap F)
        (classifyingSpaceMapUniversal_point (secondMatrixStageRow F) (SingleObj.star _))) rfl

/-- The actual capped rank-one input has the original positive matrix marking. -/
theorem basedBEdge_positive (b : Fˣ) :
    (Quotient.mk' (inputCube (basedBEdge F b)) : (exactStructure Fᵐᵒᵖ).K 1) =
      FGModuleCat.SymbolMarking.positiveRankOneKOne F b := by
  rw [basedBEdge_class]
  have h := DFunLike.congr_fun
    (piOne_homotopy_corrected (secondStageNormalizedHomotopy F)
      (secondNormalizedCap F) (secondStageCap F)
      (Automorphism.loopComponent_piOne_mul_comm (Path.refl (exactStructure Fᵐᵒᵖ).kBasepoint)))
    (sourcePiOne F (1,b))
  change pathTransportMulEquiv (secondNormalizedCap F) 0
    (piMap 0 (secondNormalizedMap F) rfl (sourcePiOne F (1,b))) =
      pathTransportMulEquiv (secondStageCap F) 0
        (piMap 0 ((secondStageNormalizedMap F).comp
          (classifyingSpaceMapUniversal (secondMatrixStageRow F))) rfl (sourcePiOne F (1,b))) at h
  rw [h]
  change (loopShiftMulEquiv 0).symm
    (pathTransportMulEquiv ((Automorphism.rightNormalizationPath
      (loopReversal.comp (stageCoreLoopMap F 1)) (classifyingSpacePoint (stageVertex F 1))).cast
        (congrArg (secondStageNormalizedMap F)
          (classifyingSpaceMapUniversal_point (secondMatrixStageRow F) (SingleObj.star _))) rfl) 0
      (piMap 0 ((secondStageNormalizedMap F).comp
        (classifyingSpaceMapUniversal (secondMatrixStageRow F))) rfl (sourcePiOne F (1,b)))) = _
  erw [corrected_precomp (secondStageNormalizedMap F)
    (classifyingSpaceMapUniversal (secondMatrixStageRow F)) _ _
    (classifyingSpaceMapUniversal_point (secondMatrixStageRow F) (SingleObj.star _))]
  erw [secondMatrixStageRow_piOne]
  erw [stageCoreLoop_normalizationOrder F 1]
  erw [← elementaryProjectiveKOneEquiv_matrix_positiveCore]
  exact StableCompletion.elementaryProjectiveKOneEquiv_quotientMap F _

/-- The capped endpoint is the inverse original scalar operation on the positive matrix input. -/
theorem scalarLoopCube_originalClass (a b : Fˣ) :
    (loopShiftMulEquiv (x := (exactStructure Fᵐᵒᵖ).kBasepoint) 1).symm
      (Quotient.mk' (scalarLoopCube F a b)) = (FGModuleCat.SymbolMarking.scalarClass F a b)⁻¹ :=
        by
  rw [scalarLoopCube_class, basedBEdge_positive]
  rfl

end FGModuleCat.SymbolMarking

end

end
