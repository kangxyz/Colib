/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Quillen.Automorphism.Universal
public import Colib.CategoryTheory.QConstruction.ObjectClass
public import Colib.CategoryTheory.ExactCategory.QSpanNaturality
public import Colib.Topology.ClassifyingSpace.UniversalComposition
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.FamilyCommutation
public import Colib.KTheory.Quillen.LowDegreeScalarAction.ExactNaturality
public import Colib.Topology.Realization.DoubleHomotopy
public import Colib.Topology.Homotopy.HomotopyGroup.SelfTrackLoopShift
public import Colib.Topology.Realization.DescAcross

/-!
# The actual biproduct braiding of zero-first Q-cone loop families

The split-conflation cones and their genuine composition homotopies produce
commutation over the entire core source. The actual braiding vertex track is
retained. No nullity of the object loop or stationarity of that track is used.
-/
/-! Implementation source: `Quillen/KTheory/LowDegreeScalarAction/BiproductLoopFamilies.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual cone paths,
composition triangles and categorical universes are preserved under native ownership. -/
@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology
open scoped Topology ZeroObject

universe u v w r

namespace CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies

section Topological
variable {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z] {x : X}

/-- Literal chronological concatenation of loop-valued source maps. -/
def concatenate (f g : C(Z, Path x x)) : C(Z, Path x x) where
  toFun z := (f z).trans (g z)
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (Path.trans_continuous_family f (Path.continuous_uncurry_iff.mpr (f).continuous)
      g (Path.continuous_uncurry_iff.mpr g.continuous))

/-- A common middle cone cancels over the entire source, not only at its vertices. -/
def middleConeCancellation {f : C(Z, X)}
    (A B C : (ContinuousMap.const Z x).Homotopy f) :
    (concatenate (ConePair.loopMap A B) (ConePair.loopMap B C)).Homotopy
      (ConePair.loopMap A C) := by
  refine (ConePair.commonTailCancellation A C B.symm).cast ?_ rfl
  apply ContinuousMap.ext
  intro z
  change ((A.trans B.symm).evalAt z).trans ((C.trans B.symm).evalAt z).symm =
    ((A.evalAt z).trans (B.evalAt z).symm).trans
      ((B.evalAt z).trans (C.evalAt z).symm)
  rw [ConePair.evalAt_trans, ConePair.evalAt_trans]
  change ((A.evalAt z).trans (B.evalAt z).symm).trans
    ((C.evalAt z).trans (B.evalAt z).symm).symm = _
  rw [Path.trans_symm, Path.symm_symm]

/-- Two whole-source loop homotopies can be pasted without discarding parameters. -/
def concatenateHomotopy {f₀ f₁ g₀ g₁ : C(Z, Path x x)}
    (H : f₀.Homotopy f₁) (K : g₀.Homotopy g₁) :
    (concatenate f₀ g₀).Homotopy (concatenate f₁ g₁) where
  toFun z := (H z).trans (K z)
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (Path.trans_continuous_family H (Path.continuous_uncurry_iff.mpr H.continuous)
      K (Path.continuous_uncurry_iff.mpr K.continuous))
  map_zero_left z := by rw [H.apply_zero, K.apply_zero]; rfl
  map_one_left z := by rw [H.apply_one, K.apply_one]; rfl

end Topological

section Categorical
variable {D : Type w} [Category.{r} D] {C : Type u} [Category.{v} C]
variable {X Y Z : D ⥤ C} {c : C}

/-- The three split-conflation cone identities supply actual additivity of the
entire loop family, with each composition triangle and cancellation retained. -/
def splitConeHomotopy
    (zX fX : (Functor.const D).obj c ⟶ X)
    (zY fY : (Functor.const D).obj c ⟶ Y)
    (zZ fZ : (Functor.const D).obj c ⟶ Z)
    (i : X ⟶ Y) (p : Z ⟶ Y)
    (hz : zX ≫ i = zY) (hf : fZ ≫ p = fY) (hm : fX ≫ i = zZ ≫ p) :
    (ConePair.naturalPair zY fY).Homotopy
      (concatenate (ConePair.naturalPair zX fX) (ConePair.naturalPair zZ fZ)) := by
  let middle := fX ≫ i
  let H := middleConeCancellation (ConePair.realizedCone zY)
    (ConePair.realizedCone middle) (ConePair.realizedCone fY)
  have HX : (ConePair.naturalPair zY middle).Homotopy (ConePair.naturalPair zX fX) := by
    rw [← hz]
    exact ConePair.naturalPairSuffixHomotopy zX fX i
  have HZ : (ConePair.naturalPair middle fY).Homotopy (ConePair.naturalPair zZ fZ) := by
    dsimp only [middle]
    rw [hm, ← hf]
    exact ConePair.naturalPairSuffixHomotopy zZ fZ p
  exact H.symm.trans (concatenateHomotopy HX HZ)

end Categorical

section Biproduct
variable {D : Type w} [Category.{r} D] {C : Type u} [Category.{v} C]
  [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C) (L R : D ⥤ Core C)
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The common categorical source acts on both summands simultaneously. -/
def biprodCore : D ⥤ Core C where
  obj d := Core.mk ((L.obj d).of ⊞ (R.obj d).of)
  map f := CoreHom.mk (biprod.mapIso (L.map f).iso (R.map f).iso)
  map_id d := by
    apply Core.hom_ext
    simp only [CategoryTheory.Functor.map_id, coreCategory_id_iso, biprod.mapIso_hom, Iso.refl_hom]
    apply biprod.hom_ext <;> simp
  map_comp f g := by
    apply Core.hom_ext
    simp only [Functor.map_comp, coreCategory_comp_iso, biprod.mapIso_hom, Iso.trans_hom]
    apply biprod.hom_ext <;> simp

/-- The Q-construction functor of the left core row. -/
def leftQ : D ⥤ E.QCategory := L ⋙ Automorphism.coreQ E
/-- The Q-construction functor of the right core row. -/
def rightQ : D ⥤ E.QCategory := R ⋙ Automorphism.coreQ E
/-- The Q-construction functor of the biproduct core row. -/
def sumQ : D ⥤ E.QCategory := biprodCore L R ⋙ Automorphism.coreQ E

/-- The actual admissible subobject Q-arrow, natural on the common source. -/
def splitInclusion : leftQ E L ⟶ sumQ E L R where
  app d := E.qInflation (biprod.inl : (L.obj d).of ⟶ (L.obj d).of ⊞ (R.obj d).of)
    (E.inflation_biprod_inl _ _)
  naturality {a b} f := by
    symm
    apply E.qSpan_iso_naturality _ _ (L.map f).iso
      (biprod.mapIso (L.map f).iso (R.map f).iso) (L.map f).iso
    · simp
    · simp

/-- The actual reverse quotient Q-arrow for that same split conflation. -/
def splitProjection : rightQ E R ⟶ sumQ E L R where
  app d := E.qDeflation (biprod.snd : (L.obj d).of ⊞ (R.obj d).of ⟶ (R.obj d).of)
    (E.deflation_of_conflation (E.conflation_biprod_inl_snd _ _))
  naturality {a b} f := by
    symm
    apply E.qSpan_iso_naturality _ _ (R.map f).iso
      (biprod.mapIso (L.map f).iso (R.map f).iso)
      (biprod.mapIso (L.map f).iso (R.map f).iso)
    · simp
    · simp

/-- The zero cone pulled back along the given core row. -/
def zeroCone (A : D ⥤ Core C) : (Functor.const D).obj E.qZero ⟶ A ⋙ Automorphism.coreQ E :=
  Functor.whiskerLeft A (Automorphism.zeroCone E)

/-- The full cone pulled back along the given core row. -/
def fullCone (A : D ⥤ Core C) : (Functor.const D).obj E.qZero ⟶ A ⋙ Automorphism.coreQ E :=
  Functor.whiskerLeft A (Automorphism.fullCone E)

/-- A simultaneous isomorphism of source diagrams keeps both canonical Q-cones. -/
def coreIsoLoopHomotopy (e : L ≅ R) :
    (ConePair.naturalPair (zeroCone E L) (fullCone E L)).Homotopy
      (ConePair.naturalPair (zeroCone E R) (fullCone E R)) := by
  let r := Functor.whiskerRight e.hom (Automorphism.coreQ E)
  have hz : zeroCone E L ≫ r = zeroCone E R := by
    apply NatTrans.ext
    funext d
    exact ((Automorphism.zeroCone E).naturality (e.hom.app d)).symm.trans
      (Category.id_comp _)
  have hf : fullCone E L ≫ r = fullCone E R := by
    apply NatTrans.ext
    funext d
    exact ((Automorphism.fullCone E).naturality (e.hom.app d)).symm.trans
      (Category.id_comp _)
  have H := ConePair.naturalPairSuffixHomotopy (zeroCone E L) (fullCone E L) r
  rw [hz, hf] at H
  exact H.symm

theorem zeroCone_splitInclusion :
    zeroCone E L ≫ splitInclusion E L R = zeroCone E (biprodCore L R) := by
  apply NatTrans.ext
  funext d
  exact E.fromZero_qInflation _ _

theorem fullCone_splitProjection :
    fullCone E R ≫ splitProjection E L R = fullCone E (biprodCore L R) := by
  apply NatTrans.ext
  funext d
  exact E.fromZeroTotal_qDeflation _ _

theorem split_middle_cone :
    fullCone E L ≫ splitInclusion E L R = zeroCone E R ≫ splitProjection E L R := by
  apply NatTrans.ext
  funext d
  exact (E.conflation_q_relation (E.conflation_biprod_inl_snd (L.obj d).of (R.obj d).of)).symm

/-- Entire canonical zero-first Q-cone loops split along the actual biproduct,
uniformly on every simplex and every loop coordinate of the common source. -/
def biprodCoreLoopHomotopy :
    (ConePair.naturalPair (zeroCone E (biprodCore L R))
      (fullCone E (biprodCore L R))).Homotopy
    (concatenate (ConePair.naturalPair (zeroCone E L) (fullCone E L))
      (ConePair.naturalPair (zeroCone E R) (fullCone E R))) :=
  splitConeHomotopy (zeroCone E L) (fullCone E L)
    (zeroCone E (biprodCore L R)) (fullCone E (biprodCore L R))
    (zeroCone E R) (fullCone E R) (splitInclusion E L R) (splitProjection E L R)
    (zeroCone_splitInclusion E L R) (fullCone_splitProjection E L R)
    (split_middle_cone E L R)


end Biproduct
end CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology
open scoped Topology ZeroObject

universe u v w r

namespace CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
open CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies

variable {D : Type w} [Category.{r} D] {C : Type u} [Category.{v} C]
  [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C) (L R : D ⥤ Core C)
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- The actual biproduct braiding acts simultaneously on the whole common source. -/
def biprodSwapIso : biprodCore L R ≅ biprodCore R L :=
  NatIso.ofComponents (fun d => Core.isoMk (biprod.braiding (L.obj d).of (R.obj d).of))
    (by
      intro a b f
      apply Core.hom_ext
      change biprod.map (L.map f).iso.hom (R.map f).iso.hom ≫
          (biprod.braiding (L.obj b).of (R.obj b).of).hom =
        (biprod.braiding (L.obj a).of (R.obj a).of).hom ≫
          biprod.map (R.map f).iso.hom (L.map f).iso.hom
      apply biprod.hom_ext <;> simp)

/-- The entire loop-family commutation homotopy retains the braiding's actual
vertex track. It makes no stationarity claim at the common source vertex. -/
def coreLoopCommutation :
    (concatenate
      (ConePair.naturalPair (zeroCone E L) (fullCone E L))
      (ConePair.naturalPair (zeroCone E R) (fullCone E R))).Homotopy
    (concatenate
      (ConePair.naturalPair (zeroCone E R) (fullCone E R))
      (ConePair.naturalPair (zeroCone E L) (fullCone E L))) :=
  (biprodCoreLoopHomotopy E L R).symm.trans
    ((coreIsoLoopHomotopy E (biprodCore L R) (biprodCore R L)
      (biprodSwapIso L R)).trans (biprodCoreLoopHomotopy E R L))


end CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology
open scoped Topology
namespace CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies
section SmallCore
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [Preadditive C] [HasFiniteBiproducts C] (E : ExactStructure C)

/-- Pulling back both actual cones realizes to the original core loop map. -/
theorem coreRowLoopMap (A : D ⥤ Core C) :
    ConePair.naturalPair (zeroCone E A) (fullCone E A) =
      (Automorphism.coreLoopMap E).comp (classifyingSpaceMap A).hom := by
  ext z t
  change (((ConePair.realizedCone (zeroCone E A)).evalAt z).trans
    ((ConePair.realizedCone (fullCone E A)).evalAt z).symm) t =
      ((Automorphism.conePath E (Automorphism.zeroCone E) (classifyingSpaceMap A z)).trans
        (Automorphism.conePath E (Automorphism.fullCone E) (classifyingSpaceMap A z)).symm) t
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact (universalHomotopy_whiskerLeft A (Automorphism.zeroCone E) _ z).trans
      (by rw [classifyingSpaceMapUniversal_eq A]; exact classifyingSpaceUniversalHomotopy_eq _ _ _)
  · exact (universalHomotopy_whiskerLeft A (Automorphism.fullCone E) _ z).trans
      (by rw [classifyingSpaceMapUniversal_eq A]; exact classifyingSpaceUniversalHomotopy_eq _ _ _)

/-- The constant-object row and identity core row supply the actual family
commutation, including the braiding's moving vertex. The object loop is not capped. -/
def constantCoreLoopCommutation (P : C) :
    (⟨fun z => (Automorphism.coreLoopMap E (classifyingSpacePoint (Core.mk P))).trans
      (Automorphism.coreLoopMap E z), by fun_prop⟩ :
        C(ClassifyingSpace (Core C), Path E.kBasepoint E.kBasepoint)).Homotopy
    ⟨fun z => (Automorphism.coreLoopMap E z).trans
      (Automorphism.coreLoopMap E (classifyingSpacePoint (Core.mk P))), by fun_prop⟩ := by
  have h := coreLoopCommutation E ((Functor.const (Core C)).obj (Core.mk P)) (𝟭 (Core C))
  simp only [coreRowLoopMap, classifyingSpaceMap_const_direct, classifyingSpaceMap_id] at h
  exact h

section Normalization
variable (P : C)
local notation "f" => Automorphism.coreLoopMap E
local notation "z" => classifyingSpacePoint (Core.mk P)

/-- The actual categorical family equates normalization orders with the supplied
original caps. No replacement or equality of differently parametrized caps is presumed. -/
theorem coreLoop_normalizationOrder
    (γ : Path ((f z).symm.trans (f z)) (Path.refl E.kBasepoint))
    (δ : Path ((f z).trans (f z).symm) (Path.refl E.kBasepoint))
    (a : HomotopyGroup.Pi 1 (ClassifyingSpace (Core C)) z) :
    (loopShiftMulEquiv 0).symm
      (pathTransport γ 1
        (HomotopyGroup.map
          (⟨fun w => (f w).symm.trans (f z),
            Path.continuous_trans.comp
              ((Path.continuous_symm.comp (f).continuous).prodMk continuous_const)⟩ :
            C(ClassifyingSpace (Core C), Path E.kBasepoint E.kBasepoint)) rfl a)) =
    (loopShiftMulEquiv 0).symm
      (pathTransport δ 1
        (HomotopyGroup.map
          (⟨fun w => (f z).trans (f w).symm,
            Path.continuous_trans.comp
              (continuous_const.prodMk (Path.continuous_symm.comp (f).continuous))⟩ :
            C(ClassifyingSpace (Core C), Path E.kBasepoint E.kBasepoint)) rfl a)) :=
  Topology.loopFamily_normalizationOrder _ _ (constantCoreLoopCommutation E P) γ δ a

end Normalization

/-- The actual categorical inverse-axis loop has its based cap at the double
object loop, with no nullity premise and no stationarity assumption. -/
def coreLoopInverseAxisCap (P : C)
    (δ : Path (classifyingSpacePoint (Core.mk P)) (classifyingSpacePoint (Core.mk P))) :
    (((δ.map (Automorphism.coreLoopMap E).continuous).prod
      (δ.map (Automorphism.coreLoopMap E).continuous).symm).map
        Path.continuous_trans).Homotopy
      (Path.refl ((Automorphism.coreLoopMap E (classifyingSpacePoint (Core.mk P))).trans
        (Automorphism.coreLoopMap E (classifyingSpacePoint (Core.mk P))))) :=
  Topology.loopFamilyInverseAxisCap _ _ (constantCoreLoopCommutation E P) δ

end SmallCore
end CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies

universe v w

section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology SSet
open MonoidalCategory CartesianMonoidalCategory
open scoped ZeroObject Simplicial Topology unitInterval
namespace CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies.Equivariance

private theorem ordinalInterchange
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X))
    {X Y : C} (f : X ⟶ Y) (a b c d : Fin 2) (hab : a ≤ b) (hcd : c ≤ d) :
    HEq
      (((ComposableArrows.mk₁ η).map (homOfLE hcd)).app
          (((ComposableArrows.mk₁ α).obj a).obj X) ≫
        ((ComposableArrows.mk₁ η).obj d).map
          (((ComposableArrows.mk₁ α).map (homOfLE hab)).app X ≫
            ((ComposableArrows.mk₁ α).obj b).map f))
      (((ComposableArrows.mk₁ β).map (homOfLE hab)).app
          (((ComposableArrows.mk₁ η).obj c).obj X) ≫
        ((ComposableArrows.mk₁ β).obj b).map
          (((ComposableArrows.mk₁ η).map (homOfLE hcd)).app X ≫
            ((ComposableArrows.mk₁ η).obj d).map f)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals try exact ((by decide : ¬ (1 : Fin 2) ≤ 0) hab).elim
  all_goals try exact ((by decide : ¬ (1 : Fin 2) ≤ 0) hcd).elim
  all_goals
    simp_all only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ComposableArrows.mk₁_obj,
      ComposableArrows.Mk₁.obj, Functor.id_obj, Fin.mk_one, homOfLE_leOfHom,
      ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map, Functor.id_map, Functor.map_comp,
      heq_eq_eq, NatTrans.id_app, Category.id_comp]
  exact β.naturality_assoc (η.app X) (G.map f)

private theorem nerveInterchange
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X)) :
    naturalTransformationNerveCylinder α ▷ Δ[1] ≫
        naturalTransformationNerveCylinder η =
      simplicialCylinderSwap (nerve C) ≫ naturalTransformationNerveCylinder η ▷ Δ[1] ≫
        naturalTransformationNerveCylinder β := by
  ext n z
  change
    (z.2.down.toOrderHom.monotone.functor.prod'
      ((z.1.2.down.toOrderHom.monotone.functor.prod' z.1.1) ⋙
        naturalTransformationCylinderFunctor α)) ⋙
      naturalTransformationCylinderFunctor η =
    (z.1.2.down.toOrderHom.monotone.functor.prod'
      ((z.2.down.toOrderHom.monotone.functor.prod' z.1.1) ⋙
        naturalTransformationCylinderFunctor η)) ⋙
      naturalTransformationCylinderFunctor β
  refine CategoryTheory.Functor.hext (fun p => ?_) ?_
  · dsimp [naturalTransformationNerveCylinder, naturalTransformationCylinderFunctor,
      Functor.uncurry, Functor.prod', simplicialCylinderSwap]
    generalize hτ : z.1.2.down.toOrderHom p = t
    generalize hθ : z.2.down.toOrderHom p = s
    fin_cases t <;> fin_cases s <;> rfl
  · intro p q f
    exact ordinalInterchange η α β hF hG (z.1.1.map f)
      (z.1.2.down.toOrderHom p) (z.1.2.down.toOrderHom q)
      (z.2.down.toOrderHom p) (z.2.down.toOrderHom q)
      (z.1.2.down.toOrderHom.monotone (leOfHom f))
      (z.2.down.toOrderHom.monotone (leOfHom f))

/-- The actual two-time nerve square gives the whole realized interchange. -/
theorem homotopyInterchange
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (η : F ⟶ G) (α : 𝟭 C ⟶ 𝟭 C) (β : 𝟭 D ⟶ 𝟭 D)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X))
    (s t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy η
        (s, classifyingSpaceNaturalTransformationHomotopy α (t, x)) =
      classifyingSpaceNaturalTransformationHomotopy β
        (t, classifyingSpaceNaturalTransformationHomotopy η (s, x)) :=
  realizationSimplicialHomotopy_interchange
    (naturalTransformationNerveHomotopy η) (naturalTransformationNerveHomotopy α)
    (naturalTransformationNerveHomotopy η) (naturalTransformationNerveHomotopy β)
    (nerveInterchange η α β hF hG) s t x

variable {C : Type (max u v)} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The action of an identity-functor automorphism on the core category. -/
def identityCoreAction (u : 𝟭 C ≅ 𝟭 C) : 𝟭 (Core C) ⟶ 𝟭 (Core C) where
  app A := CoreHom.mk (u.app A.of)
  naturality {A B} f := by
    apply Core.hom_ext
    exact u.hom.naturality f.iso.hom


end CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies.Equivariance
end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory SSet Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
namespace CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies.Cylinder

/- The four naturality proofs retain the original nerve-cylinder argument
from TheoremB/Naturality, with independent object and morphism universes. -/
/-- The categorical nerve-cylinder construction commutes with precomposition. -/
theorem naturalTransformationNerveCylinder_whiskerLeft
    {A C D : Type u} [Category.{v} A] [Category.{v} C] [Category.{v} D]
    (K : A ⥤ C) {F G : C ⥤ D} (α : F ⟶ G) :
    naturalTransformationNerveCylinder (Functor.whiskerLeft K α) =
      nerveMap K ▷ Δ[1] ≫ naturalTransformationNerveCylinder α := by
  have hc : naturalTransformationCylinderFunctor (Functor.whiskerLeft K α) =
      (𝟭 (Fin 2)).prod K ⋙ naturalTransformationCylinderFunctor α := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ rfl rfl ?_
    ext a
    simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
      ComposableArrows.mk₁, ComposableArrows.hom]
  ext n z
  change _ ⋙ naturalTransformationCylinderFunctor (Functor.whiskerLeft K α) =
    _ ⋙ naturalTransformationCylinderFunctor α
  rw [hc]
  rfl

/-- The categorical nerve-cylinder construction commutes with postcomposition. -/
theorem naturalTransformationNerveCylinder_whiskerRight
    {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    {F G : C ⥤ D} (α : F ⟶ G) (K : D ⥤ E) :
    naturalTransformationNerveCylinder (Functor.whiskerRight α K) =
      naturalTransformationNerveCylinder α ≫ nerveMap K := by
  have hc : naturalTransformationCylinderFunctor (Functor.whiskerRight α K) =
      naturalTransformationCylinderFunctor α ⋙ K := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ ?_ ?_ ?_
    · refine CategoryTheory.Functor.ext (fun a ↦ rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁]
    · refine CategoryTheory.Functor.ext (fun a ↦ rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁]
    · ext a
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj, Functor.uncurry,
        ComposableArrows.mk₁, ComposableArrows.hom]
  ext n z
  change _ ⋙ naturalTransformationCylinderFunctor (Functor.whiskerRight α K) =
    (_ ⋙ naturalTransformationCylinderFunctor α) ⋙ K
  rw [hc]
  rfl

/-- Precomposing a natural transformation precomposes its actual realized homotopy. -/
theorem classifyingSpaceNaturalTransformationHomotopy_whiskerLeft
    {A C D : Type u} [Category.{v} A] [Category.{v} C] [Category.{v} D]
    (K : A ⥤ C) {F G : C ⥤ D} (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerLeft K α) (t, x) =
      classifyingSpaceNaturalTransformationHomotopy α (t, classifyingSpaceMap K x) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (Functor.whiskerLeft K α))
    ((realizationCylinderIso (nerve A)).inv (x, ULift.up t)) = _
  rw [naturalTransformationNerveCylinder_whiskerLeft, Functor.map_comp, TopCat.comp_app]
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality (nerveMap K)) (x, ULift.up t)
  exact congrArg (SSet.toTop.map (naturalTransformationNerveCylinder α)) hn

/-- Postcomposing a natural transformation postcomposes its actual realized homotopy. -/
theorem classifyingSpaceNaturalTransformationHomotopy_whiskerRight
    {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    {F G : C ⥤ D} (α : F ⟶ G) (K : D ⥤ E)
    (t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerRight α K) (t, x) =
      classifyingSpaceMap K (classifyingSpaceNaturalTransformationHomotopy α (t, x)) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (Functor.whiskerRight α K))
    ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)) = _
  rw [naturalTransformationNerveCylinder_whiskerRight, Functor.map_comp, TopCat.comp_app]
  rfl


/-- The identity cylinder is the literal projection at every simplex. -/
theorem identity_cylinder {C : Type u} [Category.{v} C] :
    naturalTransformationNerveCylinder (𝟙 (𝟭 C)) = fst (nerve C) Δ[1] := by
  have hc : naturalTransformationCylinderFunctor (𝟙 (𝟭 C)) =
      CategoryTheory.Prod.snd (Fin 2) C := by
    apply Functor.curry_obj_injective
    refine ComposableArrows.ext₁ ?_ ?_ ?_
    · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
        Functor.uncurry, ComposableArrows.mk₁]
    · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
        Functor.uncurry, ComposableArrows.mk₁]
    · ext X
      simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
        Functor.uncurry, ComposableArrows.mk₁, ComposableArrows.hom]
  ext n z
  change _ ⋙ naturalTransformationCylinderFunctor (𝟙 (𝟭 C)) = z.1
  rw [hc]
  rfl

/-- The identity transformation has the actual stationary realized track. -/
theorem identity_track {C : Type u} [Category.{v} C]
    (t : unitInterval) (z : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy (𝟙 (𝟭 C)) (t,z) = z := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (𝟙 (𝟭 C)))
    ((realizationCylinderIso (nerve C)).inv (z,ULift.up t)) = z
  rw [identity_cylinder]
  exact congrArg _root_.Prod.fst (ConcreteCategory.congr_hom
    (realizationCylinderIso (nerve C)).inv_hom_id (z,ULift.up t))

end CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies.Cylinder

end

section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite SSet
open scoped Simplicial Topology unitInterval
namespace CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies.Promotion

/-- The actual universe-up cylinder map descends on the original paired simplices.
The interval simplex and its barycentric coordinates are unchanged. -/
private def cylinderMapUp (C : Type u) [Category.{v} C] :
    C(|nerve C ⊗ (Δ[1] : SSet.{max u v})|,
      |nerve (AsSmall.{max u v w} C) ⊗ (Δ[1] : SSet.{max u v w})|) :=
  realizationDesc
    (fun n x => realizationSimplex
      (X := nerve (AsSmall.{max u v w} C) ⊗ (Δ[1] : SSet.{max u v w}))
      (n := n) (x.1 ⋙ AsSmall.up, ULift.up x.2.down)) (by
      intro n m a x t
      exact realizationSimplex_naturality
        (X := nerve (AsSmall.{max u v w} C) ⊗ (Δ[1] : SSet.{max u v w}))
        a (x.1 ⋙ AsSmall.up, ULift.up x.2.down) t)

private theorem cylinderMapUp_simplex (C : Type u) [Category.{v} C]
    (n : SimplexCategory) (x : (nerve C ⊗ (Δ[1] : SSet.{max u v})).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    cylinderMapUp.{u,v,w} C (realizationSimplex x t) =
      realizationSimplex (X := nerve (AsSmall.{max u v w} C) ⊗ Δ[1])
        (x.1 ⋙ AsSmall.up, ULift.up x.2.down) t := by
  unfold cylinderMapUp
  exact realizationDesc_simplex _ (by
    intro n m a x t
    exact realizationSimplex_naturality
      (X := nerve (AsSmall.{max u v w} C) ⊗ (Δ[1] : SSet.{max u v w}))
      a (x.1 ⋙ AsSmall.up, ULift.up x.2.down) t) n x t

/-- An ordinary realization map preserves the characteristic map of each simplex. -/
private theorem realizationMap_simplex {X Y : SSet.{u}} (f : X ⟶ Y) (n : SimplexCategory)
    (x : X.obj (op n)) (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    SSet.toTop.map f (realizationSimplex x t) = realizationSimplex (f.app (op n) x) t := by
  change (SSet.toTop.map (SSet.yonedaEquiv.symm x) ≫ SSet.toTop.map f)
    ((SimplexCategory.toTopHomeo n).symm t) = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

/-- The actual interval coordinate is independent of its ambient universe. -/
private theorem intervalCoordinate_simplex (n : SimplexCategory)
    (a : (Δ[1] : SSet.{u}).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    (SSet.stdSimplex.toTopObjIsoI.hom (realizationSimplex a t)).down =
      Convexity.StdSimplex.homeomorphI (Convexity.StdSimplex.map a.down.toOrderHom t) := by
  have ha : SSet.yonedaEquiv.symm a = SSet.stdSimplex.map a.down := by
    ext m b
    rfl
  change (SSet.stdSimplex.toTopObjIsoI.hom
    (SSet.toTop.map (SSet.yonedaEquiv.symm a) ((SimplexCategory.toTopHomeo n).symm t))).down = _
  rw [ha]
  change Convexity.StdSimplex.homeomorphI (SimplexCategory.toTopHomeo ⦋1⦌
    (SSet.toTop.map (SSet.stdSimplex.map a.down) ((SimplexCategory.toTopHomeo n).symm t))) = _
  rw [SimplexCategory.toTopHomeo_naturality_apply, Homeomorph.apply_symm_apply]
  rfl

/-- Both original cylinder projections survive the actual universe-up map. -/
private theorem cylinderComparison_up (C : Type u) [Category.{v} C]
    (z : |nerve C ⊗ (Δ[1] : SSet.{max u v})|) :
    (realizationCylinderIso (nerve (AsSmall.{max u v w} C))).hom
        (cylinderMapUp.{u,v,w} C z) =
      (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v w} C)
        ((realizationCylinderIso (nerve C)).hom z).1,
        ULift.up (((realizationCylinderIso (nerve C)).hom z).2.down)) := by
  have h : (fun z : |nerve C ⊗ (Δ[1] : SSet.{max u v})| =>
      (realizationCylinderIso (nerve (AsSmall.{max u v w} C))).hom
        (cylinderMapUp.{u,v,w} C z)) =
    (fun z : |nerve C ⊗ (Δ[1] : SSet.{max u v})| =>
      (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v w} C)
        ((realizationCylinderIso (nerve C)).hom z).1,
        ULift.up (((realizationCylinderIso (nerve C)).hom z).2.down))) := by
    apply realization_ext
    intro n x t
    rw [cylinderMapUp_simplex]
    apply Prod.ext
    · change SSet.toTop.map (fst (nerve (AsSmall.{max u v w} C)) Δ[1])
        (realizationSimplex (x.1 ⋙ AsSmall.up, ULift.up x.2.down) t) =
      classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v w} C)
        (SSet.toTop.map (fst (nerve C) Δ[1]) (realizationSimplex x t))
      rw [realizationMap_simplex, realizationMap_simplex, classifyingSpaceMapUniversal_simplex]
      rfl
    · apply ULift.ext
      change (SSet.stdSimplex.toTopObjIsoI.hom
        (SSet.toTop.map (snd (nerve (AsSmall.{max u v w} C)) Δ[1])
          (realizationSimplex (x.1 ⋙ AsSmall.up, ULift.up x.2.down) t))).down =
        (SSet.stdSimplex.toTopObjIsoI.hom
          (SSet.toTop.map (snd (nerve C) Δ[1]) (realizationSimplex x t))).down
      rw [realizationMap_simplex, realizationMap_simplex,
        intervalCoordinate_simplex, intervalCoordinate_simplex]
      rfl
  exact congrFun h z

/-- The original inverse cylinder retains its entire time coordinate under universe lifting. -/
private theorem cylinderInverse_up (C : Type u) [Category.{v} C]
    (x : ClassifyingSpace C) (t : unitInterval) :
    cylinderMapUp.{u,v,w} C ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)) =
      (realizationCylinderIso (nerve (AsSmall.{max u v w} C))).inv
        (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v w} C) x, ULift.up t) := by
  apply (TopCat.homeoOfIso (realizationCylinderIso (nerve (AsSmall.{max u v w} C)))).injective
  change (realizationCylinderIso (nerve (AsSmall.{max u v w} C))).hom _ =
    (realizationCylinderIso (nerve (AsSmall.{max u v w} C))).hom _
  rw [cylinderComparison_up]
  have hx := ConcreteCategory.congr_hom
    (realizationCylinderIso (nerve C)).inv_hom_id (x, ULift.up t)
  have hy := ConcreteCategory.congr_hom
    (realizationCylinderIso (nerve (AsSmall.{max u v w} C))).inv_hom_id
      (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v w} C) x, ULift.up t)
  change (realizationCylinderIso (nerve C)).hom
    ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)) = (x, ULift.up t) at hx
  change (realizationCylinderIso (nerve (AsSmall.{max u v w} C))).hom
    ((realizationCylinderIso (nerve (AsSmall.{max u v w} C))).inv
      (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v w} C) x, ULift.up t)) =
    (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v w} C) x, ULift.up t) at hy
  rw [hx, hy]

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The original natural transformation with both categorical universes lifted. -/
def liftTransformation {F G : C ⥤ D} (α : F ⟶ G) :
    (AsSmall.down : AsSmall.{max u v w} C ⥤ C) ⋙ F ⋙
        (AsSmall.up : D ⥤ AsSmall.{max u v w} D) ⟶
      (AsSmall.down : AsSmall.{max u v w} C ⥤ C) ⋙ G ⋙
        (AsSmall.up : D ⥤ AsSmall.{max u v w} D) :=
  Functor.whiskerLeft AsSmall.down (Functor.whiskerRight α AsSmall.up)

private theorem liftedCylinderFunctorSquare {F G : C ⥤ D} (α : F ⟶ G) :
    ((𝟭 (Fin 2)).prod (AsSmall.up : C ⥤ AsSmall.{max u v w} C)) ⋙
      naturalTransformationCylinderFunctor (liftTransformation.{u,v,w} α) =
    naturalTransformationCylinderFunctor α ⋙ (AsSmall.up : D ⥤ AsSmall.{max u v w} D) := by
  apply Functor.curry_obj_injective
  refine ComposableArrows.ext₁ rfl rfl ?_
  ext a
  apply ULift.ext
  simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
    Functor.uncurry, ComposableArrows.mk₁, ComposableArrows.hom,
    liftTransformation, AsSmall.down, AsSmall.up, down_comp]

private theorem naturalCylinder_lift_map {F G : C ⥤ D} (α : F ⟶ G) :
    (classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v w} D)).comp
      (SSet.toTop.map (naturalTransformationNerveCylinder α)).hom =
    (SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v,w} α))).hom.comp
      (cylinderMapUp.{u,v,w} C) := by
  apply DFunLike.coe_injective
  apply realization_ext
  intro n z t
  change classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v w} D)
      (SSet.toTop.map (naturalTransformationNerveCylinder α) (realizationSimplex z t)) =
    SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v,w} α))
      (cylinderMapUp.{u,v,w} C (realizationSimplex z t))
  rw [realizationMap_simplex, classifyingSpaceMapUniversal_simplex,
    cylinderMapUp_simplex, realizationMap_simplex]
  apply congrArg (fun b => realizationSimplex b t)
  change (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
      (naturalTransformationCylinderFunctor α ⋙ AsSmall.up) =
    (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
      (((𝟭 (Fin 2)).prod (AsSmall.up : C ⥤ AsSmall.{max u v w} C)) ⋙
        naturalTransformationCylinderFunctor (liftTransformation.{u,v,w} α))
  rw [liftedCylinderFunctorSquare]

/-- Lifting preserves the entire original natural-transformation homotopy and its time. -/
theorem naturalTransformationHomotopy_up {F G : C ⥤ D} (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy (liftTransformation.{u,v,w} α)
      (t,classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v w} C) x) =
    classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v w} D)
      (classifyingSpaceNaturalTransformationHomotopy α (t,x)) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v,w} α))
      ((realizationCylinderIso (nerve (AsSmall.{max u v w} C))).inv
        (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v w} C) x, ULift.up t)) =
    classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v w} D)
      (SSet.toTop.map (naturalTransformationNerveCylinder α)
        ((realizationCylinderIso (nerve C)).inv (x,ULift.up t)))
  rw [← cylinderInverse_up]
  exact (ContinuousMap.congr_fun (naturalCylinder_lift_map.{u,v,w} α)
    ((realizationCylinderIso (nerve C)).inv (x,ULift.up t))).symm

/-- The universal construction is the same whole cylinder in mixed categorical universes. -/
theorem universal_eq {F G : C ⥤ D} (α : F ⟶ G)
    (t : unitInterval) (z : ClassifyingSpace C) :
    classifyingSpaceUniversalHomotopy α (t,z) =
      classifyingSpaceNaturalTransformationHomotopy α (t,z) := by
  change classifyingSpaceMapUniversal (AsSmall.down : AsSmall.{max u v} D ⥤ D)
    (classifyingSpaceNaturalTransformationHomotopy (liftTransformation.{u,v,0} α)
      (t,classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v} C) z)) = _
  rw [naturalTransformationHomotopy_up]
  change ((classifyingSpaceMapUniversal (AsSmall.down : AsSmall.{max u v} D ⥤ D)).comp
    (classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v} D))) _ = _
  rw [← classifyingSpaceMapUniversal_comp]
  change classifyingSpaceMapUniversal (𝟭 D) _ = _
  rw [classifyingSpaceMapUniversal_id]
  rfl

end CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies.Promotion
end

section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology SSet
open MonoidalCategory CartesianMonoidalCategory
open scoped ZeroObject Simplicial Topology unitInterval
namespace CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies.Equivariance

/-- The original two-time interchange in the full common upper universe. -/
theorem universalInterchange
    {A : Type u} [Category.{v} A] {B : Type (max u v w)} [SmallCategory B]
    {F G : A ⥤ B} (η : F ⟶ G) (α : 𝟭 A ⟶ 𝟭 A) (β : 𝟭 B ⟶ 𝟭 B)
    (hF : ∀ X, F.map (α.app X) = β.app (F.obj X))
    (hG : ∀ X, G.map (α.app X) = β.app (G.obj X))
    (s t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceUniversalHomotopy η
        (s, classifyingSpaceUniversalHomotopy α (t, x)) =
      classifyingSpaceNaturalTransformationHomotopy β
        (t, classifyingSpaceUniversalHomotopy η (s, x)) := by
  let U : A ⥤ AsSmall.{max u v w} A := AsSmall.up
  let V : AsSmall.{max u v w} A ⥤ A := AsSmall.down
  let η' := Functor.whiskerLeft V η
  let α' : 𝟭 (AsSmall.{max u v w} A) ⟶ 𝟭 (AsSmall.{max u v w} A) :=
    Functor.whiskerLeft V (Functor.whiskerRight α U)
  have hU (z : ClassifyingSpace A) (r : unitInterval) :
      classifyingSpaceNaturalTransformationHomotopy α'
          (r, classifyingSpaceMapUniversal U z) =
        classifyingSpaceMapUniversal U (classifyingSpaceUniversalHomotopy α (r,z)) := by
    rw [Promotion.universal_eq]
    exact Promotion.naturalTransformationHomotopy_up.{u, v, w} α r z
  have hη (z : ClassifyingSpace A) (r : unitInterval) :
      classifyingSpaceNaturalTransformationHomotopy η'
          (r, classifyingSpaceMapUniversal U z) =
        classifyingSpaceUniversalHomotopy η (r,z) := by
    rw [← classifyingSpaceUniversalHomotopy_eq, ← universalHomotopy_whiskerLeft U]
    rfl
  have hh := homotopyInterchange η' α' β
    (fun X => hF (V.obj X)) (fun X => hG (V.obj X))
    s t (classifyingSpaceMapUniversal U x)
  rw [hU, hη, hη] at hh
  exact hh

variable {C : Type (max u v)} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Both cone time and automorphism time survive on every point of the full core source. -/
theorem wholeConeInterchange (u : 𝟭 C ≅ 𝟭 C)
    (η : (Functor.const (Core C)).obj E.qZero ⟶ Automorphism.coreQ E)
    (z : ClassifyingSpace (Core C)) (s t : unitInterval) :
    IdentityAutomorphism.homotopy E u
        (t, classifyingSpaceUniversalHomotopy η (s, z)) =
      classifyingSpaceUniversalHomotopy η
        (s, classifyingSpaceUniversalHomotopy (identityCoreAction u) (t, z)) := by
  let α := identityCoreAction u
  let β := (IdentityAutomorphism.identityQAut E u).hom
  have hF (A : Core C) :
      ((Functor.const (Core C)).obj E.qZero).map (α.app A) = β.app E.qZero := by
    apply @Subsingleton.elim _
      (E.qHom_subsingleton_of_isZero E.qZero E.qZero (isZero_zero C))
  have hG (A : Core C) : (Automorphism.coreQ E).map (α.app A) =
      β.app ((Automorphism.coreQ E).obj A) := rfl
  exact (IdentityAutomorphism.identityQAut_homotopy E u t _).symm.trans
    (universalInterchange η α β hF hG s t z).symm

/-- The entire original core loop is equivariant for the actual normalized scalar track. -/
theorem wholeCoreLoopInterchange (u : 𝟭 C ≅ 𝟭 C)
    (z : ClassifyingSpace (Core C)) (s t : unitInterval) :
    IdentityAutomorphism.homotopy E u (t, Automorphism.universalCoreLoopMap E z s) =
      Automorphism.universalCoreLoopMap E
        (classifyingSpaceUniversalHomotopy (identityCoreAction u) (t, z)) s := by
  change IdentityAutomorphism.homotopy E u
      (t, ((ConePair.realizedCone (Automorphism.zeroCone E)).evalAt z).trans
        ((ConePair.realizedCone (Automorphism.fullCone E)).evalAt z).symm s) =
    ((ConePair.realizedCone (Automorphism.zeroCone E)).evalAt
      (classifyingSpaceUniversalHomotopy (identityCoreAction u) (t,z))).trans
        ((ConePair.realizedCone (Automorphism.fullCone E)).evalAt
          (classifyingSpaceUniversalHomotopy (identityCoreAction u) (t,z))).symm s
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact wholeConeInterchange E u (Automorphism.zeroCone E) z _ t
  · exact wholeConeInterchange E u (Automorphism.fullCone E) z _ t

/-- The precise inverse sign needed when the scalar operation is compared in loop space. -/
theorem originalScalar_loopShift (u : 𝟭 C ≅ 𝟭 C) (a : E.K 1) :
    (loopShiftMulEquiv (x := E.kBasepoint) 1).symm
      (IdentityTrack.operation
        (IdentityTrack.loopedHomotopy (IdentityAutomorphism.homotopy E u).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E u))
        (IdentityTrack.loopedHomotopy_based (IdentityAutomorphism.homotopy E u).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E u)) 0
        (loopShiftMulEquiv 0 a)) = (IdentityAutomorphism.kOneAction E u a)⁻¹ :=
  IdentityTrack.operation_loopShift_symm (IdentityAutomorphism.homotopy E u).toHomotopy
    (IdentityAutomorphism.homotopy_fixed E u) a

end CategoryTheory.ExactCategory.LowDegreeScalarAction.BiproductLoopFamilies.Equivariance

end
