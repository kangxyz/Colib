/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Localization.Lifts
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import Mathlib.CategoryTheory.Subobject.Lattice

/-! # Subobjects and intervals in Serre localizations

Adapted from Quillen/Aglib/CategoryTheory/Abelian/SerreClass/Lifts.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Uses the pinned upstream exactness
and fraction calculus, retaining actual ambient arrows and subobjects.
-/

@[expose] public noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.SerreLocalization
open CategoryTheory.Localization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (L : C ⥤ D) (V : D)

section Serre

variable [Abelian C] [Preadditive D]
  (P : ObjectProperty C) [P.IsSerreClass] [L.IsLocalization P.isoModSerre] [L.Additive]
include P

/-- For a Serre quotient, compatibility forces every lift arrow to have kernel
and cokernel in the Serre class. -/
theorem auxiliaryLift_hom_isoModSerre {X Y : AuxiliaryLift L V} (f : X ⟶ Y) :
    P.isoModSerre f.hom.left :=
  (ObjectProperty.SerreClassLocalization.isIso_map_iff L P _).1 inferInstance

omit [Preadditive D] [L.Additive] in
/-- No extra filtering assumption is needed for the lift category of a Serre
quotient: both fraction calculi were constructed from the Serre hypotheses. -/
theorem serreAuxiliaryLift_isFiltered : IsFiltered (AuxiliaryLift L V) :=
  auxiliaryLift_isFiltered L V P.isoModSerre

omit [Preadditive D] [L.Additive] in
theorem serreAuxiliaryLift_isCofiltered : IsCofiltered (AuxiliaryLift L V) :=
  auxiliaryLift_isCofiltered L V P.isoModSerre

end Serre

section SubobjectSum

variable [Abelian C]

/-- The two inclusions into the join of abelian subobjects are jointly epic.
This elementary least-upper-bound argument avoids depending on a particular
chosen image presentation of the join. -/
theorem subobject_sup_desc_epi {M : C} (A B : Subobject M) :
    Epi (biprod.desc (Subobject.ofLE A (A ⊔ B) le_sup_left)
      (Subobject.ofLE B (A ⊔ B) le_sup_right)) := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro T g h
  have ha : Subobject.ofLE A (A ⊔ B) le_sup_left ≫ g = 0 := by
    have hh := congrArg (fun k => biprod.inl ≫ k) h
    simpa [Category.assoc] using hh
  have hb : Subobject.ofLE B (A ⊔ B) le_sup_right ≫ g = 0 := by
    have hh := congrArg (fun k => biprod.inr ≫ k) h
    simpa [Category.assoc] using hh
  let K : Subobject M := Subobject.mk (kernel.ι g ≫ (A ⊔ B).arrow)
  have hle : A ⊔ B ≤ K := by
    apply sup_le
    · apply Subobject.le_mk_of_comm (kernel.lift g (Subobject.ofLE A (A ⊔ B) le_sup_left) ha)
      simp
    · apply Subobject.le_mk_of_comm (kernel.lift g (Subobject.ofLE B (A ⊔ B) le_sup_right) hb)
      simp
  let r := Subobject.ofLE (A ⊔ B) K hle ≫
    (Subobject.underlyingIso (kernel.ι g ≫ (A ⊔ B).arrow)).hom
  have hr : r ≫ kernel.ι g = 𝟙 ((A ⊔ B : Subobject M) : C) := by
    apply (cancel_mono (A ⊔ B).arrow).1
    simp [r, K, Category.assoc]
  calc
    g = (r ≫ kernel.ι g) ≫ g := by rw [hr, Category.id_comp]
    _ = 0 := by simp

end SubobjectSum

section SubobjectLifting

variable [Abelian C] [Abelian D]
  (P : ObjectProperty C) [P.IsSerreClass] [L.IsLocalization P.isoModSerre] [L.Additive]
include P

/-- A quotient subobject of an actual localized object is represented by an
ambient subobject of that same object. The target is held fixed, unlike a
general arrow-isomorphism presentation of quotient monomorphisms. -/
theorem exists_mono_lift {M : C} {V : D} (i : V ⟶ L.obj M) [Mono i] :
    ∃ (N : C) (j : N ⟶ M) (_ : Mono j) (e : L.obj N ≅ V), L.map j = e.hom ≫ i := by
  have := Localization.essSurj L P.isoModSerre
  have := ObjectProperty.SerreClassLocalization.preservesEpimorphisms L P
  let e₀ := L.objObjPreimageIso V
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.isoModSerre (e₀.hom ≫ i)
  have hf : L.map φ.f = L.map φ.s ≫ e₀.hom ≫ i := by
    have h := congrArg (fun k => L.map φ.s ≫ k) hφ
    simpa [MorphismProperty.RightFraction.map, Category.assoc] using h.symm
  have : Mono (L.map φ.f) := by rw [hf]; infer_instance
  have : Mono (L.map (Abelian.factorThruImage φ.f)) :=
    mono_of_mono_fac (by rw [← L.map_comp, Abelian.image.fac])
  have : IsIso (L.map (Abelian.factorThruImage φ.f)) := isIso_of_mono_of_epi _
  let e : L.obj (Abelian.image φ.f) ≅ V :=
    (asIso (L.map (Abelian.factorThruImage φ.f))).symm ≪≫ asIso (L.map φ.s) ≪≫ e₀
  refine ⟨Abelian.image φ.f, Abelian.image.ι φ.f, inferInstance, e, ?_⟩
  apply (cancel_epi (L.map (Abelian.factorThruImage φ.f))).1
  change L.map (Abelian.factorThruImage φ.f) ≫ L.map (Abelian.image.ι φ.f) =
    L.map (Abelian.factorThruImage φ.f) ≫
      (inv (L.map (Abelian.factorThruImage φ.f)) ≫ L.map φ.s ≫ e₀.hom) ≫ i
  simpa only [← L.map_comp, Abelian.image.fac, Category.assoc, IsIso.hom_inv_id_assoc]
    using hf

/-- Dually, every quotient of `L(M)` lifts to an actual quotient of the same
ambient object `M`, with its quotient identification fixed explicitly. -/
theorem exists_epi_lift {M : C} {V : D} (p : L.obj M ⟶ V) [Epi p] :
    ∃ (N : C) (j : M ⟶ N) (_ : Epi j) (e : L.obj N ≅ V), L.map j ≫ e.hom = p := by
  have := Localization.essSurj L P.isoModSerre
  have := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  let e₀ := L.objObjPreimageIso V
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.isoModSerre (p ≫ e₀.inv)
  have hf : L.map φ.f = p ≫ e₀.inv ≫ L.map φ.s := by
    have h := congrArg (fun k => k ≫ L.map φ.s) hφ
    simpa [MorphismProperty.LeftFraction.map, Category.assoc] using h.symm
  have : Epi (L.map φ.f) := by rw [hf]; infer_instance
  have : Epi (L.map (Abelian.image.ι φ.f)) :=
    epi_of_epi_fac (by rw [← L.map_comp, Abelian.image.fac])
  have : IsIso (L.map (Abelian.image.ι φ.f)) := isIso_of_mono_of_epi _
  let e : L.obj (Abelian.image φ.f) ≅ V :=
    asIso (L.map (Abelian.image.ι φ.f)) ≪≫ (asIso (L.map φ.s)).symm ≪≫ e₀
  refine ⟨Abelian.image φ.f, Abelian.factorThruImage φ.f, inferInstance, e, ?_⟩
  change L.map (Abelian.factorThruImage φ.f) ≫
    L.map (Abelian.image.ι φ.f) ≫ inv (L.map φ.s) ≫ e₀.hom = p
  rw [← Category.assoc, ← L.map_comp, Abelian.image.fac, hf]
  simp

/-- The monotone map on subobjects induced by the exact Serre quotient. -/
@[implicit_reducible]
def subobjectMap (M : C) : Subobject M →o Subobject (L.obj M) := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  exact
    { toFun := fun A => Subobject.mk (L.map A.arrow)
      monotone' := fun A B h => Subobject.mk_le_mk_of_comm
        (L.map (Subobject.ofLE A B h)) (by simp [← L.map_comp]) }

@[simp]
theorem subobjectMap_mk {M N : C} (j : N ⟶ M) [Mono j] :
    let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
    subobjectMap L P M (Subobject.mk j) = Subobject.mk (L.map j) := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  apply Subobject.mk_eq_mk_of_comm _ _ (L.mapIso (Subobject.underlyingIso j))
  simp [← L.map_comp]

/-- Every quotient subobject has an ambient representative, as an equality of
actual subobjects rather than only an isomorphism of arrow domains. -/
theorem subobjectMap_surjective (M : C) : Function.Surjective (subobjectMap L P M) := by
  intro U
  obtain ⟨N, j, hj, e, he⟩ := exists_mono_lift L P U.arrow
  let := hj
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  refine ⟨Subobject.mk j, ?_⟩
  rw [subobjectMap_mk]
  exact Subobject.mk_eq_of_comm _ e he.symm

/-- Exact localization preserves binary intersections of ambient subobjects. -/
theorem subobjectMap_inf {M : C} (A B : Subobject M) :
    subobjectMap L P M (A ⊓ B) = subobjectMap L P M A ⊓ subobjectMap L P M B := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits L P
  apply le_antisymm
  · exact le_inf ((subobjectMap L P M).monotone inf_le_left)
      ((subobjectMap L P M).monotone inf_le_right)
  · let U := subobjectMap L P M A
    let V := subobjectMap L P M B
    let a : ((U ⊓ V : Subobject (L.obj M)) : D) ⟶ L.obj (A : C) :=
      Subobject.ofLE (U ⊓ V) U inf_le_left ≫ (Subobject.underlyingIso (L.map A.arrow)).hom
    let b : ((U ⊓ V : Subobject (L.obj M)) : D) ⟶ L.obj (B : C) :=
      Subobject.ofLE (U ⊓ V) V inf_le_right ≫ (Subobject.underlyingIso (L.map B.arrow)).hom
    have ha : a ≫ L.map A.arrow = (U ⊓ V).arrow := by
      dsimp only [a]
      rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
      exact Subobject.ofLE_arrow inf_le_left
    have hb : b ≫ L.map B.arrow = (U ⊓ V).arrow := by
      dsimp only [b]
      rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
      exact Subobject.ofLE_arrow inf_le_right
    have hw : a ≫ L.map A.arrow = b ≫ L.map B.arrow := ha.trans hb.symm
    let sq := (Subobject.inf_isPullback A B).map L
    let k := sq.lift a b hw
    change U ⊓ V ≤ Subobject.mk (L.map (A ⊓ B).arrow)
    apply Subobject.le_mk_of_comm k
    rw [← Subobject.ofLE_arrow (inf_le_left : A ⊓ B ≤ A), L.map_comp,
      ← Category.assoc, IsPullback.lift_fst]
    exact ha

/-- Exact localization preserves binary sums of subobjects. The proof uses
joint epimorphy of the ambient sum inclusions and preservation of the actual
biproduct cocone, rather than merely monotonicity of the subobject map. -/
theorem subobjectMap_sup {M : C} (A B : Subobject M) :
    subobjectMap L P M (A ⊔ B) = subobjectMap L P M A ⊔ subobjectMap L P M B := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  let := ObjectProperty.SerreClassLocalization.preservesEpimorphisms L P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits L P
  apply le_antisymm
  · let U := subobjectMap L P M A ⊔ subobjectMap L P M B
    let c := cokernel.π U.arrow
    have ha : L.map A.arrow ≫ c = 0 := by
      apply (cancel_epi (Subobject.underlyingIso (L.map A.arrow)).hom).1
      rw [← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, comp_zero]
      change (subobjectMap L P M A).arrow ≫ c = 0
      rw [← Subobject.ofLE_arrow (show subobjectMap L P M A ≤ U from le_sup_left),
        Category.assoc]
      simp [c]
    have hb : L.map B.arrow ≫ c = 0 := by
      apply (cancel_epi (Subobject.underlyingIso (L.map B.arrow)).hom).1
      rw [← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, comp_zero]
      change (subobjectMap L P M B).arrow ≫ c = 0
      rw [← Subobject.ofLE_arrow (show subobjectMap L P M B ≤ U from le_sup_right),
        Category.assoc]
      simp [c]
    let p := biprod.desc (Subobject.ofLE A (A ⊔ B) le_sup_left)
      (Subobject.ofLE B (A ⊔ B) le_sup_right)
    have : Epi p := subobject_sup_desc_epi A B
    have hp : L.map p ≫ L.map (A ⊔ B).arrow ≫ c = 0 := by
      apply (isColimitOfPreserves L (BinaryBiproduct.isColimit (A : C) (B : C))).hom_ext
      rintro ⟨j⟩
      cases j
      · change L.map biprod.inl ≫ (L.map p ≫ L.map (A ⊔ B).arrow ≫ c) = _ ≫ 0
        rw [comp_zero, ← L.map_comp_assoc]
        simp only [p, biprod.inl_desc]
        rw [← L.map_comp_assoc, Subobject.ofLE_arrow]
        exact ha
      · change L.map biprod.inr ≫ (L.map p ≫ L.map (A ⊔ B).arrow ≫ c) = _ ≫ 0
        rw [comp_zero, ← L.map_comp_assoc]
        simp only [p, biprod.inr_desc]
        rw [← L.map_comp_assoc, Subobject.ofLE_arrow]
        exact hb
    have hz : L.map (A ⊔ B).arrow ≫ c = 0 := by
      apply (cancel_epi (L.map p)).1
      simpa only [comp_zero] using hp
    change Subobject.mk (L.map (A ⊔ B).arrow) ≤ U
    apply Subobject.mk_le_of_comm (Abelian.monoLift U.arrow (L.map (A ⊔ B).arrow) hz)
    exact Abelian.monoLift_comp _ _ _
  · exact sup_le ((subobjectMap L P M).monotone le_sup_left)
      ((subobjectMap L P M).monotone le_sup_right)

/-- Two nested ambient subobjects with the same localized subobject have
Serre-class quotient. This converts lattice lift data into actual layers. -/
theorem cokernel_ofLE_mem_of_subobjectMap_eq {M : C} {A B : Subobject M}
    (h : A ≤ B) (he : subobjectMap L P M A = subobjectMap L P M B) :
    P (cokernel (Subobject.ofLE A B h)) := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  have hi : IsIso (L.map (Subobject.ofLE A B h)) := by
    by_contra hn
    have ht := Subobject.mk_lt_mk_of_comm
      (i₁ := L.map A.arrow) (i₂ := L.map B.arrow) (L.map (Subobject.ofLE A B h))
      (by simp [← L.map_comp]) hn
    change subobjectMap L P M A < subobjectMap L P M B at ht
    rw [he] at ht
    exact lt_irrefl _ ht
  exact ((ObjectProperty.SerreClassLocalization.isIso_map_iff L P _).1 hi).2

/-- Conversely, an ambient layer whose quotient is in the Serre class has
equal localized endpoints. -/
theorem subobjectMap_eq_of_cokernel_ofLE_mem {M : C} {A B : Subobject M}
    (h : A ≤ B) (hP : P (cokernel (Subobject.ofLE A B h))) :
    subobjectMap L P M A = subobjectMap L P M B := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  have hw : P.isoModSerre (Subobject.ofLE A B h) :=
    (ObjectProperty.isoModSerre_iff_of_mono P _).2 hP
  have := Localization.inverts L P.isoModSerre _ hw
  exact Subobject.mk_eq_mk_of_comm _ _ (asIso (L.map (Subobject.ofLE A B h)))
    (by simp [← L.map_comp])

/-- An ambient interval of subobjects lifting a fixed quotient interval.
No Serre condition is imposed on its quotient unless the two target endpoints
coincide. -/
@[ext]
structure SubobjectIntervalLift (M : C) (S T : Subobject (L.obj M)) where
  /-- The lower subobject of `M`, whose image under `subobjectMap L P M` is `S`. -/
  lower : Subobject M
  /-- The upper subobject of `M`, containing `lower` and mapping to `T`. -/
  upper : Subobject M
  le : lower ≤ upper
  map_lower : subobjectMap L P M lower = S
  map_upper : subobjectMap L P M upper = T

namespace SubobjectIntervalLift

variable {L P} {M : C} {S T : Subobject (L.obj M)}

instance : PartialOrder (SubobjectIntervalLift L P M S T) where
  le A B := B.lower ≤ A.lower ∧ A.upper ≤ B.upper
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h k := ⟨k.1.trans h.1, h.2.trans k.2⟩
  le_antisymm A B h k := by
    apply SubobjectIntervalLift.ext
    · exact le_antisymm k.1 h.1
    · exact le_antisymm h.2 k.2

/-- The actual join combines intersection below with sum above. -/
def join (A B : SubobjectIntervalLift L P M S T) : SubobjectIntervalLift L P M S T where
  lower := A.lower ⊓ B.lower
  upper := A.upper ⊔ B.upper
  le := inf_le_left.trans (A.le.trans le_sup_left)
  map_lower := by rw [subobjectMap_inf, A.map_lower, B.map_lower, inf_idem]
  map_upper := by rw [subobjectMap_sup, A.map_upper, B.map_upper, sup_idem]

instance : SemilatticeSup (SubobjectIntervalLift L P M S T) where
  sup := join
  le_sup_left _ _ := ⟨inf_le_left, le_sup_left⟩
  le_sup_right _ _ := ⟨inf_le_right, le_sup_right⟩
  sup_le _ _ _ h k := ⟨le_inf h.1 k.1, sup_le h.2 k.2⟩

/-- Nested quotient subobjects have nested ambient representatives: first
lift both, then intersect the lower lift with the upper one. -/
theorem nonempty (h : S ≤ T) : Nonempty (SubobjectIntervalLift L P M S T) := by
  obtain ⟨A, hA⟩ := subobjectMap_surjective L P M S
  obtain ⟨B, hB⟩ := subobjectMap_surjective L P M T
  exact ⟨{ lower := A ⊓ B
           upper := B
           le := inf_le_right
           map_lower := by rw [subobjectMap_inf, hA, hB, inf_eq_left.mpr h]
           map_upper := hB }⟩

/-- The localized lower endpoint, identified with the fixed lower subobject. -/
def lowerIso (A : SubobjectIntervalLift L P M S T) : L.obj (A.lower : C) ≅ (S : D) := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  exact Subobject.isoOfMkEq (L.map A.lower.arrow) S A.map_lower

/-- The localized upper endpoint, identified with the fixed upper subobject. -/
def upperIso (A : SubobjectIntervalLift L P M S T) : L.obj (A.upper : C) ≅ (T : D) := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  exact Subobject.isoOfMkEq (L.map A.upper.arrow) T A.map_upper

@[reassoc (attr := simp)]
lemma lowerIso_hom_arrow (A : SubobjectIntervalLift L P M S T) :
    A.lowerIso.hom ≫ S.arrow = L.map A.lower.arrow := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  exact Subobject.ofMkLE_arrow A.map_lower.le

@[reassoc (attr := simp)]
lemma upperIso_hom_arrow (A : SubobjectIntervalLift L P M S T) :
    A.upperIso.hom ≫ T.arrow = L.map A.upper.arrow := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  exact Subobject.ofMkLE_arrow A.map_upper.le

/-- Localization commutes with the inclusion between the two chosen endpoints. -/
lemma endpoint_square (A : SubobjectIntervalLift L P M S T) (h : S ≤ T) :
    L.map (Subobject.ofLE A.lower A.upper A.le) ≫ A.upperIso.hom =
      A.lowerIso.hom ≫ Subobject.ofLE S T h := by
  apply (cancel_mono T.arrow).1
  simp [Category.assoc, ← L.map_comp]

/-- The quotient of an ambient lifted interval localizes to the quotient of
the prescribed interval, with a canonical cokernel comparison isomorphism. -/
def quotientIso (A : SubobjectIntervalLift L P M S T) (h : S ≤ T) :
    L.obj (cokernel (Subobject.ofLE A.lower A.upper A.le)) ≅
      cokernel (Subobject.ofLE S T h) := by
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits L P
  exact PreservesCokernel.iso L _ ≪≫
    cokernel.mapIso _ _ A.lowerIso A.upperIso (A.endpoint_square h)

/-- The quotient comparison respects the actual cokernel projections. -/
@[reassoc (attr := simp)]
lemma map_π_quotientIso_hom (A : SubobjectIntervalLift L P M S T) (h : S ≤ T) :
    L.map (cokernel.π (Subobject.ofLE A.lower A.upper A.le)) ≫ (A.quotientIso h).hom =
      A.upperIso.hom ≫ cokernel.π (Subobject.ofLE S T h) := by
  let := ObjectProperty.SerreClassLocalization.preservesFiniteColimits L P
  simp [quotientIso]

end SubobjectIntervalLift

end SubobjectLifting

section Canonical

variable {A : Type u₁} [Category.{u₁} A] [Abelian A]
  (P : ObjectProperty A) [P.IsSerreClass] (V : P.isoModSerre.Localization)

/-- The ordinary lift category for the actual canonical Serre quotient. -/
abbrev QuotientAuxiliaryLift := AuxiliaryLift P.isoModSerre.Q V

instance quotientAuxiliaryLift_isFiltered : IsFiltered (QuotientAuxiliaryLift P V) :=
  auxiliaryLift_isFiltered P.isoModSerre.Q V P.isoModSerre

instance quotientAuxiliaryLift_isCofiltered : IsCofiltered (QuotientAuxiliaryLift P V) :=
  auxiliaryLift_isCofiltered P.isoModSerre.Q V P.isoModSerre

end Canonical

end CategoryTheory.ExactCategory.SerreLocalization
