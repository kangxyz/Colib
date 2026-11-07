/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Colib.Topology.MappingCylinder.Compact.Fibers
public import Colib.Topology.Pushout.CompactParameter
public import Colib.Topology.Maps.SumSubtype
public import Colib.Topology.HomotopyLifting.Compact.Stationary

/-!
# Compact homotopy lifting for the mapping cylinder

Time functions and compact parameter quotients construct continuous lifts on the two cylinder
    pieces. Their matching and descent give the compact homotopy lifting property.


Implementation provenance:
`Quillen/Topology/MappingCylinder/Compact/Lifting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology


noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace TopCat.MappingCylinder.Compact

/-- Follow a shifted path until time one. -/
def addTime (s t : unitInterval) : unitInterval :=
  ⟨min ((s : ℝ) + (t : ℝ)) 1,le_min (add_nonneg s.2.1 t.2.1) zero_le_one,min_le_right _ _⟩
/-- The remaining path time after traversing a cylinder segment. -/
def remainingTime (t s : unitInterval) : unitInterval :=
  ⟨max ((t : ℝ) - (s : ℝ)) 0,le_max_right _ _,max_le (by linarith [t.2.2,s.2.1]) zero_le_one⟩

@[fun_prop] theorem continuous_addTime : Continuous (fun z : unitInterval × unitInterval ↦
    addTime z.1 z.2) := by
  unfold addTime
  fun_prop
@[fun_prop] theorem continuous_remainingTime :
    Continuous (fun z : unitInterval × unitInterval ↦ remainingTime z.1 z.2) := by
  unfold remainingTime
  fun_prop
@[simp] theorem addTime_zero (s : unitInterval) : addTime s 0 = s := by
  apply Subtype.ext
  simp [addTime,min_eq_left s.2.2]
@[simp] theorem zero_addTime (t : unitInterval) : addTime 0 t = t := by
  apply Subtype.ext
  simp [addTime,min_eq_left t.2.2]
@[simp] theorem remainingTime_zero (t : unitInterval) : remainingTime t 0 = t := by
  apply Subtype.ext
  simp [remainingTime,max_eq_left t.2.1]
@[simp] theorem remainingTime_self (t : unitInterval) : remainingTime t t = 0 := by
  apply Subtype.ext
  simp [remainingTime]
theorem remainingTime_eq_zero {t s : unitInterval} (h : t ≤ s) : remainingTime t s = 0 := by
  apply Subtype.ext
  exact max_eq_right (sub_nonpos.mpr h)
theorem addTime_remainingTime {s t : unitInterval} (h : s ≤ t) :
    addTime s (remainingTime t s) = t := by
  apply Subtype.ext
  change min ((s : ℝ) + max ((t : ℝ) - (s : ℝ)) 0) 1 = (t : ℝ)
  rw [max_eq_left (sub_nonneg.mpr (show (s : ℝ) ≤ (t : ℝ) from h))]
  have he : (s : ℝ) + ((t : ℝ) - (s : ℝ)) = (t : ℝ) := by ring
  rw [he, min_eq_left t.2.2]
@[simp] theorem addTime_symm (s : unitInterval) : addTime s (unitInterval.symm s) = 1 := by
  apply Subtype.ext
  change min ((s : ℝ) + (1 - (s : ℝ))) 1 = 1
  simp

end TopCat.MappingCylinder.Compact

end

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace TopCat.MappingCylinder.Compact
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)
  {D : Type u} [TopologicalSpace D] (b : C(D, T))

/-- The source points paired with test parameters whose initial base values agree. -/
abbrev SourceStart := {z : A × D // (f ≫ base) z.1 = b z.2}
/-- The target points paired with test parameters whose initial base values agree. -/
abbrev TargetStart := {z : C × D // base z.1 = b z.2}
/-- The strict pullback of the displayed mapping-cylinder projection along the test map `b`. -/
abbrev CylinderStart := {z : M × D // projection sq base z.1 = b z.2}
/-- The disjoint union of matched source cylinder points and matched target points used to
present `CylinderStart`. -/
abbrev StartPieces := (SourceStart (f := f) base b × TopCat.I) ⊕ TargetStart base b

/-- Literal sum presentation of the mapping cylinder matched with a test. -/
def parameterQuotient : C(StartPieces (f := f) base b,CylinderStart sq base b) where
  toFun := Sum.elim
    (fun z ↦ ⟨(l (z.1.1.1,z.2),z.1.1.2),
      (ConcreteCategory.congr_hom
        (TopCat.MappingCylinder.mappingCylinderProjection_cylinder_assoc sq base)
        (z.1.1.1,z.2)).trans z.1.2⟩)
    (fun z ↦ ⟨(c z.1.1,z.1.2),
      (ConcreteCategory.congr_hom
        (TopCat.MappingCylinder.mappingCylinderProjection_target_assoc sq base) z.1.1).trans z.2⟩)
  continuous_toFun := by
    apply Continuous.sumElim <;> fun_prop

/-- The sum presentation has the actual pullback topology under the explicit
closed matching-locus hypothesis and a locally compact parameter. -/
theorem parameterQuotient_isQuotientMap [LocallyCompactSpace D]
    (hc : IsClosed (Set.ofPred (fun z : M × D ↦ projection sq base z.1 = b z.2))) :
    IsQuotientMap (parameterQuotient sq base b) := by
  let P := {z : ((A × TopCat.I) ⊕ C) × D //
    projection sq base (Sum.elim l c z.1) = b z.2}
  let pred : ((A × TopCat.I) × D) ⊕ (C × D) → Prop :=
    Sum.elim (fun z ↦ (f ≫ base) z.1.1 = b z.2) (fun z ↦ base z.1 = b z.2)
  let e : C(P,{z // pred z}) := {
    toFun z := ⟨Homeomorph.sumProdDistrib z.1,by
      rcases z with ⟨⟨z | z,d⟩,h⟩
      · exact (ConcreteCategory.congr_hom
          (TopCat.MappingCylinder.mappingCylinderProjection_cylinder_assoc sq base) z).symm.trans h
      · exact (ConcreteCategory.congr_hom
          (TopCat.MappingCylinder.mappingCylinderProjection_target_assoc sq base) z).symm.trans h⟩
    continuous_toFun := by dsimp only [P]; fun_prop }
  let e' : C(P,({z : (A × TopCat.I) × D // (f ≫ base) z.1.1 = b z.2}) ⊕ TargetStart base b) :=
    ⟨fun z ↦ sumSubtypeHomeomorph pred (e z),
      (sumSubtypeHomeomorph pred).continuous.comp e.continuous⟩
  let left : C({z : (A × TopCat.I) × D // (f ≫ base) z.1.1 = b z.2},
      SourceStart (f := f) base b × TopCat.I) :=
    ⟨fun z ↦ (⟨(z.1.1.1,z.1.2),z.2⟩,z.1.1.2),by fun_prop⟩
  let split : C(P,StartPieces (f := f) base b) :=
    ⟨(Sum.map left id) ∘ e',by fun_prop⟩
  have hQ := pushout_parameter_pullback_quotient_of_isClosed sq (projection sq base) b hc
  have heq : ((parameterQuotient sq base b) : StartPieces (f := f) base b → _ ) ∘ split =
      (fun z : P ↦ (⟨(Sum.elim l c z.1.1,z.1.2),z.2⟩ : CylinderStart sq base b)) := by
    funext z
    rcases z with ⟨⟨z | z,d⟩,h⟩ <;> rfl
  exact IsQuotientMap.of_comp split.continuous (parameterQuotient sq base b).continuous
    (heq.symm ▸ hQ)

end TopCat.MappingCylinder.Compact

end

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
namespace TopCat.MappingCylinder.Compact
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)
  {D : Type u} [TopologicalSpace D] (b : C(D, T))

/-- Genuine lifting on the original source and target constructs the exact
piecewise cylinder lift. No HLP of the pushout projection is used. -/
theorem exists_piece_lift
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (H : C(unitInterval × D, T)) (hH₀ : ∀ d, H (0, d) = b d) :
    ∃ L : C(StartPieces (f := f) base b × unitInterval,M),
      (∀ z,L (z,0) = (parameterQuotient sq base b z).1.1) ∧
      (∀ z t,projection sq base (L (z,t)) = H (t,(parameterQuotient sq base b z).1.2)) ∧
      ∀ (a : SourceStart (f := f) base b) t,
        L (.inl (a,ULift.up 1),t) =
          L (.inr (⟨(f a.1.1,a.1.2),a.2⟩ : TargetStart base b),t) := by
  classical
  have htarget (x : C) : projection sq base (c x) = base x :=
    ConcreteCategory.congr_hom
      (TopCat.MappingCylinder.mappingCylinderProjection_target_assoc sq base) x
  let a₀ : C(SourceStart (f := f) base b,A) := ⟨fun z ↦ z.1.1,by fun_prop⟩
  let AH : C(unitInterval × SourceStart (f := f) base b,T) :=
    ⟨fun z ↦ H (z.1,z.2.1.2),by fun_prop⟩
  obtain ⟨LA,hLA₀,hLA⟩ := hp _ a₀ AH (fun z ↦ (hH₀ z.1.2).trans z.2.symm)
  let Q := {z : C × (unitInterval × D) // base z.1 = H (z.2.1,z.2.2)}
  let q₀ : C(Q,C) := ⟨fun z ↦ z.1.1,by fun_prop⟩
  let QH : C(unitInterval × Q,T) :=
    ⟨fun z ↦ H (addTime z.2.1.2.1 z.1,z.2.1.2.2),by dsimp only [Q]; fun_prop⟩
  obtain ⟨LQ,hLQ₀,hLQ⟩ := hq Q q₀ QH (by
    intro z
    change H (addTime z.1.2.1 0,z.1.2.2) = base z.1.1
    rw [addTime_zero]
    exact z.2.symm)
  let qstart : C(SourceStart (f := f) base b × TopCat.I,Q) := {
    toFun z := ⟨(f (LA (σ z.2.down,z.1)),(σ z.2.down,z.1.1.2)),hLA _ _⟩
    continuous_toFun := by fun_prop }
  let targetStart : C(TargetStart base b,Q) := {
    toFun z := ⟨(z.1.1,(0,z.1.2)),z.2.trans (hH₀ z.1.2).symm⟩
    continuous_toFun := by fun_prop }
  let G₁ : C((SourceStart (f := f) base b × TopCat.I) × unitInterval,M) :=
    ⟨fun z ↦ l (LA (z.2,z.1.1),ULift.up (addTime z.1.2.down z.2)),by fun_prop⟩
  let G₂ : C((SourceStart (f := f) base b × TopCat.I) × unitInterval,M) :=
    ⟨fun z ↦ c (LQ (remainingTime z.2 (σ z.1.2.down),qstart z.1)),by fun_prop⟩
  have hseam (z : (SourceStart (f := f) base b × TopCat.I) × unitInterval)
      (hz : z.2 = σ z.1.2.down) : G₁ z = G₂ z := by
    change l (LA (z.2,z.1.1),ULift.up (addTime z.1.2.down z.2)) =
      c (LQ (remainingTime z.2 (σ z.1.2.down),qstart z.1))
    rw [hz,addTime_symm,remainingTime_self,hLQ₀]
    exact ConcreteCategory.congr_hom sq.w (LA (σ z.1.2.down,z.1.1))
  let left : C((SourceStart (f := f) base b × TopCat.I) × unitInterval,M) := {
    toFun z := if z.2 ≤ σ z.1.2.down then G₁ z else G₂ z
    continuous_toFun := Continuous.if_le G₁.continuous G₂.continuous
      (by fun_prop) (by fun_prop) hseam }
  let right : C(TargetStart base b × unitInterval,M) :=
    ⟨fun z ↦ c (LQ (z.2,targetStart z.1)),by fun_prop⟩
  let L : C(StartPieces (f := f) base b × unitInterval,M) :=
    (⟨Sum.elim left right,left.continuous.sumElim right.continuous⟩ : C(_,M)).comp
      ⟨fun z ↦ Homeomorph.sumProdDistrib z,Homeomorph.sumProdDistrib.continuous⟩
  refine ⟨L,?_,?_,?_⟩
  · intro z
    rcases z with ⟨a,s⟩ | a
    · change (if (0 : unitInterval) ≤ σ s.down then G₁ ((a,s),0) else G₂ ((a,s),0)) = l (a.1.1,s)
      rw [ite_eq_left (show (0 : unitInterval) ≤ σ s.down from zero_le)]
      change l (LA (0,a),ULift.up (addTime s.down 0)) = _
      rw [hLA₀,addTime_zero]
      rfl
    · change c (LQ (0,targetStart a)) = c a.1.1
      rw [hLQ₀]
      rfl
  · intro z t
    rcases z with ⟨a,s⟩ | a
    · change projection sq base (if t ≤ σ s.down then G₁ ((a,s),t) else G₂ ((a,s),t)) = H (t,a.1.2)
      split_ifs with ht
      · exact (ConcreteCategory.congr_hom
          (TopCat.MappingCylinder.mappingCylinderProjection_cylinder_assoc sq base)
          (LA (t,a),ULift.up (addTime s.down t))).trans (hLA t a)
      · change projection sq base (c (LQ (remainingTime t (σ s.down),qstart (a,s)))) = _
        rw [htarget]
        rw [hLQ]
        change H (addTime (σ s.down) (remainingTime t (σ s.down)),a.1.2) = _
        rw [addTime_remainingTime (le_of_lt (lt_of_not_ge ht))]
    · change projection sq base (c (LQ (t,targetStart a))) = H (t,a.1.2)
      rw [htarget,hLQ]
      change H (addTime 0 t,a.1.2) = _
      rw [zero_addTime]
  · intro a t
    change (if t ≤ σ (1 : unitInterval) then G₁ ((a,ULift.up 1),t)
      else G₂ ((a,ULift.up 1),t)) =
      c (LQ (t,targetStart ⟨(f a.1.1,a.1.2),a.2⟩))
    rw [symm_one]
    split_ifs with ht
    · have ht' : t = 0 := le_antisymm ht (show (0 : unitInterval) ≤ t from zero_le)
      subst t
      change l (LA (0,a),ULift.up (addTime 1 0)) = _
      rw [addTime_zero,hLA₀,hLQ₀]
      exact ConcreteCategory.congr_hom sq.w a.1.1
    · change c (LQ (remainingTime t (σ (1 : unitInterval)),qstart (a,ULift.up 1))) = _
      rw [symm_one,remainingTime_zero]
      apply congrArg c
      apply congrArg (fun z ↦ LQ (t,z))
      apply Subtype.ext
      change (f (LA (σ (1 : unitInterval),a)),σ (1 : unitInterval),a.1.2) =
        (f a.1.1,0,a.1.2)
      rw [symm_one,hLA₀]
      rfl

end TopCat.MappingCylinder.Compact

end

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace TopCat.MappingCylinder.Compact
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)
  {D : Type u} [TopologicalSpace D] (b : C(D, T))

/-- The only identifications of the original piecewise lift are its literal
cap seam. Interior representatives and target representatives are retained. -/
theorem piece_lift_factorsThrough
    (L : C(StartPieces (f := f) base b × unitInterval, M))
    (hcap : ∀ (a : SourceStart (f := f) base b) t,
      L (.inl (a, ULift.up 1), t) =
        L (.inr (⟨(f a.1.1, a.1.2), a.2⟩ : TargetStart base b), t)) :
    Function.FactorsThrough L (fun z ↦ (parameterQuotient sq base b z.1,z.2)) := by
  have hi : Function.Injective (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) := by
    intro a a' h
    exact congrArg Prod.fst h
  have hc : Function.Injective c :=
    Types.pushoutCocone_inr_injective_of_isColimit (sq.map (forget TopCat)).isColimit hi
  have interior (a a' : SourceStart (f := f) base b) (s s' : TopCat.I)
      (hs : s ≠ ULift.up 1)
      (hm : l (a.1.1,s) = l (a'.1.1,s')) (hd : a.1.2 = a'.1.2) :
      (a,s) = (a',s') := by
    have hn : (a.1.1,s) ∉ Set.range (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) := by
      rintro ⟨x,hx⟩
      exact hs (congrArg Prod.snd hx).symm
    have he := pushout_cell_eq_of_not_mem_range sq hn hm
    have hfirst : a.1.1 = a'.1.1 := congrArg (fun z : A × TopCat.I ↦ z.1) he
    have hsecond : s = s' := congrArg (fun z : A × TopCat.I ↦ z.2) he
    have ha : a = a' := Subtype.ext (Prod.ext hfirst hd)
    exact Prod.ext ha hsecond
  have mixed (a : SourceStart (f := f) base b) (s : TopCat.I)
      (a' : TargetStart base b) (t : unitInterval)
      (hm : l (a.1.1,s) = c a'.1.1) (hd : a.1.2 = a'.1.2) :
      L (.inl (a,s),t) = L (.inr a',t) := by
    obtain ⟨x,hx,hf⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      (sq.map (forget TopCat)).isColimit hi (a.1.1,s) a'.1.1).mp hm
    have hx₁ : x = a.1.1 := congrArg Prod.fst hx
    have hs : s = ULift.up 1 := (congrArg Prod.snd hx).symm
    rw [hs,hcap]
    apply congrArg (fun z ↦ L (.inr z,t))
    apply Subtype.ext
    exact Prod.ext (hx₁ ▸ hf) hd
  rintro ⟨z,t⟩ ⟨z',t'⟩ h
  have ht : t = t' := congrArg Prod.snd h
  subst t'
  have hm := congrArg (fun z ↦ z.1.1.1) h
  have hd := congrArg (fun z ↦ z.1.1.2) h
  rcases z with ⟨a,s⟩ | a <;> rcases z' with ⟨a',s'⟩ | a'
  · change l (a.1.1,s) = l (a'.1.1,s') at hm
    change a.1.2 = a'.1.2 at hd
    by_cases hs : s = ULift.up 1
    · by_cases hs' : s' = ULift.up 1
      · subst s
        subst s'
        rw [hcap,hcap]
        have hff : f a.1.1 = f a'.1.1 := hc
          ((ConcreteCategory.congr_hom sq.w a.1.1).symm.trans
            (hm.trans (ConcreteCategory.congr_hom sq.w a'.1.1)))
        exact congrArg (fun z ↦ L (.inr z,t)) (Subtype.ext (Prod.ext hff hd))
      · exact congrArg (fun x ↦ L (.inl x,t)) (interior a' a s' s hs' hm.symm hd.symm).symm
    · exact congrArg (fun x ↦ L (.inl x,t)) (interior a a' s s' hs hm hd)
  · exact mixed a s a' t hm hd
  · exact (mixed a' s' a t hm.symm hd.symm).symm
  · exact congrArg (fun x ↦ L (.inr x,t)) (Subtype.ext (Prod.ext (hc hm) hd))

/-- Lift any displayed homotopy on a locally compact test whose original
matching locus is closed. This is an actual continuous lift on that test,
not a global path-space lifting function. -/
theorem homotopy_lift_of_closed_matching [LocallyCompactSpace D]
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (a : C(D, M)) (H : C(unitInterval × D, T))
    (hH₀ : ∀ d, H (0, d) = projection sq base (a d))
    (hc : IsClosed (Set.ofPred (fun z : M × D ↦ projection sq base z.1 = H (0,z.2)))) :
    ∃ L : C(unitInterval × D,M),(∀ d,L (0,d) = a d) ∧
      ∀ t d,projection sq base (L (t,d)) = H (t,d) := by
  let b : C(D,T) := ⟨fun d ↦ H (0,d),by fun_prop⟩
  obtain ⟨G,hG₀,hG,hcap⟩ := exists_piece_lift sq base b hp hq H (fun _ ↦ rfl)
  have hQ := parameterQuotient_isQuotientMap sq base b hc
  let QI : C(StartPieces (f := f) base b × unitInterval,CylinderStart sq base b × unitInterval) :=
    (parameterQuotient sq base b).prodMap (ContinuousMap.id _)
  have hQI : IsQuotientMap QI := quotientMap_prod_parameter (D := unitInterval) hQ
  let R := hQI.lift G (piece_lift_factorsThrough sq base b G hcap)
  have hR : R.comp QI = G := hQI.lift_comp G _
  let L : C(unitInterval × D,M) := R.comp
    ⟨fun z ↦ (⟨(a z.2,z.2),(hH₀ z.2).symm⟩,z.1),by fun_prop⟩
  refine ⟨L,?_,?_⟩
  · intro d
    obtain ⟨z,hz⟩ := hQ.surjective (⟨(a d,d),(hH₀ d).symm⟩ : CylinderStart sq base b)
    have hh := ContinuousMap.congr_fun hR (z,0)
    change R (parameterQuotient sq base b z,0) = G (z,0) at hh
    change R (⟨(a d,d),(hH₀ d).symm⟩,0) = a d
    rw [← hz,hh,hG₀]
    exact congrArg (fun z ↦ z.1.1) hz
  · intro t d
    obtain ⟨z,hz⟩ := hQ.surjective (⟨(a d,d),(hH₀ d).symm⟩ : CylinderStart sq base b)
    have hh := ContinuousMap.congr_fun hR (z,t)
    change R (parameterQuotient sq base b z,t) = G (z,t) at hh
    change projection sq base (R (⟨(a d,d),(hH₀ d).symm⟩,t)) = H (t,d)
    rw [← hz,hh,hG]
    exact congrArg (fun d ↦ H (t,d)) (congrArg (fun z ↦ z.1.2) hz)

end TopCat.MappingCylinder.Compact

end

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval Simplicial
universe u
namespace TopCat.MappingCylinder.Compact
variable {A C M T : TopCat.{u}} {f : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ M} {c : C ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : C ⟶ T)

/-- Compact locally compact test lifting on the original quotient projection,
assuming the actual relevant test graphs are closed in the unchanged base. -/
theorem compactHomotopyLiftingProperty_of_closedGraphs
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (hgraph : ∀ (D : Type u) [TopologicalSpace D] [CompactSpace D] [LocallyCompactSpace D]
      (b : C(D, T)), IsClosed (Set.ofPred (fun z : D × T ↦ b z.1 = z.2))) :
    CompactHomotopyLiftingProperty (projection sq base).hom := by
  intro D _ _ _ a H h₀
  let b : C(D,T) := ⟨fun d ↦ H (0,d),by fun_prop⟩
  apply homotopy_lift_of_closed_matching sq base hp hq a H h₀
  have hc := (hgraph D b).preimage
    (continuous_snd.prodMk ((projection sq base).hom.continuous.comp continuous_fst))
  convert hc using 1
  ext z
  exact eq_comm

/-- A genuine homeomorphism of the base to an actual realization supplies
all required compact closed graphs. A mere homotopy equivalence is not used. -/
theorem compactHomotopyLiftingProperty_of_realizationModel
    (hp : HomotopyLiftingProperty (f ≫ base).hom)
    (hq : HomotopyLiftingProperty base.hom)
    (X : SSet.{u}) (e : T ≃ₜ |X|) :
    CompactHomotopyLiftingProperty (projection sq base).hom := by
  apply compactHomotopyLiftingProperty_of_closedGraphs sq base hp hq
  intro D _ _ _ b
  have hc := (realization_compactMap_isClosed_graph X ((e : C(T,|X|)).comp b)).preimage
    (continuous_fst.prodMk (e.continuous.comp continuous_snd))
  convert hc using 1
  ext z
  exact e.injective.eq_iff.symm

end TopCat.MappingCylinder.Compact

end
