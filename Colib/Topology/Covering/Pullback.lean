/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Covering.PathClasses
public import Colib.Topology.Homotopy.HomotopyGroup.FundamentalGroup

/-!
# Original pullback covering and its fundamental group

For the literal matching-pair subtype of a supplied covering, the first
projection is a covering with its original product/subspace topology. Its
original Pi-one map is injective. When the covering total space is simply
connected, its image is exactly the kernel of the original based Pi-one map;
the resulting kernel equivalence retains precisely the first projection.

Separately, path-connected source and covering total spaces together with
surjectivity of the original based Pi-one map imply path-connectedness of
the literal pullback. No simple-connectedness of the pullback is asserted.
All three spaces may have independent universes.
-/
/-! Implementation source: `Quillen/Topology/Covering/Pullback.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual topologies,
path classes, dependent endpoint equalities and covering maps are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory IsCoveringMap
open scoped Topology unitInterval
namespace Topology.Covering.Pullback
variable {X : Type u} {Y : Type v} {E : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
  (f : C(X, Y))

section Model
variable (q : E → Y)

/-- The literal matching-pair subtype with its original subspace topology. -/
abbrev Space := {z : X × E // f z.1 = q z.2}

/-- The original first projection of the literal pullback. -/
def projection : C(Space f q, X) :=
  ⟨fun z => z.val.1, continuous_fst.comp continuous_subtype_val⟩

/-- The original second projection of the literal pullback. -/
def lift : C(Space f q, E) :=
  ⟨fun z => z.val.2, continuous_snd.comp continuous_subtype_val⟩

end Model

variable (q : C(E, Y))

/-- The literal pullback retains its original commuting square. -/
theorem square : q.comp (lift f q) = f.comp (projection f q) := by
  ext z
  exact z.property.symm

/-- A covering remains a covering on the actual first pullback projection. -/
theorem projection_isCoveringMap (hq : IsCoveringMap q) :
    IsCoveringMap (projection f q) := by
  intro x
  rcases hq (f x) with ⟨hdisc, U, hxU, hU, hqU, H, hH⟩
  let : DiscreteTopology (q ⁻¹' {f x}) := hdisc
  let V := f ⁻¹' U
  let a (z : (projection f q) ⁻¹' V) : q ⁻¹' U := ⟨z.val.val.2, by
    change q z.val.val.2 ∈ U
    rw [← z.val.property]
    exact z.property⟩
  let e : (projection f q) ⁻¹' V ≃ₜ V × (q ⁻¹' {f x}) :=
    { toFun z := (⟨z.val.val.1, z.property⟩, (H (a z)).2)
      invFun z := ⟨⟨(z.1.val, H.symm (⟨f z.1.val, z.1.property⟩, z.2)),
        (congrArg (fun t => t.1.val) (H.apply_symm_apply _)).symm.trans
          (hH (H.symm (⟨f z.1.val, z.1.property⟩, z.2)))⟩, z.1.property⟩
      left_inv z := by
        apply Subtype.ext
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · rfl
        · have he : (⟨f z.val.val.1, z.property⟩, (H (a z)).2) = H (a z) := by
            apply Prod.ext
            · apply Subtype.ext
              exact z.val.property.trans (hH (a z)).symm
            · rfl
          exact congrArg Subtype.val ((congrArg H.symm he).trans (H.symm_apply_apply _))
      right_inv z := by
        refine Prod.ext ?_ ?_
        · rfl
        · change (H (H.symm (⟨f z.1.val, z.1.property⟩, z.2))).2 = z.2
          exact congrArg (fun t : U × (q ⁻¹' {f x}) => t.2) (H.apply_symm_apply _)
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact (show IsEvenlyCovered (projection f q) x (q ⁻¹' {f x}) from
    ⟨inferInstance, V, hxU, hU.preimage f.continuous,
      (hU.preimage f.continuous).preimage (projection f q).continuous,
      e, fun _ => rfl⟩).to_isEvenlyCovered_preimage

end Topology.Covering.Pullback

namespace Topology.Covering

/-- A covering loop class lifts closed exactly when it fixes the original point by monodromy. -/
theorem mem_fundamentalGroupMap_range_iff_monodromy
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (p : C(A, B)) (hp : IsCoveringMap p) (a : A) (γ : FundamentalGroup B (p a)) :
    γ ∈ (FundamentalGroup.map p a).range ↔ hp.monodromy γ ⟨a, rfl⟩ = ⟨a, rfl⟩ := by
  constructor
  · rintro ⟨δ, rfl⟩
    exact hp.monodromy_map δ
  · intro h
    refine ⟨(hp.liftPathQuotient γ ⟨a, rfl⟩).cast rfl (congrArg Subtype.val h).symm, ?_⟩
    change Path.Homotopic.Quotient.map _ p = γ
    rw [Path.Homotopic.Quotient.map_cast]
    erw [hp.map_liftPathQuotient]
    simp only [Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]

namespace Pullback
variable {X : Type u} {Y : Type v} {E : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
  (f : C(X, Y)) (q : C(E, Y)) (hq : IsCoveringMap q)
  (z₀ : Space f q)

include hq in
/-- The original pullback projection is injective on its actual fundamental group. -/
theorem fundamentalGroup_projection_injective :
    Function.Injective (FundamentalGroup.map (projection f q) z₀) :=
  (projection_isCoveringMap f q hq).injective_path_homotopic_map z₀ z₀

/-- The original pullback square commutes on actual path-homotopy classes. -/
theorem fundamentalGroup_square (a : FundamentalGroup (Space f q) z₀) :
    FundamentalGroup.mapOfEq f z₀.property
      (FundamentalGroup.map (projection f q) z₀ a) =
      FundamentalGroup.map q z₀.val.2 (FundamentalGroup.map (lift f q) z₀ a) := by
  induction a using Quotient.inductionOn with | _ a =>
    rw [FundamentalGroup.mapOfEq_apply]
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact (a t).property

variable [SimplyConnectedSpace E]

include hq in
/-- The original first projection has exactly the kernel of the original based map as image. -/
theorem fundamentalGroup_projection_range :
    (FundamentalGroup.map (projection f q) z₀).range =
      (FundamentalGroup.mapOfEq f z₀.property).ker := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    change FundamentalGroup.mapOfEq f z₀.property
      (FundamentalGroup.map (projection f q) z₀ b) = 1
    rw [fundamentalGroup_square]
    have hb : FundamentalGroup.map (lift f q) z₀ b = 1 := Subsingleton.elim _ _
    rw [hb, map_one]
  · intro ha
    rw [mem_fundamentalGroupMap_range_iff_monodromy (projection f q)
      (projection_isCoveringMap f q hq)]
    have hn := monodromy_naturality_basepoint (projection_isCoveringMap f q hq) hq
      (lift f q) f (fun z => z.property.symm) z₀ a
    have hγ : (Path.Homotopic.Quotient.map a f).cast z₀.property.symm rfl =
        (Path.Homotopic.Quotient.refl (q z₀.val.2)).cast rfl z₀.property := by
      have ht := congrArg (fun γ : Path.Homotopic.Quotient (q z₀.val.2) (q z₀.val.2) =>
        γ.cast rfl z₀.property) ha
      simpa only [FundamentalGroup.mapOfEq_apply, FundamentalGroup.one_def,
        Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl] using ht
    have hlift : lift f q
        ((projection_isCoveringMap f q hq).monodromy a ⟨z₀, rfl⟩).val = z₀.val.2 := by
      rw [hγ] at hn
      have hh := monodromy_cast_val hq (Path.Homotopic.Quotient.refl (q z₀.val.2))
        rfl z₀.property z₀.val.2 rfl
      rw [hq.monodromy_refl] at hh
      exact hn.symm.trans hh
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext
      ((projection_isCoveringMap f q hq).monodromy a ⟨z₀, rfl⟩).property hlift

/-- The actual projection identifies the fundamental group with that kernel. -/
def fundamentalGroupKernelEquiv :
    FundamentalGroup (Space f q) z₀ ≃* (FundamentalGroup.mapOfEq f z₀.property).ker :=
  (MonoidHom.ofInjective (fundamentalGroup_projection_injective f q hq z₀)).trans
    (MulEquiv.subgroupCongr (fundamentalGroup_projection_range f q hq z₀))

/-- The kernel identification is exactly the original pullback projection. -/
theorem fundamentalGroupKernelEquiv_apply (a : FundamentalGroup (Space f q) z₀) :
    (fundamentalGroupKernelEquiv f q hq z₀ a : FundamentalGroup X z₀.val.1) =
      FundamentalGroup.map (projection f q) z₀ a := rfl


omit [SimplyConnectedSpace E] in
include hq in
/-- The original cubical Pi-one map is injective on the actual first projection. -/
theorem piOne_projection_injective :
    Function.Injective (HomotopyGroup.piMap 0 (projection f q) (x := z₀) rfl) := by
  intro a b hab
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  apply fundamentalGroup_projection_injective f q hq z₀
  have h := congrArg HomotopyGroup.pi1MulEquivFundamentalGroup hab
  simp only [HomotopyGroup.piMap, HomotopyGroup.mapHom_apply] at h
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality,
    HomotopyGroup.pi1MulEquivFundamentalGroup_naturality] at h
  simpa only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl,
    FundamentalGroup.map_apply] using h

include hq in
/-- The image of original cubical Pi one is exactly the kernel of the original based map. -/
theorem piOne_projection_range :
    (HomotopyGroup.piMap 0 (projection f q) (x := z₀) rfl).range =
      (HomotopyGroup.piMap 0 f z₀.property).ker := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
    change HomotopyGroup.pi1MulEquivFundamentalGroup
      (HomotopyGroup.piMap 0 f z₀.property (HomotopyGroup.piMap 0 (projection f q) rfl b)) =
        HomotopyGroup.pi1MulEquivFundamentalGroup 1
    simp only [HomotopyGroup.piMap, HomotopyGroup.mapHom_apply]
    rw [map_one, HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
    erw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
    have hb : FundamentalGroup.map (projection f q) z₀
        (HomotopyGroup.pi1MulEquivFundamentalGroup b) ∈
      (FundamentalGroup.mapOfEq f z₀.property).ker :=
        (fundamentalGroup_projection_range f q hq z₀).le ⟨_, rfl⟩
    change FundamentalGroup.mapOfEq f z₀.property
      (FundamentalGroup.map (projection f q) z₀
        (HomotopyGroup.pi1MulEquivFundamentalGroup b)) = 1 at hb
    simpa only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl,
      FundamentalGroup.map_apply] using hb
  · intro ha
    have hfg : HomotopyGroup.pi1MulEquivFundamentalGroup a ∈
        (FundamentalGroup.mapOfEq f z₀.property).ker := by
      change FundamentalGroup.mapOfEq f z₀.property
        (HomotopyGroup.pi1MulEquivFundamentalGroup a) = 1
      rw [← HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
      exact (congrArg HomotopyGroup.pi1MulEquivFundamentalGroup ha).trans (map_one _)
    obtain ⟨b, hb⟩ := (fundamentalGroup_projection_range f q hq z₀).ge hfg
    refine ⟨HomotopyGroup.pi1MulEquivFundamentalGroup.symm b, ?_⟩
    apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
    simp only [HomotopyGroup.piMap, HomotopyGroup.mapHom_apply]
    rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply]
    simpa only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl,
      FundamentalGroup.map_apply] using hb

/-- The original first projection identifies actual cubical Pi one with the original kernel. -/
def piOneKernelEquiv :
    HomotopyGroup.Pi 1 (Space f q) z₀ ≃* (HomotopyGroup.piMap 0 f z₀.property).ker :=
  (MonoidHom.ofInjective (piOne_projection_injective f q hq z₀)).trans
    (MulEquiv.subgroupCongr (piOne_projection_range f q hq z₀))

/-- The cubical kernel identification retains the original first-projection homomorphism. -/
theorem piOneKernelEquiv_apply (a : HomotopyGroup.Pi 1 (Space f q) z₀) :
    (piOneKernelEquiv f q hq z₀ a : HomotopyGroup.Pi 1 X z₀.val.1) =
      HomotopyGroup.piMap 0 (projection f q) rfl a := rfl

end Pullback
end Topology.Covering

namespace Topology.Covering.Pullback
variable {X : Type u} {Y : Type v} {E : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
  (f : C(X, Y)) (q : C(E, Y)) (hq : IsCoveringMap q)
  (z₀ : Space f q)

private theorem fundamentalGroupMap_surjective_of_piMap {x : X} {y : Y}
    (h : f x = y) (hf : Function.Surjective (HomotopyGroup.piMap 0 f h)) :
    Function.Surjective (FundamentalGroup.map f x) := by
  subst y
  intro a
  let eX := HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := x)
  let eY := HomotopyGroup.pi1MulEquivFundamentalGroup (X := Y) (x := f x)
  obtain ⟨b, hb⟩ := hf (eY.symm a)
  refine ⟨eX b, ?_⟩
  have hn := HomotopyGroup.pi1MulEquivFundamentalGroup_naturality f rfl b
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl] at hn
  exact hn.symm.trans ((congrArg eY hb).trans (eY.apply_symm_apply a))

private theorem pathClassMap_surjective (x₀ x : X) (α : Path x₀ x)
    (hf : Function.Surjective (FundamentalGroup.map f x₀)) :
    Function.Surjective (fun p : Path.Homotopic.Quotient x₀ x => p.map f) := by
  let F := FundamentalGroupoid.map f
  let p : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x := .mk α
  intro γ
  obtain ⟨δ, hδ⟩ := hf (γ ≫ inv (F.map p))
  refine ⟨δ ≫ p, ?_⟩
  change F.map δ = γ ≫ inv (F.map p) at hδ
  change F.map (δ ≫ p) = γ
  rw [F.map_comp, hδ]
  simp

variable [PathConnectedSpace X] [PathConnectedSpace E]

include hq in
/-- Original Pi-one surjectivity joins the original pullback basepoint to every matching pair. -/
theorem joined_basepoint
    (hf : Function.Surjective (HomotopyGroup.piMap 0 f z₀.property))
    (z : Space f q) : Joined z₀ z := by
  let α := PathConnectedSpace.somePath z₀.val.1 z.val.1
  let β := PathConnectedSpace.somePath z₀.val.2 z.val.2
  let γ : Path.Homotopic.Quotient (f z₀.val.1) (f z.val.1) :=
    ((Path.Homotopic.Quotient.mk β).map q).cast z₀.property z.property
  obtain ⟨δ, hδ⟩ := pathClassMap_surjective f z₀.val.1 z.val.1 α
    (fundamentalGroupMap_surjective_of_piMap f z₀.property hf) γ
  change δ.map f = γ at hδ
  let hp := projection_isCoveringMap f q hq
  let w := hp.monodromy δ ⟨z₀, rfl⟩
  have hn := monodromy_naturality hp hq (lift f q) f (fun t => t.property.symm) δ
    ⟨z₀, rfl⟩
  have hqδ : hq.monodromy (δ.map f) ⟨z₀.val.2, z₀.property.symm⟩ =
      ⟨z.val.2, z.property.symm⟩ := by
    apply hq.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk β)
    erw [hδ]
    simp only [γ, Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  have hw : w.val = z := by
    apply Subtype.ext
    apply Prod.ext w.property
    exact (congrArg Subtype.val hn).symm.trans (congrArg Subtype.val hqδ)
  exact ⟨(Quotient.out (hp.liftPathQuotient δ ⟨z₀, rfl⟩)).cast rfl hw.symm⟩

include hq in
/-- The literal pullback is path connected under original Pi-one surjectivity.
No simple-connectedness conclusion for the pullback is asserted. -/
theorem pathConnectedSpace
    (hf : Function.Surjective (HomotopyGroup.piMap 0 f z₀.property)) :
    PathConnectedSpace (Space f q) where
  nonempty := ⟨z₀⟩
  joined a b := (joined_basepoint f q hq z₀ hf a).symm.trans
    (joined_basepoint f q hq z₀ hf b)

end Topology.Covering.Pullback
