/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SubdivisionComparison.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Homological comparison from eventual smallness

A degreewise injective inclusion is a quasi-isomorphism if compatible
endomorphisms, acting identically on homology on both sides, eventually carry
each individual chain into its image. This algebraic argument is applied to
the constructed barycentric operators and the geometrically proved mesh decay.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

universe u v

namespace HomologicalComplex

/-- A cycle represents zero precisely when its actual chain is a boundary. -/
theorem moduleHomologyπ_eq_zero_iff (S : ShortComplex (ModuleCat.{u} ℤ))
    (z : S.cycles) :
    S.homologyπ z = 0 ↔ ∃ x : S.X₁, S.f x = S.iCycles z := by
  have heq : S.homologyι (S.homologyπ z) = S.pOpcycles (S.iCycles z) :=
    congrArg (fun f ↦ f z) S.homology_π_ι
  constructor
  · intro hz
    apply (S.moduleCat_pOpcycles_eq_zero_iff (S.iCycles z)).mp
    rw [← heq, hz, map_zero]
  · intro hz
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    rw [map_zero, heq]
    exact (S.moduleCat_pOpcycles_eq_zero_iff (S.iCycles z)).mpr hz

/-- Eventual chainwise entry under compatible homologically trivial operators
implies that the original degreewise injective comparison is a quasi-isomorphism. -/
theorem quasiIso_of_eventual_range {J : Type v} {c : ComplexShape J}
    {K L : HomologicalComplex (ModuleCat.{u} ℤ) c} (f : K ⟶ L)
    (hf : ∀ j, Function.Injective (f.f j))
    (p : ℕ → (K ⟶ K)) (q : ℕ → (L ⟶ L))
    (comm : ∀ k, p k ≫ f = f ≫ q k)
    (hp : ∀ k j, HomologicalComplex.homologyMap (p k) j = 𝟙 _)
    (hq : ∀ k j, HomologicalComplex.homologyMap (q k) j = 𝟙 _)
    (hsmall : ∀ j (x : L.X j), ∃ k, ∃ y : K.X j, f.f j y = (q k).f j x) :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply (injective_iff_map_eq_zero (HomologicalComplex.homologyMap f j).hom).mpr
    intro a ha
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ j)).mp inferInstance a
    have hn := congrArg (fun g ↦ g z) (HomologicalComplex.homologyπ_naturality f j)
    have hz : L.homologyπ j (HomologicalComplex.cyclesMap f j z) = 0 := hn.symm.trans ha
    obtain ⟨x, hx⟩ := (moduleHomologyπ_eq_zero_iff (L.sc j) _).mp hz
    obtain ⟨k, y, hy⟩ := hsmall (c.prev j) x
    have hc := congrArg (fun g ↦ g.f j (K.iCycles j z)) (comm k).symm
    have hcycle := congrArg (fun g ↦ g z) (HomologicalComplex.cyclesMap_i f j).symm
    have hybd : K.d (c.prev j) j y =
        K.iCycles j (HomologicalComplex.cyclesMap (p k) j z) := by
      apply hf j
      have hfc := congrArg (fun g ↦ g y) (f.comm (c.prev j) j).symm
      have hqc := congrArg (fun g ↦ g x) ((q k).comm (c.prev j) j).symm
      have hpcy := congrArg (fun g ↦ g z) (HomologicalComplex.cyclesMap_i (p k) j)
      change (q k).f j (f.f j (K.iCycles j z)) =
        f.f j ((p k).f j (K.iCycles j z)) at hc
      change L.d (c.prev j) j x = L.iCycles j (HomologicalComplex.cyclesMap f j z) at hx
      change f.f j (K.iCycles j z) = L.iCycles j (HomologicalComplex.cyclesMap f j z) at hcycle
      change (q k).f j (L.d (c.prev j) j x) = L.d (c.prev j) j ((q k).f (c.prev j) x) at hqc
      change f.f j (K.d (c.prev j) j y) = L.d (c.prev j) j (f.f (c.prev j) y) at hfc
      change K.iCycles j (HomologicalComplex.cyclesMap (p k) j z) =
        (p k).f j (K.iCycles j z) at hpcy
      rw [hfc, hy, ← hqc, hx, ← hcycle, hc, ← hpcy]
    have hz' := (moduleHomologyπ_eq_zero_iff (K.sc j)
      (HomologicalComplex.cyclesMap (p k) j z)).mpr ⟨y, hybd⟩
    have hpn := congrArg (fun g ↦ g z) (HomologicalComplex.homologyπ_naturality (p k) j)
    rw [hp k j] at hpn
    exact hpn.trans hz'
  · intro a
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ j)).mp inferInstance a
    obtain ⟨k, y, hy⟩ := hsmall j (L.iCycles j z)
    have hycycle : K.d j (c.next j) y = 0 := by
      apply hf (c.next j)
      rw [map_zero]
      have hfc := congrArg (fun g ↦ g y) (f.comm j (c.next j)).symm
      have hqc := congrArg (fun g ↦ g (L.iCycles j z)) ((q k).comm j (c.next j)).symm
      have hz := congrArg (fun g ↦ g z) (L.iCycles_d j (c.next j))
      change f.f (c.next j) (K.d j (c.next j) y) = L.d j (c.next j) (f.f j y) at hfc
      change (q k).f (c.next j) (L.d j (c.next j) (L.iCycles j z)) =
        L.d j (c.next j) ((q k).f j (L.iCycles j z)) at hqc
      change L.d j (c.next j) (L.iCycles j z) = 0 at hz
      rw [hfc, hy, ← hqc, hz, map_zero]
    let w : K.cycles j := (K.sc j).cyclesMk y hycycle
    have hw : K.iCycles j w = y := (K.sc j).i_cyclesMk y hycycle
    refine ⟨K.homologyπ j w, ?_⟩
    have hcw : HomologicalComplex.cyclesMap f j w = HomologicalComplex.cyclesMap (q k) j z := by
      apply (ModuleCat.mono_iff_injective (L.iCycles j)).mp inferInstance
      have hfw := congrArg (fun g ↦ g w) (HomologicalComplex.cyclesMap_i f j)
      have hqz := congrArg (fun g ↦ g z) (HomologicalComplex.cyclesMap_i (q k) j)
      exact hfw.trans ((congrArg (f.f j) hw).trans (hy.trans hqz.symm))
    have hfn := congrArg (fun g ↦ g w) (HomologicalComplex.homologyπ_naturality f j)
    have hqn := congrArg (fun g ↦ g z) (HomologicalComplex.homologyπ_naturality (q k) j)
    rw [hq k j] at hqn
    exact hfn.trans ((congrArg (L.homologyπ j) hcw).trans hqn.symm)

end HomologicalComplex
