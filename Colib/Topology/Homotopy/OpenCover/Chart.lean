/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Path.InSubset
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Chart

Common object choices and chart functors, before overlap compatibility.
-/

@[expose] public section

/-!
Local chart input and normalized path values. The global descent construction
is developed in `Colib.Topology.Homotopy.OpenCover.Descent`.
-/

noncomputable section

open CategoryTheory Set

universe u v w z

namespace FundamentalGroupoid.OpenCover

variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable {C : Type w} [Category.{z} C]

/-- Common object choices and chart functors, before overlap compatibility. -/
structure ChartData (U : ι → Set X) where
  /-- The common target object assigned to each ambient point. -/
  obj : X → C
  /-- A functor on each chart's actual fundamental groupoid. -/
  chart : ∀ i, FundamentalGroupoid (U i) ⥤ C
  /-- Identifications between the common objects and each local functor. -/
  transport : ∀ (i) (x : U i), obj x.val ≅ (chart i).obj (FundamentalGroupoid.mk x)

namespace ChartData

variable {U : ι → Set X} (d : ChartData (C := C) U)

/-- Local decoding normalized to the common object family. -/
def localValue (i : ι) {x y : X} (p : Path x y)
    (hp : Set.range p ⊆ U i) : d.obj x ⟶ d.obj y :=
  (d.transport i ⟨x, hp p.source_mem_range⟩).hom ≫
    (d.chart i).map (⟦(Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_, hp
        (p).target_mem_range⟩) p hp)⟧) ≫
      (d.transport i ⟨y, hp p.target_mem_range⟩).inv

/-- Agreement on every actual overlap path, not merely overlap connectedness. -/
def Compatible : Prop :=
  ∀ (i j : ι) {x y : X} (p : Path x y)
    (hi : Set.range p ⊆ U i) (hj : Set.range p ⊆ U j),
    d.localValue i p hi = d.localValue j p hj

/-- The local value is independent of the proof that the path lies in the chart. -/
theorem localValue_proof_irrel (i : ι) {x y : X} (p : Path x y)
    (h₁ h₂ : Set.range p ⊆ U i) : d.localValue i p h₁ = d.localValue i p h₂ := by
  rfl

/-- Normalized local decoding sends constant paths to identities. -/
theorem localValue_refl (i : ι) (x : X)
    (hp : Set.range (Path.refl x) ⊆ U i) :
    d.localValue i (Path.refl x) hp = 𝟙 (d.obj x) := by
  have h : (Path.inSubset (x := ⟨_, hp ((Path.refl x)).source_mem_range⟩) (y := ⟨_, hp
      ((Path.refl x)).target_mem_range⟩) (Path.refl x) hp) =
      Path.refl (⟨x, hp (Path.refl x).source_mem_range⟩ : U i) := by
    ext t
    rfl
  simp only [localValue, h]
  change (d.transport i _).hom ≫ (d.chart i).map (𝟙 _) ≫
    (d.transport i _).inv = _
  simp

/-- Normalized local decoding preserves composition of actual chart paths. -/
theorem localValue_trans (i : ι) {x y z : X} (p : Path x y) (q : Path y z)
    (hp : Set.range p ⊆ U i) (hq : Set.range q ⊆ U i)
    (hpq : Set.range (p.trans q) ⊆ U i) :
    d.localValue i (p.trans q) hpq =
      d.localValue i p hp ≫ d.localValue i q hq := by
  have h : (Path.inSubset (x := ⟨_, hpq ((p.trans q)).source_mem_range⟩) (y := ⟨_, hpq ((p.trans
      q)).target_mem_range⟩) (p.trans q) hpq) = ((Path.inSubset (x := ⟨_, hp
      (p).source_mem_range⟩) (y := ⟨_, hp (p).target_mem_range⟩) p hp)).trans ((Path.inSubset (x
      := ⟨_, hq (q).source_mem_range⟩) (y := ⟨_, hq (q).target_mem_range⟩) q hq)) := by
    ext t
    simp only [Path.inSubset, Path.coe_mk_mk, Path.trans_apply]
    split <;> rfl
  simp only [localValue, h]
  change (d.transport i _).hom ≫ (d.chart i).map
      ((⟦(Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_, hp (p).target_mem_range⟩)
          p hp)⟧ : FundamentalGroupoid.mk _ ⟶ _) ≫ ⟦(Path.inSubset (x := ⟨_, hq
          (q).source_mem_range⟩) (y := ⟨_, hq (q).target_mem_range⟩) q hq)⟧) ≫
      (d.transport i _).inv = _
  simp [Functor.map_comp, Category.assoc]

/-- The local class of a subpath is computed in the actual chart subtype. -/
theorem localValue_subpath (i : ι) {x y : X} (p : Path x y)
    (hp : Set.range p ⊆ U i) (a b : unitInterval)
    (hab : Set.range (p.subpath a b) ⊆ U i) :
    d.localValue i (p.subpath a b) hab =
      (d.transport i (((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_, hp
          (p).target_mem_range⟩) p hp)) a)).hom ≫
        (d.chart i).map (⟦((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_, hp
            (p).target_mem_range⟩) p hp)).subpath a b⟧) ≫
          (d.transport i (((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_, hp
              (p).target_mem_range⟩) p hp)) b)).inv := by
  have h : (Path.inSubset (x := ⟨_, hab ((p.subpath a b)).source_mem_range⟩) (y := ⟨_, hab
      ((p.subpath a b)).target_mem_range⟩) (p.subpath a b) hab) = ((Path.inSubset (x := ⟨_, hp
      (p).source_mem_range⟩) (y := ⟨_, hp (p).target_mem_range⟩) p hp)).subpath a b := by
    ext t
    rfl
  simp only [localValue, h]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Inserting any breakpoint preserves the local ordered product. The proof
uses a homotopy in the chart itself, not an ambient homotopy. -/
theorem localValue_subpath_split (i : ι) {x y : X} (p : Path x y)
    (hp : Set.range p ⊆ U i) (a b c : unitInterval)
    (hab : Set.range (p.subpath a b) ⊆ U i)
    (hbc : Set.range (p.subpath b c) ⊆ U i)
    (hac : Set.range (p.subpath a c) ⊆ U i) :
    d.localValue i (p.subpath a b) hab ≫ d.localValue i (p.subpath b c) hbc =
      d.localValue i (p.subpath a c) hac := by
  rw [d.localValue_subpath i p hp a b hab,
    d.localValue_subpath i p hp b c hbc, d.localValue_subpath i p hp a c hac]
  have h : (Path.Homotopic.Quotient.mk (((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y
      := ⟨_, hp (p).target_mem_range⟩) p hp)).subpath a b)).trans
      (Path.Homotopic.Quotient.mk (((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_,
          hp (p).target_mem_range⟩) p hp)).subpath b c)) =
      Path.Homotopic.Quotient.mk (((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_,
          hp (p).target_mem_range⟩) p hp)).subpath a c) :=
    by
      exact Quotient.sound (show Path.Homotopic
        ((((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_, hp
            (p).target_mem_range⟩) p hp)).subpath a b).trans (((Path.inSubset (x := ⟨_, hp
            (p).source_mem_range⟩) (y := ⟨_, hp (p).target_mem_range⟩) p hp)).subpath b c))
        (((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_, hp (p).target_mem_range⟩)
            p hp)).subpath a c) from
          ⟨Path.Homotopy.subpathTransSubpath ((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩)
              (y := ⟨_, hp (p).target_mem_range⟩) p hp)) a b c⟩)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, FundamentalGroupoid.comp_eq]
  exact congrArg (fun q : Path.Homotopic.Quotient (((Path.inSubset (x := ⟨_, hp
      (p).source_mem_range⟩) (y := ⟨_, hp (p).target_mem_range⟩) p hp)) a) (((Path.inSubset (x
      := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_, hp (p).target_mem_range⟩) p hp)) c) =>
    (d.transport i (((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_, hp
        (p).target_mem_range⟩) p hp)) a)).hom ≫ (d.chart i).map q ≫
      (d.transport i (((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_, hp
          (p).target_mem_range⟩) p hp)) c)).inv) h

/-- Compatibility can be used with any proofs of containment in the two charts. -/
theorem localValue_eq_of_overlap (hc : d.Compatible) (i j : ι)
    {x y : X} (p : Path x y) (hi : Set.range p ⊆ U i)
    (hj : Set.range p ⊆ U j) : d.localValue i p hi = d.localValue j p hj :=
  hc i j p hi hj

end ChartData

end FundamentalGroupoid.OpenCover
