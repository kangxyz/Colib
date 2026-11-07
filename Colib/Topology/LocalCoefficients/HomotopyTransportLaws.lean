/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.MapComposition

/-!
Adapted from `Quillen/Topology/LocalCoefficients/HomotopyTransportLaws.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual coefficient maps.

 # Genuine coefficient transport under concatenation and endpoint casts -/

@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Concatenating actual homotopies composes their actual coefficient transports. -/
theorem homotopyPullbackIso_trans_hom {f g h : C(X, Y)}
    (H : f.Homotopy g) (K : g.Homotopy h) (A : System.{u, u} Y) :
    (homotopyPullbackIso (H.trans K) A).hom =
      (homotopyPullbackIso H A).hom ≫ (homotopyPullbackIso K A).hom := by
  apply NatTrans.ext
  funext x
  exact transport_trans A (H.evalAt x.as) (K.evalAt x.as)

/-- Casting endpoints keeps the actual homotopy and records precisely the equality transports. -/
theorem homotopyPullbackIso_cast_hom {f g f' g' : C(X, Y)}
    (H : f.Homotopy g) (hf : f = f') (hg : g = g') (A : System.{u, u} Y) :
    (homotopyPullbackIso (H.cast hf hg) A).hom =
      eqToHom (congrArg (fun k ↦ pullback k A) hf.symm) ≫
        (homotopyPullbackIso H A).hom ≫ eqToHom (congrArg (fun k ↦ pullback k A) hg) := by
  subst f'
  subst g'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end FundamentalGroupoid.LocalCoefficients
