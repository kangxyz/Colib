/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.PullbackQuotient
public import Colib.CategoryTheory.Waldhausen.Rows.FlagMaps
public import Colib.CategoryTheory.ExactCategory.Filtration.PullbackFlag


/-! # Pullback of admissible flags preserves their interval quotients

The pullback of a kernel is the kernel of the composite. With an admissible
epimorphism this composite is again a deflation, so its original cokernel
object is the actual quotient of the pulled-back inclusion.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuotientRows
open ExactCategory.Filtration

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- The canonical quotient transformation for a pullback flag is componentwise
an isomorphism, proved from exact-category kernel and cokernel properties. -/
theorem pullbackFlag_quotient_isIso {n : SimplexCategory} (A : Fin (n.len + 1) ⥤ C)
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
    {P : C} (p : P ⟶ A.obj (Fin.last n.len)) (hp : E.deflation p)
    [∀ i : Fin (n.len + 1), HasPullback p (flagTopMap A i)] (ij : Interval n) :
    IsIso ((quotientNatTrans E (pullbackFlag_inflation E A p hp hA) hA
      (pullbackFlagToOriginal A p)).app ij) := by
  let sq := pullbackFlag_map_isPullback A p (homOfLE ij.2)
  let hc := flagQuotient_conflation E hA ij
  let hs := E.pullback_conflation_same_quotient sq (flagQuotient_zero E hA ij) hc
    (pullbackFlagToOriginal_deflation E A p hp ij.1.2)
  let e := (flagQuotientIsCokernel E (pullbackFlag_inflation E A p hp hA)
    ij).coconePointUniqueUpToIso
    (E.cokernel _ hs)
  have he : (quotientNatTrans E (pullbackFlag_inflation E A p hp hA) hA
      (pullbackFlagToOriginal A p)).app ij = e.hom := by
    apply (cancel_epi (flagQuotient E (pullbackFlag A p) (pullbackFlag_inflation E A p hp hA) ij)).1
    rw [flagQuotient_quotientNatTrans]
    exact ((flagQuotientIsCokernel E (pullbackFlag_inflation E A p hp hA)
      ij).comp_coconePointUniqueUpToIso_hom
      (E.cokernel _ hs) WalkingParallelPair.one).symm
  rw [he]
  infer_instance

/-- The quotient rows of a flag and its admissible pullback are canonically isomorphic. -/
def pullbackFlagQuotientIso {n : SimplexCategory} (A : Fin (n.len + 1) ⥤ C)
    (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
    {P : C} (p : P ⟶ A.obj (Fin.last n.len)) (hp : E.deflation p)
    [∀ i : Fin (n.len + 1), HasPullback p (flagTopMap A i)] :
    quotientDiagram E (pullbackFlag A p) (pullbackFlag_inflation E A p hp hA) ≅
      quotientDiagram E A hA := by
  letI (ij : Interval n) : IsIso ((quotientNatTrans E
      (pullbackFlag_inflation E A p hp hA) hA (pullbackFlagToOriginal A p)).app ij) :=
    pullbackFlag_quotient_isIso E A hA p hp ij
  exact NatIso.ofComponents
    (fun ij ↦ asIso ((quotientNatTrans E (pullbackFlag_inflation E A p hp hA) hA
      (pullbackFlagToOriginal A p)).app ij))
    (fun f ↦ (quotientNatTrans E (pullbackFlag_inflation E A p hp hA) hA
      (pullbackFlagToOriginal A p)).naturality f)

end CategoryTheory.Waldhausen.QuotientRows
