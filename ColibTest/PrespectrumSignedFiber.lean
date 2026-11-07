import Colib.Topology.Prespectrum.FiberOmega
import Colib.Topology.Prespectrum.FiberConnectivity
import Colib.Topology.Prespectrum.FiberLiftConnecting
import Colib.Topology.Prespectrum.FiberConnectingLevelOne

noncomputable section

open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace PrespectrumSignedFiberTests

variable {A E F : LoopPrespectrum.{u}} (f : E ⟶ F)

-- The structure time and the fiber-path time remain independent coordinates.
example (n : ℕ) (z : (homotopyFiber f).space n) (s t : unitInterval) :
    (((homotopyFiber f).structureMap n z t).1.2 s) =
      F.structureMap n (z.1.2 s) t := rfl

example (n : ℕ) (z : (homotopyFiber f).space n) :
    (homotopyFiberProjection f).map n z = z.1.1 := rfl

example (n : ℕ) (z : (homotopyFiber f).space n) (s : unitInterval) :
    (homotopyFiberNullHomotopy f).level n (s, z) = z.1.2 s := rfl

example (g : A ⟶ E) (H : Homotopy (g ≫ f) (zeroHom A F))
    (n : ℕ) (x : A.space n) :
    ((homotopyFiberLift f g H).map n x).1.1 = g.map n x := rfl

example (g : A ⟶ E) (H : Homotopy (g ≫ f) (zeroHom A F))
    (n : ℕ) (x : A.space n) (s : unitInterval) :
    ((homotopyFiberLift f g H).map n x).1.2 s = H.level n (s, x) := rfl

example (hE : E.IsOmega) (hF : F.IsOmega) : (homotopyFiber f).IsOmega :=
  homotopyFiber_isOmega f hE hF

-- Every integer degree, with no Omega hypothesis in stable fiber exactness.
example (d : ℤ) :
    Function.Exact ((stableHomotopyFunctor (d + 1)).map f) (stableFiberConnecting f d) ∧
    Function.Exact (stableFiberConnecting f d)
      ((stableHomotopyFunctor d).map (homotopyFiberProjection f)) ∧
    Function.Exact ((stableHomotopyFunctor d).map (homotopyFiberProjection f))
      ((stableHomotopyFunctor d).map f) := stableFiberLongExactSequence f d

-- Negative-one vanishing requires the actual degree-zero surjectivity.
example (hE : ∀ d : ℤ, d < 0 → Subsingleton (stableHomotopyGroup E d))
    (hF : ∀ d : ℤ, d < 0 → Subsingleton (stableHomotopyGroup F d))
    (h0 : Function.Surjective ((stableHomotopyFunctor 0).map f)) :
    Subsingleton (stableHomotopyGroup (homotopyFiber f) (-1)) :=
  stableFiber_neg_subsingleton_of_connective f hE hF h0 (-1) (by omega)

example (hF : F.IsOmega) (hFib : (homotopyFiber f).IsOmega)
    (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (a : HomotopyGroup.Pi (n + 2) (F.space 1) (F.point 1)) :
    stableFiberConnecting f (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup F) κ)
          (levelOneStableEquiv F hF (n + 1) (Additive.ofMul a))) =
      -(levelOneStableEquiv (homotopyFiber f) hFib n
        (Additive.ofMul (HomotopyFiber.connectingHom (f.map 1) (F.point 1)
          (E.point 1) (f.map_point 1) n a))) :=
  stableFiberConnecting_levelOneStableEquiv_sign f hF hFib n κ a

-- The lowest boundary already contains the same single minus.
example (hF : F.IsOmega) (hFib : (homotopyFiber f).IsOmega)
    (a : HomotopyGroup.Pi 2 (F.space 1) (F.point 1)) :
    stableFiberConnecting f 0 (levelOneStableEquiv F hF 1 (Additive.ofMul a)) =
      -(levelOneStableEquiv (homotopyFiber f) hFib 0
        (Additive.ofMul (HomotopyFiber.connectingHom (f.map 1) (F.point 1)
          (E.point 1) (f.map_point 1) 0 a))) := by
  simpa using stableFiberConnecting_levelOneStableEquiv_sign f hF hFib 0 rfl a

example (g : A ⟶ E) (H : Homotopy (g ≫ f) (zeroHom A F)) (d : ℤ)
    [IsIso ((stableHomotopyFunctor d).map (homotopyFiberLift f g H))] :
    stableFiberLiftConnecting g f H d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift f g H) =
      stableFiberConnecting f d := stableFiberLiftConnecting_comp_lift g f H d

end PrespectrumSignedFiberTests
