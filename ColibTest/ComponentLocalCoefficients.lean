module

import Colib.Topology.LocalCoefficients.ComponentComparison

open CategoryTheory
open FundamentalGroupoid.LocalCoefficients

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

-- The exact component preimage is retained, and the target system is arbitrary.
example (f : C(X, Y)) (x : X) (y : Y)
    (hpre : ∀ z, f z ∈ pathComponent y ↔ z ∈ pathComponent x)
    (hf : ∀ B : System.{u, u} Y, QuasiIso (pushforwardChainMap f B))
    (A : System.{u, u} (pathComponent y)) :
    QuasiIso (pushforwardChainMap (componentMap f x y hpre) A) :=
  componentMap_quasiIso f x y hpre hf A

-- Support is a property of actual coefficient fibers, not a supplied equivalence.
example (U : Set X) (A : System.{u, u} X)
    (hU : ∀ a ∈ U, ∀ b, Joined a b → b ∈ U)
    (hA : ∀ x, x ∉ U → Limits.IsZero (fiber A x)) :
    IsIso (pushforwardChainMap (subspaceInclusion U) A) :=
  subspaceInclusion_pushforwardChainMap_isIso_of_support U hU A hA

#print axioms FundamentalGroupoid.LocalCoefficients.componentMap_quasiIso
#print axioms FundamentalGroupoid.LocalCoefficients.componentExtensionPullbackIso
#print axioms
  FundamentalGroupoid.LocalCoefficients.subspaceInclusion_pushforwardChainMap_isIso_of_support
