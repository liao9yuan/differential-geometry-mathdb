import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Relative
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.LinearAlgebra.FreeModule.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The actual singular simplices form a basis of the actual chain groups -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Module
open scoped _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

/-- The actual simplices in the pinned singular simplicial set. -/
abbrev integralSingularSimplex (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSimplex ``Submission.DifferentialGeometry.Topology.integralSingularSimplex

/-- These are exactly continuous maps from the original barycentric simplex. -/
def integralSingularSimplexEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularSimplex n X ≃ C(stdSimplex ℝ (Fin (n + 1)), X) :=
  (TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSimplexEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSimplexEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSimplexEquiv ``Submission.DifferentialGeometry.Topology.integralSingularSimplexEquiv

/-- Identify the actual categorical coproduct chain group with the explicit
finite formal sums of its same actual simplices. -/
def integralSingularChainFinsuppIso (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralSingularChains X).X n ≅
      ModuleCat.of ℤ (integralSingularSimplex n X →₀ ULift.{u} ℤ) :=
  ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan
    integralSingularCoefficients n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (integralSingularSimplex n X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainFinsuppIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainFinsuppIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainFinsuppIso ``Submission.DifferentialGeometry.Topology.integralSingularChainFinsuppIso

/-- Integral coordinates of an actual singular chain, with the coefficient
universe lift removed by its actual linear equivalence. -/
def integralSingularChainRepr (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralSingularChains X).X n ≃ₗ[ℤ] (integralSingularSimplex n X →₀ ℤ) :=
  (integralSingularChainFinsuppIso n X).toLinearEquiv.trans
    (Finsupp.mapRange.linearEquiv ULift.moduleEquiv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainRepr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainRepr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainRepr ``Submission.DifferentialGeometry.Topology.integralSingularChainRepr

/-- The basis is indexed by the actual singular simplices, rather than a
postulated freely generated replacement for the original chain group. -/
def integralSingularChainBasis (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Basis (integralSingularSimplex n X) ℤ ((integralSingularChains X).X n) :=
  Basis.ofRepr (integralSingularChainRepr n X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainBasis ``Submission.DifferentialGeometry.Topology.integralSingularChainBasis

/-- Freeness of each original chain group has the preceding explicit basis. -/
instance integralSingularChain_free (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Module.Free ℤ ((integralSingularChains X).X n) :=
  Module.Free.of_basis (integralSingularChainBasis n X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChain_free then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChain_free"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChain_free ``Submission.DifferentialGeometry.Topology.integralSingularChain_free

/-- In particular the original chain groups are projective, as needed for
the integral universal coefficient argument. -/
instance integralSingularChain_projective (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Projective ((integralSingularChains X).X n) :=
  ModuleCat.projective_of_free (integralSingularChainBasis n X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChain_projective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChain_projective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChain_projective ``Submission.DifferentialGeometry.Topology.integralSingularChain_projective

end DifferentialGeometry.Topology
