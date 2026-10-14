import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBoundary
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Cycles

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The original paths as actual integral singular chains -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Module
open scoped _root_.Simplicial _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {x y : X}

/-- The original point as a coefficient-one singular vertex. -/
def integralVertexChain (x : X) : (integralSingularChains X).X 0 :=
  integralSimplexChain 0 (TopCat.toSSetObj₀Equiv.symm x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralVertexChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralVertexChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralVertexChain ``Submission.DifferentialGeometry.Topology.integralVertexChain

/-- The original path, with its original parameter, as a singular 1-simplex. -/
def integralPathSimplex (p : Path x y) : integralSingularSimplex 1 X :=
  TopCat.toSSetObj₁Equiv.symm (TopCat.pathEquiv.symm p).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathSimplex ``Submission.DifferentialGeometry.Topology.integralPathSimplex

/-- The original path as a coefficient-one singular chain. -/
def integralPathChain (p : Path x y) : (integralSingularChains X).X 1 :=
  integralSimplexChain 1 (integralPathSimplex p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathChain ``Submission.DifferentialGeometry.Topology.integralPathChain

/-- Its original boundary is exactly target minus source. -/
theorem integralPathChain_boundary (p : Path x y) :
    (integralSingularChains X).d 1 0 (integralPathChain p) =
      integralVertexChain y - integralVertexChain x := by
  change (integralSingularChains X).d 1 0 (integralSimplexChain 1
    (TopCat.toSSetObj₁Equiv.symm (TopCat.pathEquiv.symm p).hom)) = _
  rw [integralSimplexChain_boundary_one]
  simp only [TopCat.δ_zero_toSSetObj₁Equiv.symm, TopCat.δ_one_toSSetObj₁Equiv.symm]
  change integralVertexChain (p 1) - integralVertexChain (p 0) = _
  rw [Path.target, Path.source]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathChain_boundary ``Submission.DifferentialGeometry.Topology.integralPathChain_boundary

/-- The original interval path of an arbitrary original singular 1-simplex. -/
def integralSimplexPath (σ : integralSingularSimplex 1 X) :
    Path (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
      (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) where
  toFun t := TopCat.toSSetObj₁Equiv σ (TopCat.I.homeomorph.symm t)
  continuous_toFun := (TopCat.toSSetObj₁Equiv σ).hom.continuous.comp TopCat.I.homeomorph.symm.continuous
  source' := TopCat.toSSetObj₁Equiv_apply_zero σ
  target' := TopCat.toSSetObj₁Equiv_apply_one σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSimplexPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSimplexPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSimplexPath ``Submission.DifferentialGeometry.Topology.integralSimplexPath

/-- Converting an original singular edge to a path and back preserves that
same simplex, rather than choosing a homotopic substitute. -/
theorem integralPathSimplex_simplexPath (σ : integralSingularSimplex 1 X) :
    integralPathSimplex (integralSimplexPath σ) = σ := by
  apply TopCat.toSSetObj₁Equiv.injective
  change TopCat.toSSetObj₁Equiv (TopCat.toSSetObj₁Equiv.symm
    (TopCat.pathEquiv.symm (integralSimplexPath σ)).hom) = TopCat.toSSetObj₁Equiv σ
  rw [Equiv.apply_symm_apply]
  ext t
  change TopCat.toSSetObj₁Equiv σ (TopCat.I.homeomorph.symm (TopCat.I.homeomorph t)) =
    TopCat.toSSetObj₁Equiv σ t
  rw [Homeomorph.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathSimplex_simplexPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathSimplex_simplexPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathSimplex_simplexPath ``Submission.DifferentialGeometry.Topology.integralPathSimplex_simplexPath

/-- Hence every original degree-one basis chain is the chain of its same
actual interval path. -/
theorem integralPathChain_simplexPath (σ : integralSingularSimplex 1 X) :
    integralPathChain (integralSimplexPath σ) = integralSimplexChain 1 σ := by
  unfold integralPathChain
  rw [integralPathSimplex_simplexPath]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathChain_simplexPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathChain_simplexPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathChain_simplexPath ``Submission.DifferentialGeometry.Topology.integralPathChain_simplexPath

end DifferentialGeometry.Topology
