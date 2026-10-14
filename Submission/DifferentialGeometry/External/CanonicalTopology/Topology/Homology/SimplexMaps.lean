import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The original image simplices and coefficient-one chain maps -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap
open scoped _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original image singular simplex under the actual continuous map. -/
def integralSingularSimplexMap (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    integralSingularSimplex n Y :=
  (TopCat.toSSet.map (TopCat.ofHom f)).app (Opposite.op ⦋n⦌) σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSimplexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSimplexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSimplexMap ``Submission.DifferentialGeometry.Topology.integralSingularSimplexMap

/-- Its continuous map is exactly postcomposition of the original simplex. -/
theorem integralSingularSimplexMap_apply (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    integralSingularSimplexEquiv n Y (integralSingularSimplexMap n f σ) =
      f.comp (integralSingularSimplexEquiv n X σ) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSimplexMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSimplexMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSimplexMap_apply ``Submission.DifferentialGeometry.Topology.integralSingularSimplexMap_apply

/-- The original chain map takes a coefficient-one simplex to its same
coefficient-one image simplex. -/
theorem integralSimplexChain_map (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    (integralSingularChainMap f).f n (integralSimplexChain n σ) =
      integralSimplexChain n (integralSingularSimplexMap n f σ) := by
  exact congrArg (fun h : integralSingularCoefficients.{u} ⟶
    (integralSingularChains Y).X n => h (ULift.up 1))
      (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSet.obj (TopCat.of Y))
        (TopCat.toSSet.map (TopCat.ofHom f))
        integralSingularCoefficients σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSimplexChain_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSimplexChain_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSimplexChain_map ``Submission.DifferentialGeometry.Topology.integralSimplexChain_map

end DifferentialGeometry.Topology
