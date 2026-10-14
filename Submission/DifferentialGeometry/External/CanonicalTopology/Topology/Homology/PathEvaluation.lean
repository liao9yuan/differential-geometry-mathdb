import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathChains

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Evaluation of the same original path simplex -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap
open scoped _root_.Simplicial _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {x y : X}

/-- The actual singular path simplex evaluates the original path at the
original barycentric interval parameter. -/
theorem integralPathSimplex_apply (p : Path x y) (t : stdSimplex ℝ (Fin 2)) :
    integralSingularSimplexEquiv 1 X (integralPathSimplex p) t =
      p (stdSimplexHomeomorphUnitInterval t) := by
  exact congrArg (fun f : C(stdSimplex ℝ (Fin 2), X) => f t)
    ((integralSingularSimplexEquiv 1 X).apply_symm_apply
      (p.toContinuousMap.comp ⟨stdSimplexHomeomorphUnitInterval,
        stdSimplexHomeomorphUnitInterval.continuous⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathSimplex_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathSimplex_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathSimplex_apply ``Submission.DifferentialGeometry.Topology.integralPathSimplex_apply

end DifferentialGeometry.Topology
