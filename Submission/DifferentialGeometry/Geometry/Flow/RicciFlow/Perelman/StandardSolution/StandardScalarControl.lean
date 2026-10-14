import Submission.DifferentialGeometry.Geometry.Curvature.ScalarControlsRm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureOperator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem PartialStandardSolution.normSq_rm_le_scalar_sq
    (S : PartialStandardSolution) (t : ℝ) (ht : t ∈ S.domain) (x : E3) :
    normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x) ≤
      100 ^ 2 * (metricScalarAt (S.metric t) x) ^ 2 := by
  exact DifferentialGeometry.Geometry.Curvature.normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
    (S.metric t) x (by simp) (S.curvatureOperator_nonnegative t ht x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.normSq_rm_le_scalar_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.normSq_rm_le_scalar_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.normSq_rm_le_scalar_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.normSq_rm_le_scalar_sq

end DifferentialGeometry.PDE.RicciFlow

end
