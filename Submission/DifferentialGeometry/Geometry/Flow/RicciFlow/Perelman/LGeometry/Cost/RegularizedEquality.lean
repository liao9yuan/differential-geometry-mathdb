import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lCost_eq_lRegularizedCostC1
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x y : M)
    (tau : ℝ) (htau : 0 ≤ tau) :
    lCost S T x y tau = lRegularizedCostC1 S T 0 (Real.sqrt tau) x y := by
  unfold lCost lRegularizedCostC1
  simp_rw [lLength_squareRootReparametrization_eq_lRegularizedAction S T _ tau htau]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_lRegularizedCostC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_lRegularizedCostC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_lRegularizedCostC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCost_eq_lRegularizedCostC1

end DifferentialGeometry.PDE.RicciFlow.Perelman
