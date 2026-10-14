import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Carrier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped _root_.BigOperators _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow

section GramOperator

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem chartGramOp_continuousOn_carrier
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.carrier) (x₀ : M) {K : Set E}
    (hK : K ⊆ interior (extChartAt I x₀).target) :
    ContinuousOn (chartGramOp (I := I) G x₀) (J ×ˢ K) := by
  exact DifferentialGeometry.Geometry.Curvature.chartGramOp_continuousOn_of_carrier
    hG hJ x₀ (hK.trans interior_subset)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.chartGramOp_continuousOn_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.chartGramOp_continuousOn_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.chartGramOp_continuousOn_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.chartGramOp_continuousOn_carrier

end GramOperator

end DifferentialGeometry.PDE.RicciFlow

end
