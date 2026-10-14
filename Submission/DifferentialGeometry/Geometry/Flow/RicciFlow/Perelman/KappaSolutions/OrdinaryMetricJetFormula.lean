import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TimeJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureFields

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.BigOperators

section Ancient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance ordinaryMetricC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ordinaryMetricC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ordinaryMetricC1 target :: scope.openDecls } }


theorem closedWindow_metric_time_jet_component_eq_polynomial
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Set.Icc a b) (hregular : Set.Ioo a b ⊆ D.regular)
    (ht : t ∈ Set.Icc c b) (x : M) {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (TangentSpace I x)) (q : ℕ) (slots : Fin 2 → Fin n) :
    component0S (I := I) basis
      (iteratedDerivWithin (q + 1) (fun s => metricTensorField (S.base.metric s) x) (Set.Icc c b) t) slots =
    MvPolynomial.eval
      (curvatureTimePolynomialValues S.base.metric
        (fun r s => mixedCurvatureTensor S 0 r s x) basis t)
      (ordinaryMetricJetPolynomial q slots) := by
  exact ordinary_metric_time_jet_component_eq_polynomial_on_closed_interval
    S hS hac hcb hcarrier hregular ht x basis q slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_component_eq_polynomial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_component_eq_polynomial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_component_eq_polynomial ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_component_eq_polynomial

end Ancient
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
