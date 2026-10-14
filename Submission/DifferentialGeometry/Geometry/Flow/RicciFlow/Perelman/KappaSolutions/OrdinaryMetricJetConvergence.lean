import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.TimeJetConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OrdinaryMetricJetFormula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance ordinaryConvergenceC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ordinaryConvergenceC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ordinaryConvergenceC1 target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem closedWindow_metric_time_jet_components_contDiffOn {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = _root_.Set.Icc a b) (hregular : _root_.Set.Ioo a b ⊆ D.regular) (ht : t ∈ _root_.Set.Icc c b)
    (q : ℕ) (x₀ : M) {W : Set E} (hWt : W ⊆ (extChartAt I x₀).target)
    (slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun y =>
      (iteratedDerivWithin q
        (fun s => metricTensorField (S.base.metric s) ((extChartAt I x₀).symm y)) (_root_.Set.Icc c b) t)
        (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) W := by
  exact ordinary_metric_time_jet_components_contDiffOn_of_closed_interval
    S hS hac hcb hcarrier hregular ht q x₀ hWt slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_components_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_components_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_components_contDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_components_contDiffOn


theorem closedWindow_metric_time_jet_components_mapCInf_of_gram {D D₀ : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D₀) (hS₀ : IsSolutionOn S₀)
    {a c b a₀ c₀ b₀ : ℝ} (hac : a < c) (hcb : c < b)
    (ha₀c₀ : a₀ < c₀) (hc₀b₀ : c₀ < b₀)
    (hcarrier : D.carrier = _root_.Set.Icc a b) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (hcarrier₀ : D₀.carrier = _root_.Set.Icc a₀ b₀) (hregular₀ : _root_.Set.Ioo a₀ b₀ ⊆ D₀.regular)
    (τ : ℕ → ℝ) (hτ : ∀ n, τ n ∈ _root_.Set.Icc c b) (t₀ : ℝ) (ht₀ : t₀ ∈ _root_.Set.Icc c₀ b₀) (x₀ : M)
    {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x₀).target)
    (hgram : ∀ i j : CoordinateIdx (𝕜 := ℝ) E, MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) ((S n).base.metric (τ n)) x₀ i j)
      (chartGramOnE (I := I) (S₀.base.metric t₀) x₀ i j)) (q : ℕ)
    (slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E) :
    MapCInfConvergenceOnCompacts W
      (fun n y =>
        (iteratedDerivWithin q
          (fun s => metricTensorField ((S n).base.metric s) ((extChartAt I x₀).symm y)) (_root_.Set.Icc c b) (τ n))
          (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y)))
      (fun y =>
        (iteratedDerivWithin q
          (fun s => metricTensorField (S₀.base.metric s) ((extChartAt I x₀).symm y)) (_root_.Set.Icc c₀ b₀) t₀)
          (fun j => chartBasisVecFiber (I := I) x₀ (slots j) ((extChartAt I x₀).symm y))) := by
  exact ordinary_metric_time_jet_components_mapCInf_of_gram_on_closed_interval
    S hS S₀ hS₀ hac hcb ha₀c₀ hc₀b₀ hcarrier hregular hcarrier₀ hregular₀
    τ hτ t₀ ht₀ x₀ hW hWt hgram q slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_components_mapCInf_of_gram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_components_mapCInf_of_gram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_components_mapCInf_of_gram ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.closedWindow_metric_time_jet_components_mapCInf_of_gram

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
