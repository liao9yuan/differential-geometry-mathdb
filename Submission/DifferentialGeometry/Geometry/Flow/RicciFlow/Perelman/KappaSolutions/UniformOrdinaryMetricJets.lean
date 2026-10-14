import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.UniformTimeJetConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OrdinaryMetricJetConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

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
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Integral.Measure

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance uniformOrdinaryC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformOrdinaryC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformOrdinaryC1 target :: scope.openDecls } }


omit [BoundarylessManifold I M] in
theorem uniform_metric_time_jets_on_compact_closedWindow
    {D : ℕ → RealTimeInterval} {D₀ : RealTimeInterval}
    (S : (n : ℕ) → SolutionOn (I := I) (M := M) (D n)) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D₀) (hS₀ : IsSolutionOn S₀)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : ∀ n, _root_.Set.Icc a b ⊆ (D n).carrier) (hregular : ∀ n, _root_.Set.Ioo a b ⊆ (D n).regular)
    (hslab₀ : _root_.Set.Icc a b ⊆ D₀.carrier) (hregular₀ : _root_.Set.Ioo a b ⊆ D₀.regular)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ _root_.Set.Icc c b) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ U →
      ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) ((S n).base.metric t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I) (S₀.base.metric t) p i j) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r q : ℕ)
    (slots : Fin 2 → Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField ((S n).base.metric s) ((extChartAt I p).symm z)) (_root_.Set.Icc c b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y -
        iteratedFDeriv ℝ r (fun z =>
          (iteratedDerivWithin q
            (fun s => metricTensorField (S₀.base.metric s) ((extChartAt I p).symm z)) (_root_.Set.Icc c b) t)
            (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε := by
  let D' := RealTimeInterval.closed a b (hac.trans hcb).le
  exact uniform_ordinary_metric_jets_on_compact_time_of_closed_interval
    (fun n => (S n).timeRestrict D')
    (fun n => isSolutionOn_timeRestrict (hS n) (hslab n) (hregular n))
    (S₀.timeRestrict D') (isSolutionOn_timeRestrict hS₀ hslab₀ hregular₀)
    hac hcb rfl Subset.rfl hJ hJb p hU hUt hgram hK hKU r q slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_metric_time_jets_on_compact_closedWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_metric_time_jets_on_compact_closedWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_metric_time_jets_on_compact_closedWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_metric_time_jets_on_compact_closedWindow

end Geometry
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
