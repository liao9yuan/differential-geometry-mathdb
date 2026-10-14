import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalChartJets
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.JetOperators
import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.DifferentiatedBasisIdentityOffCenter

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Analysis _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Geometry.Operator

export DifferentialGeometry.CheegerGromovCompactness
  (mapCInfConvergence_jet2 mapCInfConvergence_chartJetOperator
    mapCInfConvergence_chartChristoffel_of_gram mapCInfConvergence_chartRicci_of_gram)

section Flow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem solution_chartRicci_jets_tendsto_terminal
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (p : M) :
    ∃ W : Set E, IsOpen W ∧ extChartAt I p p ∈ W ∧ W ⊆ (extChartAt I p).target ∧
      ∀ r : ℕ, ∀ i j : Fin (Module.finrank ℝ E), ∀ K : Set E, IsCompact K → K ⊆ W →
        TendstoUniformlyOn (fun t => iteratedFDeriv ℝ r
          (chartRicciTensor (I := I) (S.base.metric t) p i j))
          (iteratedFDeriv ℝ r (chartRicciTensor (I := I) (S.base.metric b) p i j))
          (𝓝[<] b) K := by
  obtain ⟨W, hW, hpW, hWt, hgram⟩ := solution_chartGram_jets_tendsto_terminal
    S hS hab hslab hreg p
  refine ⟨W, hW, hpW, hWt, ?_⟩
  intro r i j K hK hKW
  apply tendstoUniformlyOn_of_seq_tendstoUniformlyOn
  intro τ hτ
  have hseq (u v : Fin (Module.finrank ℝ E)) : MapCInfConvergenceOnCompacts W
      (fun n => chartGramOnE (I := I) (S.base.metric (τ n)) p u v)
      (chartGramOnE (I := I) (S.base.metric b) p u v) := by
    intro Q _hQ hQW m
    apply mapCPConvergenceOn_of_tendstoUniformlyOn hW hQW
      (fun n => ((chartGramOnE_contDiffOn (I := I) (S.base.metric (τ n)) p u v).mono hWt).of_le
        (by exact_mod_cast le_top))
      (((chartGramOnE_contDiffOn (I := I) (S.base.metric b) p u v).mono hWt).of_le
        (by exact_mod_cast le_top))
    intro q _hq
    exact ((hgram q u v).seq_tendstoUniformlyOn τ hτ).mono hQW
  have hric := mapCInfConvergence_chartRicci_of_gram (fun n => S.base.metric (τ n))
    (S.base.metric b) p hW hWt hseq i j
  exact hric.tendstoUniformlyOn_iteratedFDeriv hW hK hKW
    (fun n => (chartRicciTensor_contDiffOn_interior (I := I) (S.base.metric (τ n)) p i j).mono
      (interior_maximal hWt hW))
    ((chartRicciTensor_contDiffOn_interior (I := I) (S.base.metric b) p i j).mono
      (interior_maximal hWt hW)) r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartRicci_jets_tendsto_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartRicci_jets_tendsto_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartRicci_jets_tendsto_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartRicci_jets_tendsto_terminal

end Flow

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
