import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.JetLipschitzClosure
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Jets.ChartRicciLieLipschitz
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.GramRealizeDifferenceJet
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.RemainderPolynomial

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Calculus
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem hasChartJetLip_chartDeTurckRicciRHS
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i k : Fin (Module.finrank ℝ E)) :
    HasChartJetLip g₁ g₂ α K
      (fun g => fun z => chartDeTurckRicciRHS (I := I) g g_bg α i k z) 2 := by
  have hRic := (hasChartJetLip_chartRicciTensor (I := I) (M := M) g₁ g₂ α hK hKsub i k).const_smul
    hKsub (-2 : ℝ)
  have hLie := hasChartJetLip_chartLieDeTurckComp (I := I) (M := M) g₁ g₂ g_bg α hK hKsub i k
  have hAdd := HasChartJetLip.add hKsub hRic hLie
  have hmax : _root_.Max.max 2 2 = 2 := by norm_num
  rw [hmax] at hAdd
  refine hAdd.congr ?_
  intro g
  funext z
  rw [chartDeTurckRicciRHS_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasChartJetLip_chartDeTurckRicciRHS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasChartJetLip_chartDeTurckRicciRHS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasChartJetLip_chartDeTurckRicciRHS ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.hasChartJetLip_chartDeTurckRicciRHS

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem chartDeTurckRicciRHS_realize_seminorm_le_chartComponentJetSeminormSum
    (g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g_bg 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g_bg (ccTensorBilinSymm (I := I) g_bg T') δ')
    (α : M) {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i k : Fin (Module.finrank ℝ E)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      iteratedFDerivSeminorm N
          (fun z => chartDeTurckRicciRHS (I := I)
              (tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ) g_bg α i k z -
            chartDeTurckRicciRHS (I := I)
              (tensorSectionRealizeMetric (I := I) g_bg T' hδ'_lt hδ') g_bg α i k z)
          (interior (extChartAt I α).target) y ≤
        C * chartComponentJetSeminormSum (I := I) (M := M) g_bg (T - T') α (N + 2) y := by
  classical
  set g₁ := tensorSectionRealizeMetric (I := I) g_bg T hδ_lt hδ with hg₁_def
  set g₂ := tensorSectionRealizeMetric (I := I) g_bg T' hδ'_lt hδ' with hg₂_def
  obtain ⟨C, hC_pos, hC⟩ :=
    (hasChartJetLip_chartDeTurckRicciRHS (I := I) (M := M) g₁ g₂ g_bg α hK hKsub i k).seminorm_le N
  refine ⟨C * ((Module.finrank ℝ E) : ℝ), by positivity, fun y hy => ?_⟩
  have hyint : y ∈ interior (extChartAt I α).target := hKsub hy
  refine (hC y hy).trans ?_
  have hgram := chartGramJetDiffSeminormSum_realize_le_chartComponentJetSeminormSum (I := I) (M := M)
    g_bg T T' hδ_lt hδ hδ'_lt hδ' α (N + 2) hyint
  rw [hg₁_def, hg₂_def]
  calc C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + 2) g₁ g₂ α
        (interior (extChartAt I α).target) y
      ≤ C * (((Module.finrank ℝ E) : ℝ) *
          chartComponentJetSeminormSum (I := I) (M := M) g_bg (T - T') α (N + 2) y) :=
        mul_le_mul_of_nonneg_left hgram hC_pos.le
    _ = (C * ((Module.finrank ℝ E) : ℝ)) *
          chartComponentJetSeminormSum (I := I) (M := M) g_bg (T - T') α (N + 2) y := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_realize_seminorm_le_chartComponentJetSeminormSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_realize_seminorm_le_chartComponentJetSeminormSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_realize_seminorm_le_chartComponentJetSeminormSum ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_realize_seminorm_le_chartComponentJetSeminormSum

end DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
