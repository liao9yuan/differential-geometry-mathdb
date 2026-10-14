import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Basic
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Local
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Defs
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.QuasilinearMetricShortTimeExistence
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.Regularity.JointChart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Construction.QuasilinearExistence
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.SlotSwapEquivariance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology _root_.BigOperators
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Parabolic
    DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.PDE.DeTurck
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ccTensor02Symm domDomCongrSection)

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M]
      [I.Boundaryless] [T2Space M]

private theorem rawTensorConnLapSmooth_ccTensor02Symm
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) :
    rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S) =
      ccTensor02Symm (I := I) (M := M) g₀ (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) := by
  have hhalf : ∀ W : SmoothCcTensor g₀ 0 2,
      (1 / 2 : ℝ) • W + (1 / 2 : ℝ) • W = W := fun W => by
    rw [← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
  have hzero : rawTensorConnLapSmooth (I := I) g₀ 0 2 (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g₀ 0 2 S S
    rwa [sub_self, sub_self] at h
  have hadd : ∀ A B : SmoothCcTensor g₀ 0 2,
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (A + B) =
        rawTensorConnLapSmooth (I := I) g₀ 0 2 A +
          rawTensorConnLapSmooth (I := I) g₀ 0 2 B := by
    intro A B
    have hAB : A + B = A - (0 - B) := by rw [zero_sub, sub_neg_eq_add]
    rw [hAB, rawTensorConnLapSmooth_sub (I := I) (M := M) g₀ 0 2 A (0 - B),
      rawTensorConnLapSmooth_sub (I := I) (M := M) g₀ 0 2 0 B, hzero, zero_sub, sub_neg_eq_add]
  have hLV : rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S) +
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S) =
      rawTensorConnLapSmooth (I := I) g₀ 0 2 S +
        domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) := by
    rw [← hadd, ccTensor02Symm, hhalf, hadd,
      rawTensorConnLapSmooth_domDomCongrSection (I := I) (M := M) g₀
        (Equiv.swap (0 : Fin 2) 1) S]
  have hgoal : ccTensor02Symm (I := I) (M := M) g₀ (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) =
      (1 / 2 : ℝ) • (rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S)
        +
        rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S)) := by
    rw [ccTensor02Symm, ← hLV]
  rw [hgoal, smul_add, hhalf]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.rawTensorConnLapSmooth_ccTensor02Symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.rawTensorConnLapSmooth_ccTensor02Symm target :: scope.openDecls } }

theorem deTurckRicci_solution_with_jointRegularity
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      JointChartGramSmooth (I := I) T g_DT := by
  have ha_super : 2 * Module.finrank ℝ E + 10 ≤ 4 * Module.finrank ℝ E + 10 := by omega
  have hRepr : ∀ (S : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
      (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ S) δ)
      (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g₀
          (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
              (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt
              (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ) +
            rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w =
        deTurckRicciRHS (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ) x v w := by
    intro S δ hδ_lt hδ x v w
    have hlap : ccTensorBilinSymm (I := I) g₀
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w =
        ccTensorBilinSymm (I := I) g₀
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S)) x v
            w := by
      rw [rawTensorConnLapSmooth_ccTensor02Symm (I := I) (M := M) g₀ S,
        symmetricBilinearForm_of_tensorSymmetrization_eq_self (I := I) (M := M) g₀
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w]
    rw [ccTensorBilinSymm_add (I := I) g₀
        (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt
          (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ))
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w,
      hlap,
      ← ccTensorBilinSymm_add (I := I) g₀
        (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
          (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt
          (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ))
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S)) x v w]
    set gDT := tensorSectionRealizeMetric (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt
      (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ) with hgDT_def
    set R : SmoothCcTensor g₀ 0 2 :=
      { toSection := (deTurckRHSSection (I := I) g_bg gDT).toSection
        hasCompactSupport := (deTurckRHSSection (I := I) g_bg gDT).hasCompactSupport }
      with hR_def
    have hsum_eq : deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
        (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt
        (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ) +
        rawTensorConnLapSmooth (I := I) g₀ 0 2 (ccTensor02Symm (I := I) (M := M) g₀ S) = R := by
      rw [deTurckSmoothRemainder, sub_add_cancel]
    rw [hsum_eq,
      ccTensorBilinSymm_toSection_congr R (deTurckRHSSectionBackground (I := I) g_bg gDT)
        (by rw [hR_def, deTurckRHSSectionBackground_toSection]) x v w]
    have hreal : gDT = tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ :=
      tensorSectionRealizeMetric_ccTensor02Symm_eq (I := I) g₀ S hδ_lt hδ hδ_lt
        (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ)
    rw [← hreal]
    exact deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS (I := I) g_bg gDT x v w
  exact quasilinear_metric_short_time_existence_of_nemytskii (I := I)
    (deTurckRicciRHS (I := I) g_bg) g₀ (4 * Module.finrank ℝ E + 10) rfl
    (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg (4 * Module.finrank ℝ E + 10))
    (fun S {δ} hδ_lt hδ => deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
      (ccTensor02Symm (I := I) (M := M) g₀ S) hδ_lt
        (fiberwiseOperatorNormBound_of_tensorSymmetrization (I := I) (M := M) g₀ S hδ))
    (deTurckSobolevNHa2Symm_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      (4 * Module.finrank ℝ E + 10) ha_super)
    (deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (I := I) (M := M) (g₀ := g₀)
      (g_bg := g_bg) (4 * Module.finrank ℝ E + 10) ha_super)
    hRepr
    (deTurckRicci_forcingBootstrap_symm (I := I) (M := M) g₀ g_bg
      (4 * Module.finrank ℝ E + 10) (by omega))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRicci_solution_with_jointRegularity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRicci_solution_with_jointRegularity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRicci_solution_with_jointRegularity ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRicci_solution_with_jointRegularity

theorem deturck_ricci_flow_parabolic_short_time_existence
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
          : TangentBundle I M))
        (Set.Icc 0 T ×ˢ Set.univ) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun p : ℝ × M =>
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ioo (0 : ℝ) T ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun p : ℝ × M =>
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g_DT p.1) x₀ p.2 i j)
          (Set.Ico (0 : ℝ) T ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × M =>
            DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) (g_DT q.1) α i j
              (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ (chartAt H α).source)) ∧
      (∀ (α : M) (i j : Fin (Module.finrank ℝ E)) (k : ℕ), k ≤ 2 →
        ContinuousOn
          (fun q : ℝ × M => iteratedFDeriv ℝ k
            (DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) (g_DT q.1) α i j)
            (extChartAt I α q.2))
          (Set.Icc 0 T ×ˢ chartLeviCivitaGoodSet (I := I) α)) := by
  obtain ⟨T, g_DT, hsol, hJ⟩ := deTurckRicci_solution_with_jointRegularity (I := I) g₀ g_bg
  obtain ⟨h2, h3, h4, h5, h6, h7⟩ :=
    deTurckRicci_chartRegularity_of_jointChartGramSmooth (I := I) g_bg T g_DT hJ
  exact ⟨T, g_DT, hsol, h2, h3, h4, h5, h6, h7⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deturck_ricci_flow_parabolic_short_time_existence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deturck_ricci_flow_parabolic_short_time_existence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deturck_ricci_flow_parabolic_short_time_existence ``Submission.DifferentialGeometry.PDE.RicciFlow.deturck_ricci_flow_parabolic_short_time_existence

end DifferentialGeometry.PDE.RicciFlow
