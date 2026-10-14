import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Solution.UniformBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Positivity.PositiveDefinitePerturbation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem exists_lowRealize_at
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ delta Rcap : ℝ}
    (hΛ : 1 ≤ Λ) (hdelta : 0 < delta) (hdeltathird : delta ≤ 1 / 3)
    (hRcap : 0 < Rcap) :
    ∃ D : MetricPerturbationRealizationParameters,
      HasUniformMetricPerturbationRealization (I := I) (M := M) gBase Λ D ∧
        D.threshold = delta ∧ D.radius ≤ Rcap := by
  obtain ⟨D0, hD0⟩ := exists_uniform_metric_perturbation_realization_parameters (I := I) (M := M) hDim gBase hΛ
  let radius : ℝ := _root_.Min.min (delta * D0.radius / 2) Rcap
  let D : MetricPerturbationRealizationParameters := { threshold := delta, radius := radius }
  have hradius : 0 < radius := by
    dsimp only [radius]
    exact lt_min (div_pos (mul_pos hdelta hD0.radius_pos) (by norm_num)) hRcap
  have hradiuscap : radius ≤ Rcap := min_le_right _ _
  refine ⟨D, ?_, ?_, ?_⟩
  · refine ⟨hdelta.le, hdeltathird,
      hdeltathird.trans_lt (by norm_num), hradius, ?_⟩
    intro g hEq hjet T hT
    obtain ⟨C, hC, hlin, hCP⟩ := realize_h2_bound (I := I) (M := M) g
      hD0.radius_pos (hD0.threshold_le_third.trans (by norm_num))
      (hD0.realize g hEq hjet)
    have hCP2 : C * D0.radius ≤ 2 := by
      have hmul := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp hCP
      nlinarith
    have hTradius :
        ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) T‖ ≤ delta * D0.radius / 2 := by
      exact hT.trans (min_le_left _ _)
    have hcoeff : C * ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ delta := by
      calc
        _ ≤ C * (delta * D0.radius / 2) :=
          mul_le_mul_of_nonneg_left hTradius hC.le
        _ = delta / 2 * (C * D0.radius) := by ring
        _ ≤ delta / 2 * 2 :=
          mul_le_mul_of_nonneg_left hCP2 (by positivity)
        _ = delta := by ring
    exact metricCauchySchwarzBound_mono (I := I) (M := M) g _ hcoeff (hlin T)
  · rfl
  · simpa only [D] using hradiuscap

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lowRealize_at
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lowRealize_at target :: scope.openDecls } }

theorem exists_lowBounds_at
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ delta Rcap : ℝ}
    (hΛ : 1 ≤ Λ) (hdelta : 0 < delta) (hdeltathird : delta ≤ 1 / 3)
    (hRcap : 0 < Rcap) :
    ∃ K : LowRegularityBoundParameters,
      HasUniformLowRegularityBounds (I := I) (M := M) gBase Λ K ∧
        K.threshold = delta ∧
        lowRegularityStateRadius K.top K.slope K.outer K.realize ≤ Rcap := by
  obtain ⟨RD, hRD, hRDdelta, hRDradius⟩ :=
    exists_lowRealize_at (I := I) (M := M) hDim gBase hΛ
      hdelta hdeltathird hRcap
  obtain ⟨ZD, hZD⟩ := exists_uniform_zero_order_nonlinearity_parameters (I := I) (M := M) gBase hΛ
  obtain ⟨rho, Ctop, B0, B1, hrho, hCtop, hB0, hB1, houter⟩ :=
    deTurckRemainderOnLowerState_outer_uniform_bound (I := I) (M := M) hDim gBase hΛ
      hRD.threshold_nonneg hRD.threshold_lt
  let Q : ℝ := lowRegularityOuterRadius Ctop rho RD.radius
  have hQpos : 0 < Q := by
    simpa only [Q] using lowRegularityOuterRadius_pos hCtop hrho hRD.radius_pos
  have hB1Q : 0 ≤ B1 Q := hB1 Q hQpos.le
  have hSpos : 0 < lowRegularityStateRadius Ctop (B1 Q) rho RD.radius :=
    lowRegularityStateRadius_pos hCtop hB1Q hrho hRD.radius_pos
  have hQrho : Q ≤ rho := by
    have hhalf := lowRegularityOuterRadius_le_rho
      (Ctop := Ctop) (ρ := rho) (P := RD.radius)
    dsimp only [Q]
    linarith
  have hQP : Q ≤ RD.radius := by
    have hhalf := lowRegularityOuterRadius_le_P
      (Ctop := Ctop) (ρ := rho) (P := RD.radius)
    dsimp only [Q]
    linarith
  have hSQ : lowRegularityStateRadius Ctop (B1 Q) rho RD.radius ≤ Q := by
    have hhalf := lowRegularityStateRadius_le_Q
      (Ctop := Ctop) (B1 := B1 Q) (ρ := rho) (P := RD.radius)
    linarith
  let K : LowRegularityBoundParameters := {
    threshold := RD.threshold
    top := Ctop
    base := B0 Q
    slope := B1 Q
    zeroBd := ZD.zeroBd
    outer := rho
    realize := RD.radius
    threshold_lt := hRD.threshold_lt
    top_nonneg := hCtop
    base_nonneg := hB0 Q hQpos.le
    slope_nonneg := hB1Q
    zero_nonneg := hZD.zero_nonneg
    outer_pos := hrho
    realize_pos := hRD.radius_pos
  }
  have hstatecap :
      lowRegularityStateRadius K.top K.slope K.outer K.realize ≤ Rcap := by
    exact (lowRegularityStateRadius_le_P K.realize_pos.le).trans hRDradius
  refine ⟨K, { bounds := ?_ }, ?_, hstatecap⟩
  · intro g hEq hjet
    have hreal := hRD.realize g hEq hjet
    have hrealQ : ∀ T : SmoothCcTensor g 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 1) T‖ ≤ Q →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) RD.threshold :=
      realizeOfLE (I := I) (M := M) g hQP hreal
    obtain ⟨hcont0, hcore0, htame0⟩ :=
      houter g hEq hjet hQpos.le hQrho hSpos hSQ hrealQ
    have hcore' : Continuous
        (deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hRD.threshold_lt
          (lowRegularityMetricRealization (I := I) (M := M) g
            (Ctop := Ctop) (B1 := B1 Q) (ρ := rho)
            hRD.radius_pos.le hreal)) := by
      simpa only using hcore0
    have hzero0 := zero_order_nonlinearity_bound_of_uniform_parameters (I := I) (M := M) hZD g hEq hjet
      hRD.threshold_lt hCtop hB1Q hrho hRD.radius_pos hreal hcore'
    have hrealK : ∀ T : SmoothCcTensor g 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 1) T‖ ≤ K.realize →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) K.threshold := by
      simpa only [K] using hreal
    refine {
      threshold_nonneg := by simpa only [K] using hRD.threshold_nonneg
      threshold_le_third := by simpa only [K] using hRD.threshold_le_third
      metric_realization := hrealK
      remainder_continuous := ?_
      remainder_lipschitz := ?_
      remainder_zero_bound := ?_
      smoothCore_continuous := ?_ }
    · simpa only [K, Q, boundedDeTurckRemainderOnLowerState] using hcont0
    · simpa only [K, Q, boundedDeTurckRemainderOnLowerState] using htame0
    · simpa only [K, Q] using hzero0
    · simpa only [K, Q] using hcore'
  · simpa only [K] using hRDdelta

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lowBounds_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lowBounds_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lowBounds_at ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_lowBounds_at

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
