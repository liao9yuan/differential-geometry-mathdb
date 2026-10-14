import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Bounds.Class

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
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
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

structure IsBackgroundLowRegularitySolutionAt (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (Rcap : ℝ) : Prop where

  bounds : HasLowRegularityBoundsAt (I := I) (M := M) g₀ g_bg K

  solve : IsBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K bounds hT hT1 u gforce

  time_le_horizon : T ≤ lowRegularityTimeHorizon K.top K.base K.slope K.zeroBd K.outer K.realize

  stateRadius_le : lowRegularityStateRadius K.top K.slope K.outer K.realize ≤ Rcap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt

namespace IsBackgroundLowRegularitySolutionAt

variable {g₀ g_bg : SmoothRiemannianMetric I M} {K : LowRegularityBoundParameters}
  {T : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
  {u : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T}
  {gforce : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
  {Rcap : ℝ}

theorem threshold_lt_one :
    K.threshold < 1 :=
  K.threshold_lt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_lt_one ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_lt_one

theorem top_nonneg
    :
    0 ≤ K.top :=
  K.top_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.top_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.top_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.top_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.top_nonneg

theorem slope_nonneg
    :
    0 ≤ K.slope :=
  K.slope_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.slope_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.slope_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.slope_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.slope_nonneg

theorem outer_pos :
    0 < K.outer :=
  K.outer_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.outer_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.outer_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.outer_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.outer_pos

theorem realize_pos :
    0 < K.realize :=
  K.realize_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.realize_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.realize_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.realize_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.realize_pos

theorem metric_realization
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤
          K.realize →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) K.threshold :=
  h.bounds.metric_realization

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.metric_realization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.metric_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.metric_realization ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.metric_realization

theorem threshold_nonneg
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    0 ≤ K.threshold :=
  h.bounds.threshold_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_nonneg

theorem threshold_le_third
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    K.threshold ≤ 1 / 3 :=
  h.bounds.threshold_le_third

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_le_third then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_le_third"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_le_third ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.threshold_le_third

theorem smoothCore_continuous
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg K.threshold_lt
      (lowRegularityMetricRealization (I := I) (M := M) g₀
        (Ctop := K.top) (B1 := K.slope) (ρ := K.outer)
        K.realize_pos.le h.metric_realization)) :=
  h.bounds.smoothCore_continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.smoothCore_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.smoothCore_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.smoothCore_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.smoothCore_continuous

theorem base_nonneg
    :
    0 ≤ K.base :=
  K.base_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.base_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.base_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.base_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.base_nonneg

theorem remainder_continuous
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    Continuous (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt
      K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos h.metric_realization) :=
  h.bounds.remainder_continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_continuous

theorem remainder_lipschitz
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ∀ v w : lowerState (I := I) (M := M) g₀ 1
      (lowRegularityStateRadius K.top K.slope K.outer K.realize),
    ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
          K.slope_nonneg K.outer_pos K.realize_pos h.metric_realization v -
        boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
          K.slope_nonneg K.outer_pos K.realize_pos h.metric_realization w‖ ≤
      K.top * lowRegularityOuterRadius K.top K.outer K.realize *
          ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
            (((1 : ℕ) : ℝ) + 2)) - w.1‖ +
        K.base *
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
            ((v.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - w.1)‖ +
        K.slope *
            (‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2))‖ +
              ‖(w.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖) *
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
            ((v.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - w.1)‖ :=
  h.bounds.remainder_lipschitz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_lipschitz ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_lipschitz

theorem remainder_zero_bound
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
        K.slope_nonneg K.outer_pos K.realize_pos h.metric_realization
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg K.outer_pos
            K.realize_pos).le⟩‖ ≤ K.zeroBd :=
  h.bounds.remainder_zero_bound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_zero_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_zero_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_zero_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.remainder_zero_bound

theorem forcing_norm_le_quarter_radius
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    ‖gforce‖ ≤ lowRegularityStateRadius K.top K.slope K.outer K.realize / 4 :=
  h.solve.force_bound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.forcing_norm_le_quarter_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.forcing_norm_le_quarter_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.forcing_norm_le_quarter_radius ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.forcing_norm_le_quarter_radius

theorem forcing_ae_eq_remainder
    (h : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 u gforce Rcap) :
    gforce =ᵐ[timeMeasure T]
      (fun t => boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt
        K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos h.metric_realization
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg K.outer_pos
              K.realize_pos).le)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            gforce) t)) :=
  h.solve.force_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.forcing_ae_eq_remainder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.forcing_ae_eq_remainder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.forcing_ae_eq_remainder ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.IsBackgroundLowRegularitySolutionAt.forcing_ae_eq_remainder

end IsBackgroundLowRegularitySolutionAt

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
